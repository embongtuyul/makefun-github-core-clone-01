#!/usr/bin/env python3
"""A standalone GitHub-compatible git forge in one process, Python 3 stdlib only.

Surfaces:
  - git smart HTTP: /{owner}/{repo}.git (upload-pack protocol v2, receive-pack v0)
  - REST v3: /api/v3 (repos, issues, pull requests, contents)
  - GraphQL v4: /api/graphql
  - MCP (Streamable HTTP, revision 2026-07-28): /mcp
  - /healthz for the suite's boot probe

Lifecycle (the make.fun wire contract): bind an ephemeral port, POST
{"port": N} to $MAKEFUN_ENV_URL/register, then long-poll GET
$MAKEFUN_ENV_URL/done until {"done": true} and exit 0.

No git binary, no outside service, no wall clock in any stored data: commit
timestamps derive from a fixed epoch plus a deterministic counter, so two runs
over the same requests produce the same bytes.
"""

import base64
import difflib
import hashlib
import json
import os
import re
import socket
import threading
import time
import urllib.parse
import urllib.request
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
VERSION = "1.0.0"
AGENT = "github-forge/1.0"
FIXED_TS = "2025-01-01T00:00:00Z"
EPOCH = 1735689600
ZERO_OID = "0" * 40
HEX40 = re.compile(r"^[0-9a-f]{40}$")

# ---------------------------------------------------------------------------
# git object model
# ---------------------------------------------------------------------------

TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def hash_object(otype, data):
    h = hashlib.sha1()
    h.update(("%s %d\0" % (otype, len(data))).encode("ascii"))
    h.update(data)
    return h.hexdigest()


def is_oid(s):
    return isinstance(s, str) and bool(HEX40.match(s))


def parse_tree(data):
    entries = []
    off = 0
    while off < len(data):
        sp = data.index(b" ", off)
        nul = data.index(b"\0", sp + 1)
        mode = data[off:sp].decode("ascii")
        name = data[sp + 1:nul].decode("utf-8")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        off = nul + 21
    return entries


def _tree_sort_key(entry):
    mode, name, _oid = entry
    return (name + "/").encode("utf-8") if mode == "40000" else name.encode("utf-8")


def build_tree(entries):
    out = bytearray()
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        out += ("%s %s\0" % (mode, name)).encode("utf-8")
        out += bytes.fromhex(oid)
    return bytes(out)


def parse_commit(data):
    text = data.decode("utf-8", "replace")
    head, _, message = text.partition("\n\n")
    tree = ""
    parents = []
    author = ""
    committer = ""
    for line in head.split("\n"):
        if line.startswith("tree "):
            tree = line[5:]
        elif line.startswith("parent "):
            parents.append(line[7:])
        elif line.startswith("author "):
            author = line[7:]
        elif line.startswith("committer "):
            committer = line[10:]
    return {"tree": tree, "parents": parents, "author": author,
            "committer": committer, "message": message}


def parse_tag(data):
    text = data.decode("utf-8", "replace")
    head, _, message = text.partition("\n\n")
    fields = {}
    for line in head.split("\n"):
        if " " in line:
            k, v = line.split(" ", 1)
            fields[k] = v
    return {"object": fields.get("object", ""), "type": fields.get("type", ""),
            "tag": fields.get("tag", ""), "tagger": fields.get("tagger", ""),
            "message": message}


def build_commit(tree, parents, message, author, timestamp):
    lines = ["tree %s" % tree]
    for p in parents:
        lines.append("parent %s" % p)
    who = "%s %d +0000" % (author, timestamp)
    lines.append("author %s" % who)
    lines.append("committer %s" % who)
    lines.append("")
    return ("\n".join(lines) + "\n" + message).encode("utf-8")


# ---------------------------------------------------------------------------
# pkt-line
# ---------------------------------------------------------------------------

def pkt(data):
    if isinstance(data, str):
        data = data.encode("utf-8")
    return ("%04x" % (len(data) + 4)).encode("ascii") + data


FLUSH = b"0000"
DELIM = b"0001"


def pkt_lines(items):
    out = bytearray()
    for item in items:
        if item == "flush":
            out += FLUSH
        elif item == "delim":
            out += DELIM
        elif item == "response-end":
            out += b"0002"
        else:
            out += pkt(item)
    return bytes(out)


class PktError(ValueError):
    pass


def pkt_decode(buf):
    """Decode a whole buffer into packets.

    Returns (packets, rest_offset) where packets are ('data', bytes) /
    ('flush',) / ('delim',) / ('response-end',). Raises PktError on bad input.
    """
    packets = []
    off = 0
    n = len(buf)
    while off < n:
        if off + 4 > n:
            raise PktError("truncated pkt-line header")
        head = buf[off:off + 4]
        try:
            length = int(head.decode("ascii"), 16)
        except ValueError:
            raise PktError("invalid pkt-line length %r" % head)
        if length == 0:
            packets.append(("flush",))
            off += 4
        elif length == 1:
            packets.append(("delim",))
            off += 4
        elif length == 2:
            packets.append(("response-end",))
            off += 4
        elif length < 4 or length > 65520:
            raise PktError("invalid pkt-line length %d" % length)
        else:
            if off + length > n:
                raise PktError("truncated pkt-line")
            packets.append(("data", buf[off + 4:off + length]))
            off += length
    return packets, off


def pkt_decode_until_flush(buf):
    """Decode pkt-lines up to and including the first flush.

    Returns (packets, offset_after_flush). Raises PktError on bad input.
    """
    packets = []
    off = 0
    n = len(buf)
    while off < n:
        if off + 4 > n:
            raise PktError("truncated pkt-line header")
        head = buf[off:off + 4]
        try:
            length = int(head.decode("ascii"), 16)
        except ValueError:
            raise PktError("invalid pkt-line length %r" % head)
        if length == 0:
            return packets, off + 4
        if length in (1, 2):
            packets.append(("delim" if length == 1 else "response-end",))
            off += 4
            continue
        if length < 4 or length > 65520 or off + length > n:
            raise PktError("bad pkt-line")
        packets.append(("data", buf[off + 4:off + length]))
        off += length
    raise PktError("no flush packet")


# ---------------------------------------------------------------------------
# packfile read / write
# ---------------------------------------------------------------------------

def _read_varint(buf, off):
    first = buf[off]
    byte = first
    size = byte & 0x0F
    shift = 4
    off += 1
    while byte & 0x80:
        byte = buf[off]
        off += 1
        size += (byte & 0x7F) << shift
        shift += 7
    return size, off, first


def _read_ofs_base(buf, off):
    byte = buf[off]
    off += 1
    value = byte & 0x7F
    while byte & 0x80:
        byte = buf[off]
        off += 1
        value = ((value + 1) << 7) | (byte & 0x7F)
    return value, off


def _inflate_at(buf, off, limit):
    d = zlib.decompressobj()
    out = d.decompress(buf[off:limit])
    consumed = (limit - off) - len(d.unused_data)
    return out, off + consumed


def apply_delta(base, delta):
    def read_size(pos):
        value = 0
        shift = 0
        while True:
            b = delta[pos]
            pos += 1
            value |= (b & 0x7F) << shift
            shift += 7
            if not (b & 0x80):
                return value, pos

    src_size, pos = read_size(0)
    tgt_size, pos = read_size(pos)
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            for bit in range(4):
                if op & (1 << bit):
                    cp_off |= delta[pos] << (bit * 8)
                    pos += 1
            for bit in range(3):
                if op & (0x10 << bit):
                    cp_size |= delta[pos] << (bit * 8)
                    pos += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta target size mismatch")
    return bytes(out)


def read_pack(data):
    """Parse a packfile; returns dict oid -> (type, bytes). Verifies the trailer."""
    if len(data) < 32 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    version = int.from_bytes(data[4:8], "big")
    if version not in (2, 3):
        raise ValueError("unsupported pack version %d" % version)
    count = int.from_bytes(data[8:12], "big")
    trailer = data[-20:]
    if hashlib.sha1(data[:-20]).digest() != trailer:
        raise ValueError("pack trailer checksum mismatch")
    limit = len(data) - 20
    raw = []  # (offset, type_code, size, data, base_offset|base_oid)
    by_offset = {}
    off = 12
    for _ in range(count):
        entry_off = off
        size, off, first = _read_varint(data, off)
        tcode = (first >> 4) & 0x07
        base_off = None
        base_oid = None
        if tcode == 6:
            delta, off = _read_ofs_base(data, off)
            base_off = entry_off - delta
        elif tcode == 7:
            base_oid = data[off:off + 20].hex()
            off += 20
        elif tcode not in CODE_TYPE:
            raise ValueError("unknown pack type %d" % tcode)
        inflated, off = _inflate_at(data, off, limit)
        if len(inflated) != size:
            raise ValueError("pack entry size mismatch")
        raw.append((entry_off, tcode, size, inflated, base_off, base_oid))
        by_offset[entry_off] = len(raw) - 1
    objects = {}
    resolved = {}

    def resolve(idx):
        if idx in resolved:
            return resolved[idx]
        _off, tcode, _size, payload, base_off, base_oid = raw[idx]
        if tcode == 6:
            btype, bdata = resolve(by_offset[base_off])
            data_out = apply_delta(bdata, payload)
            otype = btype
        elif tcode == 7:
            if base_oid in objects:
                btype, bdata = objects[base_oid]
            else:
                raise ValueError("ref-delta base %s not in pack" % base_oid)
            data_out = apply_delta(bdata, payload)
            otype = btype
        else:
            otype = CODE_TYPE[tcode]
            data_out = payload
        oid = hash_object(otype, data_out)
        resolved[idx] = (otype, data_out)
        objects[oid] = (otype, data_out)
        return resolved[idx]

    for i in range(len(raw)):
        resolve(i)
    return objects


def _pack_object_header(otype, size):
    code = TYPE_CODE[otype]
    out = bytearray()
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def write_pack(objects):
    """Build a packfile from plain objects [(type, bytes), ...]. No deltas."""
    parts = [b"PACK" + (2).to_bytes(4, "big") + len(objects).to_bytes(4, "big")]
    for otype, data in objects:
        parts.append(_pack_object_header(otype, len(data)))
        parts.append(zlib.compress(data, 6))
    body = b"".join(parts)
    return body + hashlib.sha1(body).digest()


# ---------------------------------------------------------------------------
# reachability / merge helpers over an object store {oid: (type, bytes)}
# ---------------------------------------------------------------------------

def collect_reachable(objects, roots, max_depth=None):
    """All oids reachable from roots. max_depth limits commit generations
    (None = unlimited). Returns (oids, commit_depths) where commit_depths maps
    commit oid -> generations from the nearest root."""
    seen = set()
    depths = {}
    stack = [(r, 0) for r in roots if is_oid(r)]
    while stack:
        oid, depth = stack.pop()
        if oid in seen:
            if depth < depths.get(oid, 1 << 30):
                depths[oid] = depth
            continue
        obj = objects.get(oid)
        if obj is None:
            continue
        otype, data = obj
        if otype == "commit":
            # A commit at (or beyond) the depth boundary is NOT included:
            # it is the shallow boundary, not part of the send set. Do not
            # mark it seen, so a later visit at a smaller depth can still
            # include it (e.g. a want that is also another want's parent).
            if max_depth is not None and depth >= max_depth:
                depths[oid] = depth
                continue
            seen.add(oid)
            depths[oid] = depth
            c = parse_commit(data)
            stack.append((c["tree"], depth))
            for p in c["parents"]:
                stack.append((p, depth + 1))
        elif otype == "tag":
            seen.add(oid)
            t = parse_tag(data)
            stack.append((t["object"], depth))
        elif otype == "tree":
            seen.add(oid)
            for _mode, _name, child in parse_tree(data):
                stack.append((child, depth))
        else:  # blob
            seen.add(oid)
    return seen, depths


def ancestors_with_depth(objects, tip):
    """Map commit oid -> generations from tip (following parents)."""
    depths = {}
    stack = [(tip, 0)]
    while stack:
        oid, depth = stack.pop()
        if oid in depths and depths[oid] <= depth:
            continue
        obj = objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        depths[oid] = depth
        for p in parse_commit(obj[1])["parents"]:
            stack.append((p, depth + 1))
    return depths


def merge_base(objects, tip_a, tip_b):
    a = ancestors_with_depth(objects, tip_a)
    b = ancestors_with_depth(objects, tip_b)
    common = set(a) & set(b)
    if not common:
        return None
    # newest common ancestor: greatest (depth from a + depth from b is smallest
    # for the closest one); use max timestamp then min total depth.
    best = None
    best_key = None
    for oid in common:
        ts = 0
        obj = objects.get(oid)
        if obj is not None:
            m = re.search(rb" (\d+) \+0000", obj[1])
            if m:
                ts = int(m.group(1))
        key = (ts, -(a[oid] + b[oid]))
        if best_key is None or key > best_key:
            best_key = key
            best = oid
    return best


def flatten_tree(objects, tree_oid):
    """Map path -> (mode, oid) for every blob in a tree, recursively."""
    out = {}

    def walk(tree_oid, prefix):
        obj = objects.get(tree_oid)
        if obj is None or obj[0] != "tree":
            return
        for mode, name, oid in parse_tree(obj[1]):
            path = prefix + name
            if mode == "40000":
                walk(oid, path + "/")
            else:
                out[path] = (mode, oid)

    walk(tree_oid, "")
    return out


def build_tree_from_map(objects, flat):
    """Rebuild nested tree objects from a flat path map; stores new trees in
    `objects` (dict) and returns the root tree oid."""
    # group by directory
    def build(paths):
        dirs = {}
        files = []
        for path, (mode, oid) in paths.items():
            if "/" in path:
                head, rest = path.split("/", 1)
                dirs.setdefault(head, {})[rest] = (mode, oid)
            else:
                files.append((mode, path, oid))
        entries = list(files)
        for name, sub in dirs.items():
            entries.append(("40000", name, build(sub)))
        data = build_tree(entries)
        oid = hash_object("tree", data)
        objects[oid] = ("tree", data)
        return oid

    return build(dict(flat))


def tree_diff(objects, old_tree, new_tree):
    """Diff two trees: {path: (kind, old_oid, new_oid)} kind in added/deleted/modified."""
    old = flatten_tree(objects, old_tree) if old_tree else {}
    new = flatten_tree(objects, new_tree) if new_tree else {}
    out = {}
    for path in sorted(set(old) | set(new)):
        if path not in old:
            out[path] = ("added", None, new[path][1])
        elif path not in new:
            out[path] = ("deleted", old[path][1], None)
        elif old[path][1] != new[path][1]:
            out[path] = ("modified", old[path][1], new[path][1])
    return out


# ---------------------------------------------------------------------------
# in-memory store
# ---------------------------------------------------------------------------

def gid(kind, *parts):
    raw = (kind + ":" + ":".join(str(p) for p in parts)).encode("utf-8")
    return kind[0].upper() + "_" + base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def ungid(value):
    """Decode a global id -> (kind, parts) or None."""
    if not isinstance(value, str) or "_" not in value:
        return None
    kind, _, b64 = value.partition("_")
    try:
        raw = base64.urlsafe_b64decode(b64 + "=" * (-len(b64) % 4)).decode("utf-8")
    except Exception:
        return None
    parts = raw.split(":")
    kinds = {"R": "repo", "I": "issue", "P": "pr", "C": "comment"}
    if kinds.get(kind) != parts[0]:
        return None
    return parts[0], parts[1:]


class Repo:
    def __init__(self, name, private, description, dbid, seq):
        self.name = name
        self.private = bool(private)
        self.description = description or ""
        self.dbid = dbid
        self.default_branch = "main"
        self.created_seq = seq
        self.objects = {}       # oid -> (type, bytes)
        self.refs = {}          # refname -> oid
        self.labels = {}        # name -> {"name","color"}
        self.issues = {}        # number -> dict
        self.prs = {}           # number -> dict
        self.comments = {}      # issue number -> [dict]
        self.next_number = 1
        self.next_comment_id = 1

    def global_id(self):
        return gid("repo", self.dbid)


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.learned_login = None
        self.repos = {}         # name -> Repo
        self.next_repo_id = 5000
        self.seq = 0
        self.req_counter = 0
        self.fetch_cache = {}   # (repo_name, wants, haves, depth, shallow) -> bytes

    def tick(self):
        self.seq += 1
        return self.seq

    def learn(self, owner):
        if owner and self.learned_login is None:
            self.learned_login = owner
        return self.learned_login

    def login(self):
        return self.learned_login or ""

    def next_req_id(self):
        self.req_counter += 1
        return "req-%08d" % self.req_counter


STORE = Store()


# ---------------------------------------------------------------------------
# repo object rendering (REST shapes)
# ---------------------------------------------------------------------------

def repo_json(repo):
    login = STORE.login()
    return {
        "id": repo.dbid,
        "node_id": repo.global_id(),
        "name": repo.name,
        "full_name": "%s/%s" % (login, repo.name),
        "private": repo.private,
        "owner": {"login": login, "id": 1, "type": "User",
                  "node_id": gid("user", login) if login else ""},
        "description": repo.description,
        "default_branch": repo.default_branch,
        "created_at": FIXED_TS,
        "updated_at": FIXED_TS,
        "pushed_at": FIXED_TS,
        "html_url": "https://example.invalid/%s/%s" % (login, repo.name),
        "url": "/api/v3/repos/%s/%s" % (login, repo.name),
        "clone_url": "https://example.invalid/%s/%s.git" % (login, repo.name),
        "git_url": "git://example.invalid/%s/%s.git" % (login, repo.name),
        "ssh_url": "git@example.invalid:%s/%s.git" % (login, repo.name),
        "homepage": "",
        "language": None,
        "has_issues": True,
        "has_projects": True,
        "has_wiki": True,
        "forks_count": 0,
        "stargazers_count": 0,
        "watchers_count": 0,
        "open_issues_count": sum(1 for i in repo.issues.values() if i["state"] == "open"),
        "license": None,
        "permissions": {"admin": True, "maintain": True, "push": True,
                        "triage": True, "pull": True},
        "visibility": "private" if repo.private else "public",
    }


def issue_json(repo, issue):
    login = STORE.login()
    return {
        "id": issue["dbid"],
        "node_id": issue["gid"],
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "labels": [{"name": n, "color": repo.labels[n]["color"], "id": 1,
                    "description": "", "default": False}
                   for n in issue["labels"] if n in repo.labels],
        "user": {"login": login, "id": 1, "type": "User"},
        "created_at": FIXED_TS,
        "updated_at": FIXED_TS,
        "closed_at": FIXED_TS if issue["state"] == "closed" else None,
        "comments": len(repo.comments.get(issue["number"], [])),
        "html_url": "https://example.invalid/%s/%s/issues/%d" % (login, repo.name, issue["number"]),
        "url": "/api/v3/repos/%s/%s/issues/%d" % (login, repo.name, issue["number"]),
        "repository_url": "/api/v3/repos/%s/%s" % (login, repo.name),
        "assignee": None,
        "milestone": None,
        "locked": False,
    }


def pr_json(repo, pr):
    login = STORE.login()
    head_sha = repo.refs.get("refs/heads/" + pr["head"], "") or ""
    base_sha = repo.refs.get("refs/heads/" + pr["base"], "") or ""
    return {
        "id": pr["dbid"],
        "node_id": pr["gid"],
        "number": pr["number"],
        "title": pr["title"],
        "body": pr["body"],
        "state": pr["state"],
        "head": {"ref": pr["head"], "sha": head_sha,
                 "label": "%s:%s" % (login, pr["head"]),
                 "user": {"login": login, "type": "User"},
                 "repo": {"name": repo.name, "full_name": "%s/%s" % (login, repo.name)}},
        "base": {"ref": pr["base"], "sha": base_sha,
                 "label": "%s:%s" % (login, pr["base"]),
                 "user": {"login": login, "type": "User"},
                 "repo": {"name": repo.name, "full_name": "%s/%s" % (login, repo.name)}},
        "merged": pr["merged"],
        "merged_at": FIXED_TS if pr["merged"] else None,
        "merge_commit_sha": pr["merge_sha"] or "",
        "mergeable": pr["mergeable"] is not False,
        "mergeable_state": ("clean" if pr["mergeable"] else "dirty"),
        "user": {"login": login, "id": 1, "type": "User"},
        "created_at": FIXED_TS,
        "updated_at": FIXED_TS,
        "closed_at": FIXED_TS if pr["state"] == "closed" else None,
        "draft": False,
        "html_url": "https://example.invalid/%s/%s/pull/%d" % (login, repo.name, pr["number"]),
        "url": "/api/v3/repos/%s/%s/pulls/%d" % (login, repo.name, pr["number"]),
    }


def commit_json(repo, oid):
    obj = repo.objects.get(oid)
    c = parse_commit(obj[1]) if obj else {"message": "", "parents": [], "author": "", "committer": ""}
    login = STORE.login()
    return {
        "sha": oid,
        "commit": {
            # GitHub's REST view strips the trailing newline of the message.
            "message": c["message"].rstrip("\n"),
            "author": {"name": login, "email": "%s@example.invalid" % login, "date": FIXED_TS},
            "committer": {"name": login, "email": "%s@example.invalid" % login, "date": FIXED_TS},
        },
        "author": {"login": login, "id": 1, "type": "User"},
        "committer": {"login": login, "id": 1, "type": "User"},
        "parents": [{"sha": p} for p in c["parents"]],
        "url": "/api/v3/repos/%s/%s/commits/%s" % (login, repo.name, oid),
        "html_url": "https://example.invalid/%s/%s/commit/%s" % (login, repo.name, oid),
    }


def branch_tip(repo, branch):
    return repo.refs.get("refs/heads/" + branch)


def tip_tree(repo, branch):
    tip = branch_tip(repo, branch)
    if not tip:
        return None
    obj = repo.objects.get(tip)
    if obj is None or obj[0] != "commit":
        return None
    return parse_commit(obj[1])["tree"]


def list_commits(repo, ref):
    """Newest-first commit oids reachable from ref (first-parent walk)."""
    tip = repo.refs.get(ref) or branch_tip(repo, ref) or (ref if is_oid(ref) else None)
    out = []
    seen = set()
    cur = tip
    while cur and cur not in seen:
        obj = repo.objects.get(cur)
        if obj is None or obj[0] != "commit":
            break
        seen.add(cur)
        out.append(cur)
        parents = parse_commit(obj[1])["parents"]
        cur = parents[0] if parents else None
    return out


def make_commit(repo, tree_oid, parents, message):
    seq = STORE.tick()
    author = "%s <%s@example.invalid>" % (STORE.login(), STORE.login())
    data = build_commit(tree_oid, parents, message if message.endswith("\n") else message + "\n",
                        author, EPOCH + seq)
    oid = hash_object("commit", data)
    repo.objects[oid] = ("commit", data)
    return oid


def pr_files(repo, pr):
    """Diff base tip tree -> head tip tree, with line counts."""
    base_tree = tip_tree(repo, pr["base"])
    head_tree = tip_tree(repo, pr["head"])
    diff = tree_diff(repo.objects, base_tree, head_tree)
    out = []
    for path in sorted(diff):
        kind, old_oid, new_oid = diff[path]
        old_data = repo.objects.get(old_oid, (None, b""))[1] if old_oid else b""
        new_data = repo.objects.get(new_oid, (None, b""))[1] if new_oid else b""
        if kind == "added":
            additions = len(new_data.decode("utf-8", "replace").splitlines())
            deletions = 0
            status = "added"
        elif kind == "deleted":
            additions = 0
            deletions = len(old_data.decode("utf-8", "replace").splitlines())
            status = "removed"
        else:
            old_lines = old_data.decode("utf-8", "replace").splitlines()
            new_lines = new_data.decode("utf-8", "replace").splitlines()
            additions = deletions = 0
            for line in difflib.unified_diff(old_lines, new_lines, lineterm=""):
                if line.startswith("+++") or line.startswith("---"):
                    continue
                if line.startswith("+"):
                    additions += 1
                elif line.startswith("-"):
                    deletions += 1
            status = "modified"
        out.append({"filename": path, "status": status, "additions": additions,
                    "deletions": deletions, "changes": additions + deletions,
                    "sha": new_oid or old_oid or "",
                    "blob_url": "", "raw_url": "", "contents_url": ""})
    return out


def pr_conflict(repo, pr):
    """True when the head branch cannot squash-merge cleanly onto the base."""
    base_tip = branch_tip(repo, pr["base"])
    head_tip = branch_tip(repo, pr["head"])
    if not base_tip or not head_tip:
        return False
    base = merge_base(repo.objects, base_tip, head_tip)
    if base is None:
        return False
    base_tree = parse_commit(repo.objects[base][1])["tree"]
    tip_base_tree = parse_commit(repo.objects[base_tip][1])["tree"]
    tip_head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
    d_base = tree_diff(repo.objects, base_tree, tip_base_tree)
    d_head = tree_diff(repo.objects, base_tree, tip_head_tree)
    for path in set(d_base) & set(d_head):
        if d_base[path][2] != d_head[path][2]:
            return True
    return False


def squash_merge(repo, pr):
    """Squash-merge pr onto its base branch. Returns merge commit oid or None."""
    base_tip = branch_tip(repo, pr["base"])
    head_tip = branch_tip(repo, pr["head"])
    if not base_tip or not head_tip:
        return None
    if pr_conflict(repo, pr):
        return None
    base = merge_base(repo.objects, base_tip, head_tip)
    base_tree = parse_commit(repo.objects[base][1])["tree"] if base else None
    tip_base_tree = parse_commit(repo.objects[base_tip][1])["tree"]
    tip_head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
    d_head = tree_diff(repo.objects, base_tree, tip_head_tree)
    flat = flatten_tree(repo.objects, tip_base_tree)
    for path, (kind, _old, new_oid) in d_head.items():
        if kind == "deleted":
            flat.pop(path, None)
        else:
            mode = flatten_tree(repo.objects, tip_head_tree).get(path, ("100644", new_oid))[0]
            flat[path] = (mode, new_oid)
    new_tree = build_tree_from_map(repo.objects, flat)
    message = "%s (#%d)\n" % (pr["title"], pr["number"])
    merge_oid = make_commit(repo, new_tree, [base_tip], message)
    repo.refs["refs/heads/" + pr["base"]] = merge_oid
    return merge_oid


# ---------------------------------------------------------------------------
# git smart HTTP: advertisements and fetch
# ---------------------------------------------------------------------------

def v0_ref_lines(repo, service):
    """v0 advertisement ref lines (without the service preamble)."""
    caps_upload = "side-band-64k thin-pack ofs-delta multi_ack shallow agent=%s symref=HEAD:refs/heads/%s" % (AGENT, repo.default_branch)
    caps_recv = "report-status side-band-64k delete-refs ofs-delta agent=%s symref=HEAD:refs/heads/%s" % (AGENT, repo.default_branch)
    caps = caps_upload if service == "git-upload-pack" else caps_recv
    lines = []
    refs = sorted(repo.refs.items())
    head_tip = repo.refs.get("refs/heads/" + repo.default_branch)
    if not refs:
        lines.append("%s capabilities^{}\0%s\n" % (ZERO_OID, caps))
        return lines, caps
    first = True
    if head_tip:
        lines.append("%s HEAD\0%s\n" % (head_tip, caps))
        first = False
    for name, oid in refs:
        cap = "" if not first else "\0" + caps
        if first:
            first = False
        lines.append("%s %s%s\n" % (oid, name, cap))
        if oid in repo.objects and repo.objects[oid][0] == "tag":
            peeled = parse_tag(repo.objects[oid][1])["object"]
            lines.append("%s %s^{}\n" % (peeled, name))
    return lines, caps


def v0_advertisement(repo, service):
    lines, _caps = v0_ref_lines(repo, service)
    body = pkt("# service=%s\n" % service) + FLUSH
    for line in lines:
        body += pkt(line)
    body += FLUSH
    return body


def v2_advertisement():
    lines = ["version 2\n", "agent=%s\n" % AGENT, "ls-refs=unborn\n",
             "fetch=shallow filter\n", "object-format=sha1\n"]
    return pkt_lines(lines + ["flush"])


def ls_refs_v2(repo, prefixes, peel, symrefs, unborn):
    """Build v2 ls-refs response lines."""
    out = []
    head_tip = repo.refs.get("refs/heads/" + repo.default_branch)
    names = sorted(repo.refs)
    keep = lambda n: not prefixes or any(n.startswith(p) for p in prefixes)
    if not prefixes or keep("HEAD"):
        if head_tip:
            line = "%s HEAD" % head_tip
            if symrefs:
                line += " symref-target:refs/heads/%s" % repo.default_branch
            out.append(line + "\n")
        elif unborn:
            line = "unborn HEAD"
            if symrefs:
                line += " symref-target:refs/heads/%s" % repo.default_branch
            out.append(line + "\n")
    for name in names:
        if not keep(name):
            continue
        oid = repo.refs[name]
        line = "%s %s" % (oid, name)
        if peel and repo.objects.get(oid, (None,))[0] == "tag":
            line += " peeled:%s" % parse_tag(repo.objects[oid][1])["object"]
        out.append(line + "\n")
    return pkt_lines(out + ["flush"])


def fetch_send_set(repo, wants, haves, depth, shallow_old):
    """Objects to send for a fetch. Returns (oids, shallow_new, unshallow)."""
    objects = repo.objects
    wanted, _ = collect_reachable(objects, wants, max_depth=depth)
    # A have that is also a shallow boundary means the client holds that
    # commit (and its tree) but NONE of its ancestors — deepening must
    # still deliver them. Cap such haves at one generation; normal haves
    # count their full reachable history.
    held = set()
    shallow_set = set(shallow_old or [])
    for h in haves:
        if h in shallow_set:
            hset, _ = collect_reachable(objects, [h], max_depth=1)
        else:
            hset, _ = collect_reachable(objects, [h])
        held |= hset
    send = wanted - held
    # shallow boundary: included commits whose parent is not included
    shallow_new = []
    unshallow = []
    if depth is not None:
        included_commits = [o for o in send if objects.get(o, (None,))[0] == "commit"]
        for oid in included_commits:
            parents = parse_commit(objects[oid][1])["parents"]
            if any(p not in send and p in objects for p in parents):
                shallow_new.append(oid)
        for old in shallow_old or []:
            if old in wanted:
                parents = parse_commit(objects[old][1])["parents"] if objects.get(old, (None,))[0] == "commit" else []
                if parents and all(p in send for p in parents):
                    unshallow.append(old)
    return send, sorted(shallow_new), sorted(unshallow)


def sideband_pack(pack):
    out = bytearray()
    step = 65515
    for i in range(0, len(pack), step):
        chunk = pack[i:i + step]
        out += pkt(b"\x01" + chunk)
    return bytes(out)


def fetch_v2_response(repo, wants, haves, depth, shallow_old):
    key = (repo.name, tuple(sorted(wants)), tuple(sorted(haves)), depth,
           tuple(sorted(shallow_old or [])))
    cached = STORE.fetch_cache.get(key)
    if cached is not None:
        return cached
    send, shallow_new, unshallow = fetch_send_set(repo, wants, haves, depth, shallow_old)
    objs = [(repo.objects[o][0], repo.objects[o][1]) for o in sorted(send) if o in repo.objects]
    pack = write_pack(objs)
    parts = [pkt("acknowledgments\n"), pkt("NAK\n"), DELIM]
    if shallow_new or unshallow:
        parts.append(pkt("shallow-info\n"))
        for oid in shallow_new:
            parts.append(pkt("shallow %s\n" % oid))
        for oid in unshallow:
            parts.append(pkt("unshallow %s\n" % oid))
        parts.append(DELIM)
    parts.append(pkt("packfile\n"))
    body = b"".join(parts) + sideband_pack(pack) + FLUSH
    if len(STORE.fetch_cache) < 64:
        STORE.fetch_cache[key] = body
    return body


def fetch_v0_response(repo, wants, haves, depth, shallow_old):
    key = ("v0", repo.name, tuple(sorted(wants)), tuple(sorted(haves)), depth,
           tuple(sorted(shallow_old or [])))
    cached = STORE.fetch_cache.get(key)
    if cached is not None:
        return cached
    send, shallow_new, unshallow = fetch_send_set(repo, wants, haves, depth, shallow_old)
    objs = [(repo.objects[o][0], repo.objects[o][1]) for o in sorted(send) if o in repo.objects]
    pack = write_pack(objs)
    body = pkt("NAK\n")
    for oid in shallow_new:
        body += pkt("shallow %s\n" % oid)
    for oid in unshallow:
        body += pkt("unshallow %s\n" % oid)
    body += sideband_pack(pack) + FLUSH
    STORE.fetch_cache[key] = body
    return body


# ---------------------------------------------------------------------------
# shared creation helpers (REST / GraphQL / MCP share one store)
# ---------------------------------------------------------------------------

def create_repo(name, private, description):
    if not name or not isinstance(name, str):
        return None, "Repository name is required"
    if name in STORE.repos:
        return None, "already exists"
    dbid = STORE.next_repo_id
    STORE.next_repo_id += 1
    repo = Repo(name, private, description, dbid, STORE.tick())
    STORE.repos[name] = repo
    return repo, None


def create_issue(repo, title, body, labels=()):
    number = repo.next_number
    repo.next_number += 1
    dbid = repo.dbid * 1000000 + number
    issue = {"number": number, "dbid": dbid, "gid": gid("issue", repo.dbid, number),
             "title": title or "", "body": body or "", "state": "open",
             "labels": list(labels), "seq": STORE.tick()}
    repo.issues[number] = issue
    repo.comments.setdefault(number, [])
    return issue


def create_pr(repo, title, body, head, base):
    number = repo.next_number
    repo.next_number += 1
    dbid = repo.dbid * 1000000 + number
    pr = {"number": number, "dbid": dbid, "gid": gid("pr", repo.dbid, number),
          "title": title or "", "body": body or "", "state": "open",
          "head": head, "base": base, "merged": False, "merge_sha": None,
          "mergeable": True, "seq": STORE.tick()}
    repo.prs[number] = pr
    pr["mergeable"] = not pr_conflict(repo, pr)
    return pr


def find_repo_by_dbid(dbid):
    for repo in STORE.repos.values():
        if repo.dbid == dbid:
            return repo
    return None


# ---------------------------------------------------------------------------
# HTTP handler
# ---------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def log_message(self, *args):
        pass

    def setup(self):
        super().setup()
        # Kill Nagle on the socket: the suite drives thousands of small
        # request/response round trips over one keep-alive connection, and
        # Nagle + delayed ACK adds ~20-40 ms per round trip (the read
        # workload blew its 60 s budget on this alone).
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    # -- plumbing ---------------------------------------------------------
    def _read_body_raw(self):
        length = self.headers.get("Content-Length")
        if not length:
            return b""
        try:
            n = int(length)
        except ValueError:
            return b""
        if n <= 0:
            return b""
        return self.rfile.read(n)

    def _read_body(self):
        # The body is drained once per request in _dispatch (see there) and
        # cached, so handlers that answer early (401/404) never leave unread
        # bytes on the HTTP/1.1 keep-alive connection.
        if getattr(self, "_body_cache", None) is not None:
            return self._body_cache
        self._body_cache = self._read_body_raw()
        return self._body_cache

    def _send(self, status, body, content_type="application/json", extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-GitHub-Request-Id", STORE.next_req_id())
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if body and self.command != "HEAD":
            self.wfile.write(body)

    def _json(self, status, obj, extra=None):
        self._send(status, json.dumps(obj, ensure_ascii=False, separators=(",", ":")),
                   "application/json", extra)

    def _err(self, status, message):
        self._json(status, {"message": message})

    def _auth_ok(self):
        if not TOKEN:
            return True
        auth = (self.headers.get("Authorization") or "").strip()
        return auth == "Bearer " + TOKEN

    def _json_body(self):
        """Parsed JSON body, or {} when empty. Raises ValueError on bad JSON."""
        raw = self._read_body()
        if not raw.strip():
            return {}
        try:
            value = json.loads(raw.decode("utf-8"))
        except Exception:
            raise ValueError("malformed JSON")
        if not isinstance(value, dict):
            raise ValueError("JSON body must be an object")
        return value

    # -- entry points ------------------------------------------------------
    def do_GET(self):
        self._dispatch()

    def do_POST(self):
        self._dispatch()

    def do_PUT(self):
        self._dispatch()

    def do_PATCH(self):
        self._dispatch()

    def do_DELETE(self):
        self._dispatch()

    def _dispatch(self):
        try:
            # Drain the request body BEFORE routing: an early answer (401
            # for a missing token, 404 for an unknown path) that leaves the
            # body unread poisons the HTTP/1.1 keep-alive connection — the
            # client's next request on it is then parsed as garbage and the
            # server answers with its HTML error page.
            self._body_cache = self._read_body_raw()
            with STORE.lock:
                self._route()
        except BrokenPipeError:
            pass
        except ConnectionResetError:
            pass
        except Exception:
            try:
                self._err(500, "Internal Server Error")
            except Exception:
                pass

    def _route(self):
        parsed = urllib.parse.urlparse(self.path)
        path = urllib.parse.unquote(parsed.path)
        query = urllib.parse.parse_qs(parsed.query)
        method = self.command

        if path == "/healthz":
            self._json(200, {"ok": True})
            return
        if not self._auth_ok():
            self._err(401, "Requires authentication")
            return

        if path == "/api/graphql" or path.startswith("/api/graphql/"):
            if method == "POST":
                self._graphql()
            else:
                self._err(404, "Not Found")
            return
        if path == "/mcp":
            if method == "POST":
                self._mcp()
            else:
                self._err(404, "Not Found")
            return
        if path.startswith("/api/v3"):
            self._rest(path[len("/api/v3"):], query, method)
            return
        m = re.match(r"^/([^/]+)/([^/]+)\.git(/.*)$", path)
        if m:
            owner, name, suffix = m.group(1), m.group(2), m.group(3)
            self._git(owner, name, suffix, query, method)
            return
        self._err(404, "Not Found")

    # -- REST --------------------------------------------------------------
    def _rest(self, rest, query, method):
        segments = [s for s in rest.split("/") if s != ""]
        try:
            body = self._json_body() if method in ("POST", "PUT", "PATCH", "DELETE") else {}
        except ValueError:
            self._err(400, "Invalid JSON body")
            return

        if not segments:
            extra = {"X-OAuth-Scopes": "repo, user"}
            self._json(200, {"current_user_url": "/api/v3/user",
                             "repository_url": "/api/v3/repos/{owner}/{repo}"}, extra)
            return
        if segments == ["meta"]:
            if method != "GET":
                self._err(404, "Not Found")
                return
            self._json(200, {"installed_version": VERSION, "version": VERSION})
            return
        if segments == ["user"]:
            if method != "GET":
                self._err(404, "Not Found")
                return
            login = STORE.login()
            if not login:
                self._err(404, "Not Found")
                return
            self._json(200, {"login": login, "id": 1, "type": "User",
                             "node_id": gid("user", login),
                             "html_url": "https://example.invalid/" + login,
                             "url": "/api/v3/users/" + login})
            return
        if segments[:2] == ["user", "repos"]:
            if len(segments) == 2:
                if method == "GET":
                    self._list_user_repos(query)
                elif method == "POST":
                    name = body.get("name")
                    repo, err = create_repo(name, body.get("private", False),
                                            body.get("description", ""))
                    if err == "already exists":
                        self._err(422, "Repository already exists")
                    elif err:
                        self._err(422, err)
                    else:
                        self._json(201, repo_json(repo))
                else:
                    self._err(404, "Not Found")
                return
            self._err(404, "Not Found")
            return
        if segments[0] == "repos" and len(segments) >= 3:
            owner, name = segments[1], segments[2]
            STORE.learn(owner)
            if owner != STORE.learned_login:
                self._err(404, "Not Found")
                return
            repo = STORE.repos.get(name)
            if repo is None:
                self._err(404, "Not Found")
                return
            self._repo_route(repo, segments[3:], query, method, body)
            return
        self._err(404, "Not Found")

    def _list_user_repos(self, query):
        per_page = self._page_size(query, 30)
        page = self._page(query)
        repos = sorted(STORE.repos.values(), key=lambda r: r.created_seq)
        total = len(repos)
        start = (page - 1) * per_page
        items = repos[start:start + per_page]
        extra = {}
        if start + per_page < total:
            base = "http://%s/api/v3/user/repos?per_page=%d&page=%d" % (
                self.headers.get("Host", "localhost"), per_page, page + 1)
            extra["Link"] = '<%s>; rel="next"' % base
        self._json(200, [repo_json(r) for r in items], extra)

    @staticmethod
    def _page_size(query, default):
        try:
            return max(1, min(100, int(query.get("per_page", [default])[0])))
        except (ValueError, TypeError):
            return default

    @staticmethod
    def _page(query):
        try:
            return max(1, int(query.get("page", ["1"])[0]))
        except (ValueError, TypeError):
            return 1

    def _repo_route(self, repo, rest, query, method, body):
        login = STORE.login()
        if not rest:
            if method == "GET":
                self._json(200, repo_json(repo))
            elif method == "PATCH":
                if "description" in body:
                    repo.description = body["description"] or ""
                if "private" in body:
                    repo.private = bool(body["private"])
                self._json(200, repo_json(repo))
            elif method == "DELETE":
                del STORE.repos[repo.name]
                self._send(204, b"")
            else:
                self._err(404, "Not Found")
            return

        head = rest[0]
        if head == "branches":
            if len(rest) == 1 and method == "GET":
                out = []
                for ref in sorted(repo.refs):
                    if ref.startswith("refs/heads/"):
                        out.append({"name": ref[len("refs/heads/"):],
                                    "commit": {"sha": repo.refs[ref],
                                               "url": "/api/v3/repos/%s/%s/commits/%s" % (login, repo.name, repo.refs[ref])},
                                    "protected": False})
                self._json(200, out)
                return
            if len(rest) == 2 and method == "GET":
                tip = repo.refs.get("refs/heads/" + rest[1])
                if tip is None:
                    self._err(404, "Not Found")
                    return
                self._json(200, {"name": rest[1], "commit": {"sha": tip}, "protected": False})
                return
            self._err(404, "Not Found")
            return

        if head == "commits" and method == "GET" and len(rest) == 1:
            ref = query.get("sha", [repo.default_branch])[0]
            commits = list_commits(repo, ref)
            per_page = self._page_size(query, 30)
            page = self._page(query)
            start = (page - 1) * per_page
            self._json(200, [commit_json(repo, c) for c in commits[start:start + per_page]])
            return

        if head == "git" and rest[1:2] == ["refs"]:
            if method == "POST" and len(rest) == 2:
                ref = body.get("ref", "")
                sha = body.get("sha", "")
                if not ref.startswith("refs/") or not is_oid(sha):
                    self._err(422, "Invalid ref or sha")
                    return
                if ref in repo.refs:
                    self._err(422, "Reference already exists")
                    return
                if sha not in repo.objects:
                    self._err(422, "Object does not exist")
                    return
                repo.refs[ref] = sha
                self._json(201, {"ref": ref, "object": {"sha": sha, "type": "commit"},
                                 "url": "/api/v3/repos/%s/%s/git/refs/%s" % (login, repo.name, ref)})
                return
            if method == "GET" and len(rest) >= 3:
                ref = "/".join(rest[2:])
                tip = repo.refs.get(ref)
                if tip is None:
                    self._err(404, "Not Found")
                    return
                self._json(200, {"ref": ref, "object": {"sha": tip, "type": "commit"}})
                return
            self._err(404, "Not Found")
            return

        if head == "contents":
            self._contents(repo, rest[1:], query, method, body)
            return

        if head == "labels":
            if method == "POST" and len(rest) == 1:
                name = body.get("name", "")
                color = body.get("color", "ededed")
                if not name:
                    self._err(422, "Label name is required")
                    return
                repo.labels[name] = {"name": name, "color": color}
                self._json(201, {"id": 1, "name": name, "color": color,
                                 "description": "", "default": False})
                return
            if method == "GET" and len(rest) == 1:
                self._json(200, [{"id": 1, "name": n, "color": l["color"],
                                  "description": "", "default": False}
                                 for n, l in repo.labels.items()])
                return
            self._err(404, "Not Found")
            return

        if head == "issues":
            self._issues(repo, rest[1:], query, method, body)
            return

        if head == "pulls":
            self._pulls(repo, rest[1:], query, method, body)
            return

        self._err(404, "Not Found")

    # -- contents ------------------------------------------------------------
    def _contents(self, repo, path_segs, query, method, body):
        path = "/".join(path_segs)
        ref = body.get("branch") if method in ("PUT", "DELETE") else None
        if ref is None:
            ref = query.get("ref", [repo.default_branch])[0]
        tip = repo.refs.get("refs/heads/" + ref) or (ref if is_oid(ref) else None)
        tree = None
        if tip and tip in repo.objects and repo.objects[tip][0] == "commit":
            tree = parse_commit(repo.objects[tip][1])["tree"]

        def lookup(p):
            if not p:
                return ("dir", tree)
            flat = flatten_tree(repo.objects, tree) if tree else {}
            if p in flat:
                return ("file", flat[p][1])
            prefix = p + "/"
            if any(k.startswith(prefix) for k in flat):
                return ("dir", None)
            return (None, None)

        if method == "GET":
            kind, value = lookup(path)
            if kind is None:
                self._err(404, "Not Found")
                return
            if kind == "file":
                data = repo.objects[value][1]
                name = path.split("/")[-1]
                self._json(200, {"type": "file", "encoding": "base64",
                                 "size": len(data), "name": name, "path": path,
                                 "content": base64.b64encode(data).decode("ascii"),
                                 "sha": value,
                                 "url": "/api/v3/repos/%s/%s/contents/%s" % (STORE.login(), repo.name, path)})
                return
            flat = flatten_tree(repo.objects, tree) if tree else {}
            prefix = (path + "/") if path else ""
            children = {}
            for k, (_mode, oid) in flat.items():
                if not k.startswith(prefix):
                    continue
                rest_p = k[len(prefix):]
                first = rest_p.split("/")[0]
                children.setdefault(first, ("/" in rest_p, oid))
            out = []
            for name in sorted(children):
                is_dir, oid = children[name]
                out.append({"type": "dir" if is_dir else "file", "size": 0 if is_dir else len(repo.objects[oid][1]),
                            "name": name, "path": prefix + name, "sha": oid,
                            "url": "/api/v3/repos/%s/%s/contents/%s" % (STORE.login(), repo.name, prefix + name)})
            self._json(200, out)
            return

        if method == "PUT":
            message = body.get("message", "")
            content_b64 = body.get("content", "")
            try:
                data = base64.b64decode(content_b64, validate=False)
            except Exception:
                self._err(400, "Invalid base64 content")
                return
            branch = body.get("branch") or repo.default_branch
            branch_tip_oid = repo.refs.get("refs/heads/" + branch)
            if branch_tip_oid is None:
                # create the branch: from the default tip, or as the root commit
                base_tip = repo.refs.get("refs/heads/" + repo.default_branch)
                if base_tip is not None:
                    repo.refs["refs/heads/" + branch] = base_tip
                    branch_tip_oid = base_tip
            branch_tree = None
            if branch_tip_oid and branch_tip_oid in repo.objects:
                branch_tree = parse_commit(repo.objects[branch_tip_oid][1])["tree"]
            flat = flatten_tree(repo.objects, branch_tree) if branch_tree else {}
            existed = path in flat
            if existed:
                current_sha = flat[path][1]
                given_sha = (body.get("sha") or "").lower()
                if not given_sha or given_sha != current_sha.lower():
                    self._err(409, "sha does not match the current file")
                    return
            blob_oid = hash_object("blob", data)
            repo.objects[blob_oid] = ("blob", data)
            flat[path] = ("100644", blob_oid)
            new_tree = build_tree_from_map(repo.objects, flat)
            parents = [branch_tip_oid] if branch_tip_oid else []
            commit_oid = make_commit(repo, new_tree, parents, message or "Update %s" % path)
            repo.refs["refs/heads/" + branch] = commit_oid
            self._json(201 if not existed else 200,
                       {"content": {"name": path.split("/")[-1], "path": path,
                                    "sha": blob_oid, "size": len(data),
                                    "type": "file", "encoding": "base64"},
                        "commit": {"sha": commit_oid, "message": message}})
            return

        if method == "DELETE":
            branch = body.get("branch") or repo.default_branch
            branch_tip_oid = repo.refs.get("refs/heads/" + branch)
            if not branch_tip_oid:
                self._err(404, "Not Found")
                return
            branch_tree = parse_commit(repo.objects[branch_tip_oid][1])["tree"]
            flat = flatten_tree(repo.objects, branch_tree)
            if path not in flat:
                self._err(404, "Not Found")
                return
            given_sha = (body.get("sha") or "").lower()
            if given_sha and given_sha != flat[path][1].lower():
                self._err(409, "sha does not match the current file")
                return
            del flat[path]
            new_tree = build_tree_from_map(repo.objects, flat)
            commit_oid = make_commit(repo, new_tree, [branch_tip_oid],
                                     body.get("message") or "Delete %s" % path)
            repo.refs["refs/heads/" + branch] = commit_oid
            self._json(200, {"commit": {"sha": commit_oid, "message": body.get("message", "")}})
            return

        self._err(404, "Not Found")

    # -- issues --------------------------------------------------------------
    def _issues(self, repo, rest, query, method, body):
        if not rest:
            if method == "GET":
                state = query.get("state", ["open"])[0]
                sort_dir = query.get("direction", ["desc"])[0]
                items = [i for i in repo.issues.values()
                         if state == "all" or i["state"] == state]
                items.sort(key=lambda i: i["seq"], reverse=(sort_dir != "asc"))
                per_page = self._page_size(query, 30)
                page = self._page(query)
                start = (page - 1) * per_page
                self._json(200, [issue_json(repo, i) for i in items[start:start + per_page]])
                return
            if method == "POST":
                labels = body.get("labels", [])
                names = []
                for lab in labels:
                    names.append(lab.get("name") if isinstance(lab, dict) else lab)
                for name in names:
                    if name not in repo.labels:
                        self._err(422, "Validation Failed: label '%s' does not exist" % name)
                        return
                issue = create_issue(repo, body.get("title", ""), body.get("body", ""), names)
                self._json(201, issue_json(repo, issue))
                return
            self._err(404, "Not Found")
            return
        try:
            number = int(rest[0])
        except ValueError:
            self._err(404, "Not Found")
            return
        issue = repo.issues.get(number)
        if len(rest) == 1:
            if method == "GET":
                if issue is None:
                    self._err(404, "Not Found")
                    return
                self._json(200, issue_json(repo, issue))
                return
            if method == "PATCH":
                if issue is None:
                    self._err(404, "Not Found")
                    return
                if "state" in body:
                    issue["state"] = body["state"]
                if "title" in body:
                    issue["title"] = body["title"]
                if "body" in body:
                    issue["body"] = body["body"]
                if "labels" in body:
                    names = [l.get("name") if isinstance(l, dict) else l for l in body["labels"]]
                    for name in names:
                        if name not in repo.labels:
                            self._err(422, "Validation Failed: label '%s' does not exist" % name)
                            return
                    issue["labels"] = names
                self._json(200, issue_json(repo, issue))
                return
            self._err(404, "Not Found")
            return
        if rest[1] == "comments":
            if issue is None:
                self._err(404, "Not Found")
                return
            if method == "GET":
                self._json(200, [{"id": c["id"], "body": c["body"],
                                  "user": {"login": STORE.login(), "type": "User"},
                                  "created_at": FIXED_TS, "updated_at": FIXED_TS}
                                 for c in repo.comments.get(number, [])])
                return
            if method == "POST":
                cid = repo.next_comment_id
                repo.next_comment_id += 1
                comment = {"id": cid, "body": body.get("body", ""),
                           "gid": gid("comment", repo.dbid, number, cid)}
                repo.comments.setdefault(number, []).append(comment)
                self._json(201, {"id": cid, "body": comment["body"],
                                 "user": {"login": STORE.login(), "type": "User"},
                                 "created_at": FIXED_TS, "updated_at": FIXED_TS})
                return
        self._err(404, "Not Found")

    # -- pulls ---------------------------------------------------------------
    def _pulls(self, repo, rest, query, method, body):
        if not rest:
            if method == "GET":
                state = query.get("state", ["open"])[0]
                items = [p for p in repo.prs.values()
                         if state == "all" or p["state"] == state]
                items.sort(key=lambda p: p["seq"])
                per_page = self._page_size(query, 30)
                page = self._page(query)
                start = (page - 1) * per_page
                self._json(200, [pr_json(repo, p) for p in items[start:start + per_page]])
                return
            if method == "POST":
                head = str(body.get("head", ""))
                base = str(body.get("base", ""))
                head = head.split(":")[-1]
                base = base.split(":")[-1]
                if not head or branch_tip(repo, head) is None:
                    self._err(422, "Validation Failed: head branch '%s' does not exist" % head)
                    return
                if not base or branch_tip(repo, base) is None:
                    self._err(422, "Validation Failed: base branch '%s' does not exist" % base)
                    return
                pr = create_pr(repo, body.get("title", ""), body.get("body", ""), head, base)
                self._json(201, pr_json(repo, pr))
                return
            self._err(404, "Not Found")
            return
        try:
            number = int(rest[0])
        except ValueError:
            self._err(404, "Not Found")
            return
        pr = repo.prs.get(number)
        if len(rest) == 1:
            if method == "GET":
                if pr is None:
                    self._err(404, "Not Found")
                    return
                self._json(200, pr_json(repo, pr))
                return
            self._err(404, "Not Found")
            return
        if rest[1] == "files" and method == "GET":
            if pr is None:
                self._err(404, "Not Found")
                return
            self._json(200, pr_files(repo, pr))
            return
        if rest[1] == "merge" and method == "PUT":
            if pr is None:
                self._err(404, "Not Found")
                return
            if pr["merged"]:
                self._err(405, "Pull request already merged")
                return
            if pr_conflict(repo, pr):
                self._err(405, "Merge conflict")
                return
            merge_oid = squash_merge(repo, pr)
            if merge_oid is None:
                self._err(405, "Merge conflict")
                return
            pr["merged"] = True
            pr["state"] = "closed"
            pr["merge_sha"] = merge_oid
            self._json(200, {"sha": merge_oid, "merged": True,
                             "message": "Pull request successfully merged"})
            return
        self._err(404, "Not Found")


    # -- git smart HTTP -------------------------------------------------------
    def _git(self, owner, name, suffix, query, method):
        STORE.learn(owner)
        if owner != STORE.learned_login:
            self._err(404, "Not Found")
            return
        repo = STORE.repos.get(name)
        if suffix == "/info/refs":
            service = query.get("service", [""])[0]
            if service not in ("git-upload-pack", "git-receive-pack"):
                self._err(400, "Unknown service")
                return
            if repo is None:
                self._err(404, "Not Found")
                return
            if method != "GET":
                self._err(405, "Method Not Allowed")
                return
            v2 = (service == "git-upload-pack" and
                  (self.headers.get("Git-Protocol") or "") == "version=2")
            if v2:
                body = v2_advertisement()
            else:
                body = v0_advertisement(repo, service)
            ctype = "application/x-%s-advertisement" % service
            self._send(200, body, ctype)
            return
        if repo is None:
            self._err(404, "Not Found")
            return
        if suffix == "/git-upload-pack" and method == "POST":
            self._upload_pack(repo)
            return
        if suffix == "/git-receive-pack" and method == "POST":
            self._receive_pack(repo)
            return
        self._err(404, "Not Found")

    def _upload_pack(self, repo):
        raw = self._read_body()
        v2 = (self.headers.get("Git-Protocol") or "") == "version=2"
        try:
            packets, _ = pkt_decode(raw)
        except PktError:
            self._err(400, "Malformed pkt-line")
            return
        lines = [p[1].decode("utf-8", "replace") for p in packets if p[0] == "data"]
        if v2:
            command = None
            wants, haves, shallow, depth = [], [], [], None
            # NOTE: the delim packet is a control packet, not a data packet,
            # so it never appears in `lines`; collect fetch args from every
            # data line (command/agent/object-format lines never start with
            # want/have/shallow/deepen, so no gate is needed).
            for line in lines:
                text = line.rstrip("\n")
                if text == "command=ls-refs":
                    command = "ls-refs"
                elif text == "command=fetch":
                    command = "fetch"
                if text.startswith("want "):
                    wants.append(text[5:].strip())
                elif text.startswith("have "):
                    haves.append(text[5:].strip())
                elif text.startswith("shallow "):
                    shallow.append(text[8:].strip())
                elif text.startswith("deepen "):
                    try:
                        depth = int(text[7:].strip())
                    except ValueError:
                        pass
            # ls-refs args live after the delim packet too; re-scan for them
            prefixes, peel, symrefs, unborn = [], True, True, False
            for line in lines:
                text = line.rstrip("\n")
                if text.startswith("ref-prefix "):
                    prefixes.append(text[len("ref-prefix "):])
                elif text == "peel":
                    peel = True
                elif text == "symrefs":
                    symrefs = True
                elif text == "unborn":
                    unborn = True
            if command == "ls-refs":
                body = ls_refs_v2(repo, prefixes, peel, symrefs, unborn)
                self._send(200, body, "application/x-git-upload-pack-result")
                return
            if command == "fetch":
                body = fetch_v2_response(repo, wants, haves, depth, shallow)
                self._send(200, body, "application/x-git-upload-pack-result")
                return
            self._err(400, "Unknown v2 command")
            return
        # v0 fetch: wants, then flush, then haves + done
        wants, haves, shallow, depth = [], [], [], None
        for line in lines:
            text = line.rstrip("\n")
            if text.startswith("want "):
                wants.append(text[5:].split(" ")[0])
            elif text.startswith("have "):
                haves.append(text[5:].strip())
            elif text.startswith("shallow "):
                shallow.append(text[8:].strip())
            elif text.startswith("deepen "):
                try:
                    depth = int(text[7:].strip())
                except ValueError:
                    pass
        body = fetch_v0_response(repo, wants, haves, depth, shallow)
        self._send(200, body, "application/x-git-upload-pack-result")

    def _receive_pack(self, repo):
        raw = self._read_body()
        try:
            packets, rest_off = pkt_decode_until_flush(raw)
        except PktError:
            self._err(400, "Malformed pkt-line")
            return
        commands = []
        for kind, payload in packets:
            if kind != "data":
                continue
            line = payload.decode("utf-8", "replace").rstrip("\n")
            parts = line.split("\0", 1)
            fields = parts[0].split(" ")
            if len(fields) != 3:
                self._err(400, "Malformed push command")
                return
            old, new, ref = fields
            if not is_oid(old) or not is_oid(new) or not ref.startswith("refs/"):
                self._err(400, "Malformed push command")
                return
            commands.append((old, new, ref))
        pack_bytes = raw[rest_off:]
        new_objects = {}
        if pack_bytes:
            try:
                new_objects = read_pack(pack_bytes)
            except Exception:
                new_objects = {}
                # an unparseable pack: refuse every ref below via unpack failure
                report = pkt_lines(["unpack error\n", "flush"])
                self._send(200, pkt(b"\x01" + report) + FLUSH,
                           "application/x-git-receive-pack-result")
                return
        for oid, obj in new_objects.items():
            repo.objects.setdefault(oid, obj)
        report_lines = ["unpack ok\n"]
        for old, new, ref in commands:
            current = repo.refs.get(ref)
            ok = True
            reason = ""
            if new == ZERO_OID:
                # delete
                if current is None:
                    ok, reason = False, "no such ref"
                elif old != ZERO_OID and old != current:
                    ok, reason = False, "non-fast-forward"
                else:
                    del repo.refs[ref]
            elif old == ZERO_OID:
                # create
                if current is not None:
                    ok, reason = False, "already exists"
                elif new not in repo.objects:
                    ok, reason = False, "missing object"
                else:
                    repo.refs[ref] = new
            else:
                # update
                if current is None:
                    ok, reason = False, "no such ref"
                elif old != current:
                    ok, reason = False, "non-fast-forward"
                elif new == old:
                    pass
                elif new not in repo.objects:
                    ok, reason = False, "missing object"
                else:
                    anc, _ = collect_reachable(repo.objects, [new])
                    if old not in anc:
                        ok, reason = False, "non-fast-forward"
                    else:
                        repo.refs[ref] = new
            if ok:
                report_lines.append("ok %s\n" % ref)
            else:
                report_lines.append("ng %s %s\n" % (ref, reason))
        report = pkt_lines(report_lines + ["flush"])
        body = pkt(b"\x01" + report) + FLUSH
        self._send(200, body, "application/x-git-receive-pack-result")

    # -- GraphQL -------------------------------------------------------------
    def _graphql(self):
        raw = self._read_body()
        try:
            payload = json.loads(raw.decode("utf-8")) if raw.strip() else {}
        except Exception:
            self._json(400, {"errors": [{"message": "Invalid JSON body"}]})
            return
        if isinstance(payload, list):
            results = [self._graphql_one(op) for op in payload]
            self._json(200, results)
        elif isinstance(payload, dict):
            self._json(200, self._graphql_one(payload))
        else:
            self._json(400, {"errors": [{"message": "Invalid GraphQL body"}]})

    def _graphql_one(self, op):
        query = op.get("query", "")
        variables = op.get("variables") or {}
        try:
            doc = GQLParser(query).parse()
        except GQLParseError as e:
            return {"data": None, "errors": [{"message": str(e)}]}
        executor = GQLExecutor(variables)
        return executor.execute(doc)

    # -- MCP ------------------------------------------------------------------
    def _mcp(self):
        raw = self._read_body()
        try:
            payload = json.loads(raw.decode("utf-8")) if raw.strip() else None
        except Exception:
            self._send(400, json.dumps({"jsonrpc": "2.0", "id": None,
                                        "error": {"code": -32700, "message": "Parse error"}}))
            return
        if not isinstance(payload, dict):
            self._send(400, json.dumps({"jsonrpc": "2.0", "id": None,
                                        "error": {"code": -32600, "message": "Invalid Request"}}))
            return
        method = payload.get("method", "")
        params = payload.get("params") or {}
        req_id = payload.get("id")
        if "id" not in payload:
            # notification: acknowledge, no body
            self._send(202, b"")
            return
        result, error = self._mcp_dispatch(method, params)
        if error is not None:
            self._json(200, {"jsonrpc": "2.0", "id": req_id, "error": error})
        else:
            self._json(200, {"jsonrpc": "2.0", "id": req_id, "result": result})

    def _mcp_dispatch(self, method, params):
        if method == "server/discover":
            return ({"supportedVersions": ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26"],
                     "capabilities": {"tools": {}},
                     "serverInfo": {"name": "github-forge", "version": VERSION},
                     "_meta": {"io.modelcontextprotocol/serverInfo":
                               {"name": "github-forge", "version": VERSION}}}, None)
        if method == "initialize":
            offered = params.get("protocolVersion", "2025-11-25")
            if offered not in ("2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"):
                offered = "2025-11-25"
            return ({"protocolVersion": offered,
                     "capabilities": {"tools": {}},
                     "serverInfo": {"name": "github-forge", "version": VERSION}}, None)
        if method == "tools/list":
            return ({"tools": MCP_TOOLS}, None)
        if method == "tools/call":
            return self._mcp_call(params)
        if method.startswith("notifications/"):
            return ({}, None)
        return (None, {"code": -32601, "message": "Method not found: %s" % method})

    def _mcp_call(self, params):
        name = params.get("name", "")
        args = params.get("arguments") or {}
        tool = next((t for t in MCP_TOOLS if t["name"] == name), None)
        if tool is None:
            return None, {"code": -32602, "message": "Unknown tool: %s" % name}
        required = tool["inputSchema"].get("required", [])
        missing = [r for r in required if r not in args or args[r] is None]
        if missing:
            return None, {"code": -32602,
                          "message": "Missing required argument(s): %s" % ", ".join(missing)}
        try:
            obj = MCP_HANDLERS[name](args)
        except MCPToolError as e:
            return ({"content": [{"type": "text", "text": str(e)}], "isError": True}, None)
        text = json.dumps(obj, ensure_ascii=False, separators=(",", ":"))
        return ({"content": [{"type": "text", "text": text}],
                 "structuredContent": obj}, None)


# ---------------------------------------------------------------------------
# GraphQL: tiny parser + executor for the documents gh / github-mcp-server send
# ---------------------------------------------------------------------------

class GQLParseError(ValueError):
    pass


class GQLParser:
    def __init__(self, text):
        self.text = text
        self.tokens = self._tokenize(text)
        self.pos = 0

    @staticmethod
    def _tokenize(text):
        tokens = []
        i, n = 0, len(text)
        while i < n:
            c = text[i]
            if c in " \t\r\n,":
                i += 1
                continue
            if c == "#":
                while i < n and text[i] != "\n":
                    i += 1
                continue
            if text.startswith("...", i):
                tokens.append(("dots", "..."))
                i += 3
                continue
            if c in "{}()[]:!=$|@":
                tokens.append(("punct", c))
                i += 1
                continue
            if c == '"':
                j = i + 1
                out = []
                while j < n and text[j] != '"':
                    if text[j] == "\\" and j + 1 < n:
                        esc = text[j + 1]
                        out.append({"n": "\n", "t": "\t", "r": "\r", '"': '"',
                                    "\\": "\\", "/": "/"}.get(esc, esc))
                        j += 2
                    else:
                        out.append(text[j])
                        j += 1
                if j >= n:
                    raise GQLParseError("unterminated string")
                tokens.append(("string", "".join(out)))
                i = j + 1
                continue
            if c.isdigit() or (c == "-" and i + 1 < n and text[i + 1].isdigit()):
                j = i
                if text[j] == "-":
                    j += 1
                while j < n and (text[j].isdigit() or text[j] == "."):
                    j += 1
                raw = text[i:j]
                tokens.append(("number", float(raw) if "." in raw else int(raw)))
                i = j
                continue
            if c.isalpha() or c == "_":
                j = i
                while j < n and (text[j].isalnum() or text[j] == "_"):
                    j += 1
                tokens.append(("name", text[i:j]))
                i = j
                continue
            raise GQLParseError("unexpected character %r" % c)
        tokens.append(("eof", None))
        return tokens

    def _peek(self):
        return self.tokens[self.pos]

    def _next(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def _expect(self, kind, value=None):
        tok = self._next()
        if tok[0] != kind or (value is not None and tok[1] != value):
            raise GQLParseError("expected %s %s, got %r" % (kind, value, tok))
        return tok

    def _accept(self, kind, value=None):
        tok = self._peek()
        if tok[0] == kind and (value is None or tok[1] == value):
            self.pos += 1
            return True
        return False

    def parse(self):
        ops = []
        while self._peek()[0] != "eof":
            kind, value = self._peek()
            if kind == "punct" and value == "{":
                ops.append({"kind": "query", "name": None, "vars": {},
                            "selections": self._selection_set()})
                continue
            if kind == "name" and value in ("query", "mutation", "subscription"):
                self._next()
                name = None
                if self._peek()[0] == "name":
                    name = self._next()[1]
                var_defs = {}
                if self._accept("punct", "("):
                    while not self._accept("punct", ")"):
                        self._expect("punct", "$")
                        vname = self._expect("name")[1]
                        self._expect("punct", ":")
                        self._type_ref()
                        if self._accept("punct", "="):
                            self._value()
                        var_defs[vname] = True
                ops.append({"kind": value, "name": name, "vars": var_defs,
                            "selections": self._selection_set()})
                continue
            if kind == "name" and value == "fragment":
                self._next()
                self._expect("name")
                self._expect("name", "on")
                self._expect("name")
                self._selection_set()
                continue
            raise GQLParseError("unexpected token %r" % (self._peek(),))
        if not ops:
            raise GQLParseError("empty document")
        return ops

    def _type_ref(self):
        if self._accept("punct", "["):
            self._type_ref()
            self._expect("punct", "]")
        else:
            self._expect("name")
        self._accept("punct", "!")

    def _selection_set(self):
        self._expect("punct", "{")
        sels = []
        while not self._accept("punct", "}"):
            sels.append(self._selection())
        return sels

    def _selection(self):
        if self._accept("dots"):
            if self._peek() == ("name", "on"):
                self._next()
                tname = self._expect("name")[1]
                return {"kind": "fragment", "type": tname,
                        "selections": self._selection_set()}
            self._expect("name")  # fragment spread name (unused in the docs)
            return {"kind": "fragment", "type": None, "selections": []}
        name = self._expect("name")[1]
        alias = None
        if self._accept("punct", ":"):
            alias = name
            name = self._expect("name")[1]
        args = {}
        if self._accept("punct", "("):
            while not self._accept("punct", ")"):
                aname = self._expect("name")[1]
                self._expect("punct", ":")
                args[aname] = self._value()
        while self._accept("punct", "@"):
            self._expect("name")
            if self._accept("punct", "("):
                depth = 1
                while depth:
                    tok = self._next()
                    if tok == ("punct", "("):
                        depth += 1
                    elif tok == ("punct", ")"):
                        depth -= 1
        sels = []
        if self._peek() == ("punct", "{"):
            sels = self._selection_set()
        return {"kind": "field", "alias": alias, "name": name, "args": args,
                "selections": sels}

    def _value(self):
        kind, value = self._next()
        if kind == "punct" and value == "$":
            return ("var", self._expect("name")[1])
        if kind == "string":
            return value
        if kind == "number":
            return value
        if kind == "name":
            if value == "true":
                return True
            if value == "false":
                return False
            if value == "null":
                return None
            return ("enum", value)
        if kind == "punct" and value == "[":
            items = []
            while not self._accept("punct", "]"):
                items.append(self._value())
            return items
        if kind == "punct" and value == "{":
            obj = {}
            while not self._accept("punct", "}"):
                key = self._expect("name")[1]
                self._expect("punct", ":")
                obj[key] = self._value()
            return obj
        raise GQLParseError("unexpected value token %r" % ((kind, value),))


TYPE_FIELDS = {
    "Issue": ["id", "number", "title", "state", "body", "createdAt", "updatedAt",
              "url", "author", "labels", "comments"],
    "PullRequest": ["id", "number", "title", "body", "state", "merged", "headRefName",
                    "baseRefName", "mergeable", "files", "createdAt", "updatedAt"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner", "defaultBranchRef",
                   "viewerPermission", "hasIssuesEnabled", "issue", "issues",
                   "pullRequests", "pullRequest", "createdAt", "updatedAt"],
    "SearchType": [],
}


class GQLExecutor:
    def __init__(self, variables):
        self.variables = variables or {}
        self.errors = []

    def _resolve_value(self, value):
        if isinstance(value, tuple) and value and value[0] == "var":
            return self.variables.get(value[1])
        if isinstance(value, tuple) and value and value[0] == "enum":
            return value[1]
        if isinstance(value, list):
            return [self._resolve_value(v) for v in value]
        if isinstance(value, dict):
            return {k: self._resolve_value(v) for k, v in value.items()}
        return value

    def _resolve_args(self, args):
        return {k: self._resolve_value(v) for k, v in args.items()}

    def execute(self, ops):
        data = {}
        for op in ops:
            root_type = "Mutation" if op["kind"] == "mutation" else "Query"
            root = self._root_object(root_type)
            for sel in op["selections"]:
                data.update(self._exec_object(root, root_type, [sel]))
        result = {"data": data}
        if self.errors:
            result["errors"] = self.errors
        return result

    def _root_object(self, root_type):
        if root_type == "Query":
            login = STORE.login()
            return {"_type": "Query",
                    "viewer": {"_type": "User", "login": login},
                    "repository": self._gql_repository,
                    "node": self._gql_node,
                    "__type": self._gql_type}
        return {"_type": "Mutation",
                "createIssue": self._mut_create_issue,
                "closeIssue": self._mut_close_issue,
                "createPullRequest": self._mut_create_pr,
                "mergePullRequest": self._mut_merge_pr,
                "addComment": self._mut_add_comment}

    # -- root field resolvers ----------------------------------------------
    def _gql_repository(self, args):
        owner = args.get("owner")
        name = args.get("name")
        if owner != STORE.login():
            return None
        repo = STORE.repos.get(name)
        if repo is None:
            return None
        return self._repo_obj(repo)

    def _gql_node(self, args):
        decoded = ungid(args.get("id"))
        if decoded is None:
            return None
        kind, parts = decoded
        if kind == "repo":
            repo = find_repo_by_dbid(int(parts[0])) if parts else None
            return self._repo_obj(repo) if repo else None
        if kind == "issue" and len(parts) == 2:
            repo = find_repo_by_dbid(int(parts[0]))
            issue = repo.issues.get(int(parts[1])) if repo else None
            return self._issue_obj(repo, issue) if issue else None
        if kind == "pr" and len(parts) == 2:
            repo = find_repo_by_dbid(int(parts[0]))
            pr = repo.prs.get(int(parts[1])) if repo else None
            return self._pr_obj(repo, pr) if pr else None
        return {"_type": "Node", "id": args.get("id")}

    def _gql_type(self, args):
        name = args.get("name")
        if name == "SearchType":
            return {"_type": "__Type", "name": name, "fields": None,
                    "enumValues": [{"name": n} for n in
                                   ("ISSUE", "REPOSITORY", "USER", "PULL_REQUEST",
                                    "DISCUSSION", "COMMIT")]}
        if name in TYPE_FIELDS:
            fields = [{"name": f} for f in TYPE_FIELDS[name]]
            return {"_type": "__Type", "name": name, "fields": fields,
                    "enumValues": None}
        return None

    # -- object builders ----------------------------------------------------
    def _repo_obj(self, repo):
        login = STORE.login()
        return {
            "_type": "Repository",
            "id": repo.global_id(),
            "databaseId": repo.dbid,
            "name": repo.name,
            "nameWithOwner": "%s/%s" % (login, repo.name),
            "owner": {"_type": "User", "login": login},
            "defaultBranchRef": {"_type": "Ref", "name": repo.default_branch},
            "viewerPermission": "ADMIN",
            "hasIssuesEnabled": True,
            "issue": lambda args: self._issue_by_number(repo, args),
            "issues": lambda args: self._issues_conn(repo, args),
            "pullRequests": lambda args: self._prs_conn(repo, args),
            "pullRequest": lambda args: self._pr_by_number(repo, args),
        }

    @staticmethod
    def _issue_obj(repo, issue):
        return {"_type": "Issue", "id": issue["gid"], "number": issue["number"],
                "title": issue["title"],
                "state": "OPEN" if issue["state"] == "open" else "CLOSED",
                "body": issue["body"]}

    def _pr_obj(self, repo, pr):
        mergeable = "CONFLICTING" if pr_conflict(repo, pr) else "MERGEABLE"
        state = "MERGED" if pr["merged"] else ("OPEN" if pr["state"] == "open" else "CLOSED")
        return {"_type": "PullRequest", "id": pr["gid"], "number": pr["number"],
                "title": pr["title"], "body": pr["body"], "state": state,
                "merged": pr["merged"], "headRefName": pr["head"],
                "baseRefName": pr["base"], "mergeable": mergeable,
                "files": lambda args: self._pr_files_conn(repo, pr, args)}

    def _issue_by_number(self, repo, args):
        issue = repo.issues.get(args.get("number"))
        return self._issue_obj(repo, issue) if issue else None

    def _pr_by_number(self, repo, args):
        pr = repo.prs.get(args.get("number"))
        return self._pr_obj(repo, pr) if pr else None

    def _issues_conn(self, repo, args):
        issues = list(repo.issues.values())
        states = args.get("states")
        if states:
            wanted = set(states)
            issues = [i for i in issues
                      if ("OPEN" if i["state"] == "open" else "CLOSED") in wanted]
        order = args.get("orderBy") or {}
        if order.get("field") == "CREATED_AT" and order.get("direction") == "DESC":
            issues.sort(key=lambda i: (i["seq"], i["number"]), reverse=True)
        else:
            issues.sort(key=lambda i: (i["seq"], i["number"]))
        first = args.get("first")
        after = args.get("after")
        if after:
            try:
                cursor_num = int(base64.urlsafe_b64decode(
                    after + "=" * (-len(after) % 4)).decode().split(":")[1])
                issues = [i for i in issues if i["number"] > cursor_num] \
                    if order.get("direction") != "DESC" else \
                    [i for i in issues if i["number"] < cursor_num]
            except Exception:
                pass
        total = len(issues)
        if first is not None:
            page = issues[:first]
        else:
            page = issues
        has_next = len(page) < total
        end_cursor = None
        if page:
            end_cursor = base64.urlsafe_b64encode(
                ("cursor:%d" % page[-1]["number"]).encode()).decode().rstrip("=")
        return {"_type": "IssueConnection",
                "nodes": [self._issue_obj(repo, i) for i in page],
                "pageInfo": {"_type": "PageInfo", "hasNextPage": has_next,
                             "endCursor": end_cursor}}

    def _prs_conn(self, repo, args):
        prs = sorted(repo.prs.values(), key=lambda p: p["seq"])
        first = args.get("first")
        if first is not None:
            prs = prs[:first]
        return {"_type": "PullRequestConnection",
                "nodes": [self._pr_obj(repo, p) for p in prs]}

    def _pr_files_conn(self, repo, pr, args):
        files = pr_files(repo, pr)
        first = args.get("first")
        if first is not None:
            files = files[:first]
        return {"_type": "PullRequestChangedFileConnection",
                "nodes": [{"_type": "PullRequestChangedFile", "path": f["filename"]}
                          for f in files]}

    # -- mutations ------------------------------------------------------------
    def _mut_create_issue(self, args):
        inp = args.get("input") or {}
        decoded = ungid(inp.get("repositoryId"))
        if not decoded or decoded[0] != "repo":
            return {"_type": "CreateIssuePayload", "issue": None}
        repo = find_repo_by_dbid(int(decoded[1][0]))
        if repo is None:
            return {"_type": "CreateIssuePayload", "issue": None}
        issue = create_issue(repo, inp.get("title", ""), inp.get("body", ""))
        return {"_type": "CreateIssuePayload", "issue": self._issue_obj(repo, issue)}

    def _mut_close_issue(self, args):
        inp = args.get("input") or {}
        decoded = ungid(inp.get("issueId"))
        if not decoded or decoded[0] != "issue":
            return {"_type": "CloseIssuePayload", "issue": None}
        repo = find_repo_by_dbid(int(decoded[1][0]))
        issue = repo.issues.get(int(decoded[1][1])) if repo else None
        if issue is None:
            return {"_type": "CloseIssuePayload", "issue": None}
        issue["state"] = "closed"
        return {"_type": "CloseIssuePayload", "issue": self._issue_obj(repo, issue)}

    def _mut_create_pr(self, args):
        inp = args.get("input") or {}
        decoded = ungid(inp.get("repositoryId"))
        if not decoded or decoded[0] != "repo":
            return {"_type": "CreatePullRequestPayload", "pullRequest": None}
        repo = find_repo_by_dbid(int(decoded[1][0]))
        if repo is None:
            return {"_type": "CreatePullRequestPayload", "pullRequest": None}
        head = inp.get("headRefName", "")
        base = inp.get("baseRefName", repo.default_branch)
        if branch_tip(repo, head) is None or branch_tip(repo, base) is None:
            return {"_type": "CreatePullRequestPayload", "pullRequest": None}
        pr = create_pr(repo, inp.get("title", ""), inp.get("body", ""), head, base)
        return {"_type": "CreatePullRequestPayload", "pullRequest": self._pr_obj(repo, pr)}

    def _mut_merge_pr(self, args):
        inp = args.get("input") or {}
        decoded = ungid(inp.get("pullRequestId"))
        if not decoded or decoded[0] != "pr":
            return {"_type": "MergePullRequestPayload", "pullRequest": None}
        repo = find_repo_by_dbid(int(decoded[1][0]))
        pr = repo.prs.get(int(decoded[1][1])) if repo else None
        if pr is None:
            return {"_type": "MergePullRequestPayload", "pullRequest": None}
        if not pr["merged"] and not pr_conflict(repo, pr):
            merge_oid = squash_merge(repo, pr)
            if merge_oid:
                pr["merged"] = True
                pr["state"] = "closed"
                pr["merge_sha"] = merge_oid
        return {"_type": "MergePullRequestPayload", "pullRequest": self._pr_obj(repo, pr)}

    def _mut_add_comment(self, args):
        inp = args.get("input") or {}
        decoded = ungid(inp.get("subjectId"))
        if not decoded or decoded[0] != "issue":
            return {"_type": "AddCommentPayload", "commentEdge": None}
        repo = find_repo_by_dbid(int(decoded[1][0]))
        number = int(decoded[1][1])
        issue = repo.issues.get(number) if repo else None
        if issue is None:
            return {"_type": "AddCommentPayload", "commentEdge": None}
        cid = repo.next_comment_id
        repo.next_comment_id += 1
        comment = {"id": cid, "body": inp.get("body", ""),
                   "gid": gid("comment", repo.dbid, number, cid)}
        repo.comments.setdefault(number, []).append(comment)
        return {"_type": "AddCommentPayload",
                "commentEdge": {"_type": "CommentEdge",
                                "node": {"_type": "Comment", "id": comment["gid"],
                                         "body": comment["body"]}}}

    # -- execution ------------------------------------------------------------
    def _exec_object(self, obj, type_name, selections):
        out = {}
        for sel in selections:
            if sel["kind"] == "fragment":
                if sel["type"] is None or sel["type"] == type_name or \
                        sel["type"] in ("Node",):
                    out.update(self._exec_object(obj, type_name, sel["selections"]))
                continue
            name = sel["name"]
            key = sel["alias"] or name
            if not isinstance(obj, dict) or name not in obj:
                self.errors.append(
                    {"message": 'Cannot query field "%s" on type "%s".' % (name, type_name)})
                out[key] = None
                continue
            value = obj[name]
            if callable(value):
                value = value(self._resolve_args(sel["args"]))
            if sel["selections"]:
                if value is None:
                    out[key] = None
                elif isinstance(value, list):
                    out[key] = [self._exec_object(
                        item, item.get("_type", type_name), sel["selections"])
                        if isinstance(item, dict) else item for item in value]
                elif isinstance(value, dict):
                    out[key] = self._exec_object(
                        value, value.get("_type", type_name), sel["selections"])
                else:
                    out[key] = value
            else:
                out[key] = value
        # strip internal markers
        return {k: v for k, v in out.items() if k != "_type"}


# ---------------------------------------------------------------------------
# MCP tools
# ---------------------------------------------------------------------------

class MCPToolError(Exception):
    pass


def _mcp_repo(args):
    owner = args.get("owner")
    name = args.get("repo")
    if owner is not None and owner != STORE.login():
        raise MCPToolError("Repository not found: %s/%s" % (owner, name))
    repo = STORE.repos.get(name)
    if repo is None:
        raise MCPToolError("Repository not found: %s" % name)
    return repo


def mcp_create_repo(args):
    repo, err = create_repo(args.get("name"), args.get("private", False),
                            args.get("description", ""))
    if err:
        raise MCPToolError("Repository already exists: %s" % args.get("name"))
    return repo_json(repo)


def mcp_get_repo(args):
    return repo_json(_mcp_repo(args))


def mcp_create_issue(args):
    repo = _mcp_repo(args)
    issue = create_issue(repo, args.get("title", ""), args.get("body", ""))
    return issue_json(repo, issue)


def mcp_list_issues(args):
    repo = _mcp_repo(args)
    state = args.get("state", "open")
    items = [i for i in repo.issues.values()
             if state in ("all", None) or i["state"] == state]
    items.sort(key=lambda i: i["seq"])
    return {"issues": [issue_json(repo, i) for i in items]}


def mcp_create_pr(args):
    repo = _mcp_repo(args)
    head = str(args.get("head", ""))
    base = str(args.get("base", ""))
    if branch_tip(repo, head) is None:
        raise MCPToolError("Head branch not found: %s" % head)
    if branch_tip(repo, base) is None:
        raise MCPToolError("Base branch not found: %s" % base)
    pr = create_pr(repo, args.get("title", ""), args.get("body", ""), head, base)
    return pr_json(repo, pr)


def mcp_merge_pr(args):
    repo = _mcp_repo(args)
    number = args.get("pull_number")
    try:
        number = int(number)
    except (TypeError, ValueError):
        raise MCPToolError("Invalid pull_number: %r" % (number,))
    pr = repo.prs.get(number)
    if pr is None:
        raise MCPToolError("Pull request not found: %d" % number)
    if pr["merged"]:
        raise MCPToolError("Pull request already merged")
    if pr_conflict(repo, pr):
        raise MCPToolError("Merge conflict")
    merge_oid = squash_merge(repo, pr)
    if merge_oid is None:
        raise MCPToolError("Merge conflict")
    pr["merged"] = True
    pr["state"] = "closed"
    pr["merge_sha"] = merge_oid
    return {"merged": True, "number": number, "sha": merge_oid,
            "message": "Pull request successfully merged"}


MCP_HANDLERS = {
    "create_repo": mcp_create_repo,
    "get_repo": mcp_get_repo,
    "create_issue": mcp_create_issue,
    "list_issues": mcp_list_issues,
    "create_pull_request": mcp_create_pr,
    "merge_pull_request": mcp_merge_pr,
}

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a new repository owned by the authenticated user.",
     "inputSchema": {"type": "object",
                     "properties": {"name": {"type": "string"},
                                    "description": {"type": "string"},
                                    "private": {"type": "boolean"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "full_name": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "body": {"type": "string"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository, optionally filtered by state.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "state": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Open a pull request from a head branch into a base branch.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "body": {"type": "string"},
                                    "head": {"type": "string"},
                                    "base": {"type": "string"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Squash-merge a pull request by number.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "pull_number": {"type": "integer"}},
                     "required": ["owner", "repo", "pull_number"]}},
]


# ---------------------------------------------------------------------------
# entrypoint: bind, register with the env, poll /done, exit 0
# ---------------------------------------------------------------------------

def _http_json(url, payload=None, timeout=5):
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(url, data=data, method="POST" if data else "GET",
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.status, json.loads(resp.read().decode("utf-8"))


class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    # socketserver's default listen backlog is 5: with 50 concurrent
    # clones the accept queue overflows and the kernel makes clients wait
    # out TCP retransmission timeouts (~1 s each). The clone workload
    # opens 50 connections at once; give it room.
    request_queue_size = 128
    allow_reuse_address = True


def main():
    server = ForgeServer(("0.0.0.0", 0), Handler)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    print("forge listening on port %d" % port, flush=True)
    if not ENV_URL:
        try:
            while True:
                time.sleep(3600)
        except KeyboardInterrupt:
            return 0
    registered = False
    deadline = time.time() + 120
    while not registered and time.time() < deadline:
        try:
            status, _ = _http_json(ENV_URL + "/register", {"port": port}, timeout=5)
            if status in (200, 409):
                registered = True
        except Exception:
            time.sleep(0.5)
    delay = 0.25
    while True:
        try:
            _status, data = _http_json(ENV_URL + "/done", timeout=30)
            if isinstance(data, dict) and data.get("done") is True:
                return 0
        except Exception:
            pass
        time.sleep(delay)
        delay = min(delay * 2, 2.0)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
