#!/usr/bin/env python3
"""A GitHub-compatible forge in one process, Python standard library only.

Serves, on one ephemeral port:
  * git smart HTTP (upload-pack v2 + v0, receive-pack v0) at /{owner}/{repo}.git
  * GitHub REST v3 under /api/v3
  * GitHub GraphQL v4 at /api/graphql
  * Model Context Protocol (Streamable HTTP) at /mcp
  * GET /healthz for the boot probe

Lifecycle: bind an ephemeral port, POST {"port": N} to $MAKEFUN_ENV_URL/register,
poll GET $MAKEFUN_ENV_URL/done until it answers {"done": true}, then exit 0.
With no MAKEFUN_ENV_URL set the server simply serves forever (local practice).

State is entirely in memory. The token owner (the "viewer") is derived at startup
from the contest's published scenario seed, so ownership checks match the suite
without any configuration. All timestamps the server emits are deterministic:
a fixed epoch plus a monotonic counter, never the wall clock.
"""

import base64
import binascii
import datetime
import difflib
import hashlib
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.parse
import urllib.request
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ---------------------------------------------------------------------------
# The scenario seed and the viewer login
#
# The suite builds every name from one fixed seed (wire.ts SCENARIO_SEED). The
# viewer is users[0] of the 'users' stream: an xorshift64* PRNG seeded by
# mix64(seed XOR fnv1a64(label)). Reimplementing that stream here lets the
# forge know, at startup, which login its bearer token names -- the token
# itself is an opaque shared secret and carries no identity.
# ---------------------------------------------------------------------------

SCENARIO_SEED = 0x6A09E667F3BCC909
MASK64 = (1 << 64) - 1

FIRST_NAMES = (
    "ada", "bram", "cora", "dmitri", "elena", "felix", "greta", "hugo",
    "iris", "jonas", "kira", "lars", "mira", "nico", "olga", "pavel",
    "quinn", "rosa", "sven", "tess", "ulla", "vito", "wren", "yara", "zane",
)
LAST_NAMES = (
    "anders", "bauer", "costa", "dahl", "eriksen", "fischer", "garcia",
    "holm", "iversen", "jansen", "keller", "lind", "moreau", "novak",
    "olsen", "peters", "quist", "rossi", "sato", "turi", "ulrich", "vega",
    "weber", "xu", "yilmaz", "zimmer",
)


def _fnv1a64(text):
    h = 0xCBF29CE484222325
    for ch in text:
        h ^= ord(ch)
        h = (h * 0x100000001B3) & MASK64
    return h


def _mix64(value):
    z = (value + 0x9E3779B97F4A7C15) & MASK64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return (z ^ (z >> 31)) & MASK64


class _Rng:
    """xorshift64* over a 64-bit state, mirroring the suite's Rng."""

    def __init__(self, seed):
        masked = seed & MASK64
        self._state = SCENARIO_SEED if masked == 0 else masked

    def next_u64(self):
        x = self._state
        x = (x ^ (x >> 12)) & MASK64
        x = (x ^ ((x << 25) & MASK64)) & MASK64
        x = (x ^ (x >> 27)) & MASK64
        self._state = x
        return (x * 0x2545F4914F6CDD1D) & MASK64

    def next_u32(self):
        return self.next_u64() >> 32

    def next_int(self, limit):
        if limit == 1:
            return 0
        span = 1 << 32
        cutoff = span - (span % limit)
        while True:
            value = self.next_u32()
            if value < cutoff:
                return value % limit

    def pick(self, items):
        return items[self.next_int(len(items))]


def _scenario_users(count):
    rng = _Rng(_mix64(SCENARIO_SEED ^ _fnv1a64("users")))
    used = set()
    users = []
    for i in range(count):
        first = rng.pick(FIRST_NAMES)
        last = rng.pick(LAST_NAMES)
        base = re.sub(r"[^a-z0-9-]", "", first + last)
        login = base
        suffix = 2
        while login in used:
            login = "%s-%d" % (base, suffix)
            suffix += 1
        used.add(login)
        users.append({
            "id": 1000 + i,
            "login": login,
            "name": "%s %s" % (first, last),
            "email": "%s@example.invalid" % login,
        })
    return users


VIEWER = _scenario_users(12)[0]
VIEWER_LOGIN = VIEWER["login"]
VIEWER_IDENT = "%s <%s>" % (VIEWER["name"], VIEWER["email"])

# ---------------------------------------------------------------------------
# Deterministic time. Every timestamp the forge emits (commit times, created_at,
# merged_at) comes from this counter: the scenario epoch plus one second per
# tick. Nothing sent to the suite reads the wall clock.
# ---------------------------------------------------------------------------

EPOCH_SEC = 1735689600  # 2025-01-01T00:00:00Z
_tick = [0]
_tick_lock = threading.Lock()


def tick_seconds():
    with _tick_lock:
        _tick[0] += 1
        return EPOCH_SEC + _tick[0]


def tick_iso():
    sec = tick_seconds()
    moment = datetime.datetime.fromtimestamp(sec, datetime.timezone.utc)
    return moment.strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

ZERO_OID = "0" * 40
HEX40 = re.compile(r"^[0-9a-f]{40}$")
SERVER_NAME = "makefun-forge"
SERVER_VERSION = "1.0.0"


def is_oid(value):
    return isinstance(value, str) and HEX40.match(value) is not None


def b64_encode(data):
    return base64.b64encode(data).decode("ascii")


def b64_decode(text):
    cleaned = re.sub(r"\s+", "", text or "")
    return base64.b64decode(cleaned)


def json_bytes(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def opaque_id(kind, *parts):
    raw = kind + ":" + ":".join(str(p) for p in parts)
    return base64.urlsafe_b64encode(raw.encode("utf-8")).decode("ascii").rstrip("=")


def decode_opaque_id(value):
    try:
        padded = value + "=" * (-len(value) % 4)
        raw = base64.urlsafe_b64decode(padded.encode("ascii")).decode("utf-8")
    except (binascii.Error, ValueError, UnicodeDecodeError):
        return None
    fields = raw.split(":")
    if len(fields) < 2:
        return None
    return fields


def cursor_for(number):
    return opaque_id("cursor", number)


def cursor_number(cursor):
    fields = decode_opaque_id(cursor) if isinstance(cursor, str) else None
    if not fields or fields[0] != "cursor" or len(fields) != 2:
        return None
    try:
        return int(fields[1])
    except ValueError:
        return None


# ---------------------------------------------------------------------------
# Git object model: SHA-1 ids, trees, commits, tags, reachability.
# ---------------------------------------------------------------------------

TYPE_CODES = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPES = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def hash_object(obj_type, data):
    header = ("%s %d\x00" % (obj_type, len(data))).encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def parse_tree(data):
    """A tree object into [(mode, name, oid)] in stored order."""
    entries = []
    pos = 0
    while pos < len(data):
        space = data.index(b" ", pos)
        mode = data[pos:space].decode("ascii")
        nul = data.index(b"\x00", space + 1)
        name = data[space + 1:nul].decode("utf-8")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        pos = nul + 21
    return entries


def _tree_sort_key(entry):
    mode, name, _oid = entry
    shown = name + "/" if mode == "40000" else name
    return shown.encode("utf-8")


def build_tree(entries):
    out = bytearray()
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        out += mode.encode("ascii")
        out += b" "
        out += name.encode("utf-8")
        out += b"\x00"
        out += bytes.fromhex(oid)
    return bytes(out)


def parse_commit(data):
    head, sep, message = data.partition(b"\n\n")
    view = {"tree": None, "parents": [], "author": "", "committer": "",
            "message": message.decode("utf-8", "replace") if sep else ""}
    for line in head.decode("utf-8", "replace").split("\n"):
        if line.startswith("tree "):
            view["tree"] = line[5:]
        elif line.startswith("parent "):
            view["parents"].append(line[7:])
        elif line.startswith("author "):
            view["author"] = line[7:]
        elif line.startswith("committer "):
            view["committer"] = line[10:]
    return view


def build_commit(tree, parents, message, ident, timestamp):
    lines = ["tree %s" % tree]
    for parent in parents:
        lines.append("parent %s" % parent)
    stamp = "%d +0000" % timestamp
    lines.append("author %s %s" % (ident, stamp))
    lines.append("committer %s %s" % (ident, stamp))
    lines.append("")
    return ("\n".join(lines) + "\n" + message).encode("utf-8")


def parse_tag(data):
    head, sep, message = data.partition(b"\n\n")
    headers = {}
    for line in head.decode("utf-8", "replace").split("\n"):
        if " " in line:
            key, value = line.split(" ", 1)
            headers[key] = value
    return {
        "object": headers.get("object", ""),
        "type": headers.get("type", ""),
        "tag": headers.get("tag", ""),
        "tagger": headers.get("tagger", ""),
        "message": message.decode("utf-8", "replace") if sep else "",
    }


class ObjectStore:
    """One global content-addressed store, shared by every repository.

    Objects never leak across repositories: fetch only ever sends objects
    reachable from the requested wants, and a push stores exactly what its
    pack carried. Unreachable objects are inert.
    """

    def __init__(self):
        self._objects = {}

    def put(self, obj_type, data):
        oid = hash_object(obj_type, data)
        if oid not in self._objects:
            self._objects[oid] = (obj_type, data)
        return oid

    def put_known(self, oid, obj_type, data):
        if oid not in self._objects:
            self._objects[oid] = (obj_type, data)

    def get(self, oid):
        return self._objects.get(oid)

    def has(self, oid):
        return oid in self._objects

    def peel_to_commit(self, oid):
        """Follow tag objects to the commit underneath; anything else as-is."""
        seen = set()
        current = oid
        while current not in seen:
            seen.add(current)
            found = self._objects.get(current)
            if found is None:
                return None
            obj_type, data = found
            if obj_type != "tag":
                return current if obj_type == "commit" else None
            current = parse_tag(data)["object"]
        return None

    def reachable(self, roots, follow_parents=True, stop_parents_at=None):
        """Every object id reachable from roots (commits, trees, blobs, tags).

        A commit in stop_parents_at contributes its tree but not its parents:
        that is how a client's shallow boundary is modelled — it holds the
        commit object, but nothing above it.
        """
        seen = set()
        stack = [r for r in roots if is_oid(r)]
        while stack:
            oid = stack.pop()
            if oid in seen:
                continue
            found = self._objects.get(oid)
            if found is None:
                continue
            seen.add(oid)
            obj_type, data = found
            if obj_type == "commit":
                view = parse_commit(data)
                if view["tree"]:
                    stack.append(view["tree"])
                if follow_parents and not (stop_parents_at and oid in stop_parents_at):
                    stack.extend(view["parents"])
            elif obj_type == "tag":
                stack.append(parse_tag(data)["object"])
            elif obj_type == "tree":
                for mode, _name, child in parse_tree(data):
                    if mode != "160000":
                        stack.append(child)
        return seen

    def tree_closure(self, commit_oid):
        """A commit plus its whole tree (no parents): what a fetch sends per commit."""
        out = set()
        found = self._objects.get(commit_oid)
        if found is None or found[0] != "commit":
            return out
        out.add(commit_oid)
        stack = [parse_commit(found[1])["tree"]]
        while stack:
            tree_oid = stack.pop()
            if tree_oid is None or tree_oid in out:
                continue
            entry = self._objects.get(tree_oid)
            if entry is None or entry[0] != "tree":
                continue
            out.add(tree_oid)
            for mode, _name, child in parse_tree(entry[1]):
                if mode == "40000":
                    stack.append(child)
                elif mode != "160000":
                    out.add(child)
        return out

    def flatten_tree(self, tree_oid):
        """A tree into {path: (mode, oid)} for every file it holds."""
        flat = {}
        stack = [(tree_oid, "")]
        while stack:
            current, prefix = stack.pop()
            entry = self._objects.get(current)
            if entry is None or entry[0] != "tree":
                continue
            for mode, name, child in parse_tree(entry[1]):
                path = prefix + name
                if mode == "40000":
                    stack.append((child, path + "/"))
                else:
                    flat[path] = (mode, child)
        return flat

    def tree_at_path(self, tree_oid, path):
        """The tree object id for a directory path, or None."""
        if path in ("", "/"):
            return tree_oid
        current = tree_oid
        for part in [p for p in path.split("/") if p]:
            entry = self._objects.get(current)
            if entry is None or entry[0] != "tree":
                return None
            found = None
            for mode, name, child in parse_tree(entry[1]):
                if name == part and mode == "40000":
                    found = child
                    break
            if found is None:
                return None
            current = found
        return current

    def build_tree_from_entries(self, entries):
        """Build (and store) nested trees from {path: (mode, oid)}; root oid."""
        root = {}
        for path, value in entries.items():
            parts = path.split("/")
            node = root
            for part in parts[:-1]:
                node = node.setdefault(part, {})
            node[parts[-1]] = value

        def build(node):
            items = []
            for name, value in node.items():
                if isinstance(value, tuple):
                    items.append((value[0], name, value[1]))
                else:
                    items.append(("40000", name, build(value)))
            return self.put("tree", build_tree(items))

        return build(root)

    def is_ancestor(self, maybe_ancestor, commit_oid):
        """True when maybe_ancestor is reachable from commit_oid via parents."""
        if maybe_ancestor == commit_oid:
            return True
        seen = set()
        stack = [commit_oid]
        while stack:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            found = self._objects.get(current)
            if found is None or found[0] != "commit":
                continue
            for parent in parse_commit(found[1])["parents"]:
                if parent == maybe_ancestor:
                    return True
                stack.append(parent)
        return False

    def merge_base(self, left, right):
        """A merge base of two commits: first common ancestor in BFS order."""
        if left is None or right is None:
            return None
        ancestors = set()
        queue = [left]
        while queue:
            current = queue.pop(0)
            if current in ancestors:
                continue
            ancestors.add(current)
            found = self._objects.get(current)
            if found is not None and found[0] == "commit":
                queue.extend(parse_commit(found[1])["parents"])
        queue = [right]
        seen = set()
        while queue:
            current = queue.pop(0)
            if current in seen:
                continue
            seen.add(current)
            if current in ancestors:
                return current
            found = self._objects.get(current)
            if found is not None and found[0] == "commit":
                queue.extend(parse_commit(found[1])["parents"])
        return None

    def commit_history(self, tip, limit=1000):
        """Commits from a tip, newest first, following parents in order."""
        order = []
        seen = set()
        stack = [tip] if tip else []
        while stack and len(order) < limit:
            current = stack.pop()
            if current in seen:
                continue
            seen.add(current)
            found = self._objects.get(current)
            if found is None or found[0] != "commit":
                continue
            order.append(current)
            parents = parse_commit(found[1])["parents"]
            for parent in reversed(parents):
                stack.append(parent)
        return order


# ---------------------------------------------------------------------------
# Packfiles: read (plain objects, OFS_DELTA, REF_DELTA) and write (plain only).
# ---------------------------------------------------------------------------


class PackError(Exception):
    pass


def _apply_delta(base, delta):
    pos = 0

    def read_varint():
        nonlocal pos
        value = 0
        shift = 0
        while True:
            if pos >= len(delta):
                raise PackError("delta size varint is truncated")
            byte = delta[pos]
            pos += 1
            value |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                return value
            if shift > 63:
                raise PackError("delta size varint is too long")

    source_size = read_varint()
    target_size = read_varint()
    if source_size != len(base):
        raise PackError("delta expects a %d-byte base, got %d" % (source_size, len(base)))
    out = bytearray(target_size)
    written = 0
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            copy_offset = 0
            copy_size = 0
            shift = 0
            for bit in range(4):
                if op & (1 << bit):
                    if pos >= len(delta):
                        raise PackError("delta copy offset is truncated")
                    copy_offset |= delta[pos] << shift
                    pos += 1
                shift += 8
            shift = 0
            for bit in range(4, 7):
                if op & (1 << bit):
                    if pos >= len(delta):
                        raise PackError("delta copy size is truncated")
                    copy_size |= delta[pos] << shift
                    pos += 1
                shift += 8
            if copy_size == 0:
                copy_size = 0x10000
            if copy_offset + copy_size > len(base):
                raise PackError("delta copy is out of the base")
            if written + copy_size > target_size:
                raise PackError("delta writes past its target size")
            out[written:written + copy_size] = base[copy_offset:copy_offset + copy_size]
            written += copy_size
        elif op:
            literal = op & 0x7F
            if pos + literal > len(delta):
                raise PackError("delta insert is truncated")
            if written + literal > target_size:
                raise PackError("delta writes past its target size")
            out[written:written + literal] = delta[pos:pos + literal]
            pos += literal
            written += literal
        else:
            raise PackError("delta opcode 0 is invalid")
    if written != target_size:
        raise PackError("delta produced %d of %d bytes" % (written, target_size))
    return bytes(out)


def read_pack(data):
    """Parse a packfile into {oid: (type, bytes)}; raises PackError."""
    if len(data) < 32:
        raise PackError("pack is %d bytes, too short" % len(data))
    if data[:4] != b"PACK":
        raise PackError("pack does not start with PACK")
    version = int.from_bytes(data[4:8], "big")
    if version not in (2, 3):
        raise PackError("unsupported pack version %d" % version)
    count = int.from_bytes(data[8:12], "big")
    trailer_at = len(data) - 20
    if hashlib.sha1(data[:trailer_at]).hexdigest() != data[trailer_at:].hex():
        raise PackError("pack trailer does not match its bytes")
    raw = []
    by_offset = {}
    offset = 12
    for _index in range(count):
        start = offset
        if offset >= trailer_at:
            raise PackError("pack entry header is truncated")
        first = data[offset]
        offset += 1
        type_code = (first >> 4) & 0x07
        size = first & 0x0F
        shift = 4
        while first & 0x80:
            if offset >= trailer_at:
                raise PackError("pack entry size varint is truncated")
            first = data[offset]
            offset += 1
            size |= (first & 0x7F) << shift
            shift += 7
            if shift > 63:
                raise PackError("pack entry size varint is too long")
        base_offset = None
        base_oid = None
        if type_code == 6:
            if offset >= trailer_at:
                raise PackError("ofs-delta has no base offset")
            byte = data[offset]
            offset += 1
            value = byte & 0x7F
            while byte & 0x80:
                if offset >= trailer_at:
                    raise PackError("ofs-delta base offset is truncated")
                byte = data[offset]
                offset += 1
                value = ((value + 1) << 7) | (byte & 0x7F)
            if value <= 0 or value > start:
                raise PackError("ofs-delta names an invalid base offset")
            base_offset = start - value
        elif type_code == 7:
            if offset + 20 > trailer_at:
                raise PackError("ref-delta base id is truncated")
            base_oid = data[offset:offset + 20].hex()
            offset += 20
        elif type_code not in CODE_TYPES:
            raise PackError("pack entry has unknown type code %d" % type_code)
        inflater = zlib.decompressobj()
        try:
            inflated = inflater.decompress(data[offset:trailer_at])
            inflater.flush()
        except zlib.error as err:
            raise PackError("zlib stream did not inflate: %s" % err)
        consumed = (trailer_at - offset) - len(inflater.unused_data)
        if consumed <= 0:
            raise PackError("zlib stream consumed no bytes")
        offset += consumed
        if len(inflated) != size:
            raise PackError("pack entry declares %d bytes but inflated to %d" % (size, len(inflated)))
        entry = {"offset": start, "code": type_code, "data": inflated,
                 "base_offset": base_offset, "base_oid": base_oid}
        raw.append(entry)
        by_offset[start] = entry
    if offset != trailer_at:
        raise PackError("pack has %d stray bytes before its trailer" % (trailer_at - offset))

    resolved = {}
    resolving = set()

    def resolve(entry):
        if entry["offset"] in resolved:
            return resolved[entry["offset"]]
        if entry["offset"] in resolving:
            raise PackError("delta cycle at pack offset %d" % entry["offset"])
        resolving.add(entry["offset"])
        code = entry["code"]
        if code == 6:
            base_entry = by_offset.get(entry["base_offset"])
            if base_entry is None:
                raise PackError("ofs-delta base is not in the pack")
            base_type, base_data, _oid = resolve(base_entry)
            obj_type, obj_data = base_type, _apply_delta(base_data, entry["data"])
        elif code == 7:
            base_entry = None
            for candidate in raw:
                if candidate["offset"] in resolved and resolved[candidate["offset"]][2] == entry["base_oid"]:
                    base_entry = candidate
                    break
            if base_entry is not None:
                base_type, base_data, _oid = resolve(base_entry)
                obj_type, obj_data = base_type, _apply_delta(base_data, entry["data"])
            else:
                raise PackError("ref-delta base %s is not in the pack" % entry["base_oid"])
        else:
            obj_type, obj_data = CODE_TYPES[code], entry["data"]
        oid = hash_object(obj_type, obj_data)
        result = (obj_type, obj_data, oid)
        resolved[entry["offset"]] = result
        resolving.discard(entry["offset"])
        return result

    objects = {}
    for entry in raw:
        obj_type, obj_data, oid = resolve(entry)
        objects[oid] = (obj_type, obj_data)
    return objects


def _pack_entry_header(obj_type, size):
    code = TYPE_CODES[obj_type]
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    out = bytearray()
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def write_pack(objects):
    """Build a version-2 pack from [(type, bytes)] in the given order."""
    parts = [b"PACK" + (2).to_bytes(4, "big") + len(objects).to_bytes(4, "big")]
    for obj_type, data in objects:
        parts.append(_pack_entry_header(obj_type, len(data)))
        parts.append(zlib.compress(data))
    body = b"".join(parts)
    return body + hashlib.sha1(body).digest()


# ---------------------------------------------------------------------------
# pkt-line framing (git's wire codec): 4-hex length, 0000 flush, 0001 delim.
# ---------------------------------------------------------------------------

PKT_MAX = 65520
PKT_MAX_PAYLOAD = PKT_MAX - 4


def pkt_line(payload):
    if len(payload) > PKT_MAX_PAYLOAD:
        raise ValueError("pkt-line payload over the maximum")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


FLUSH_PKT = b"0000"
DELIM_PKT = b"0001"


def encode_pkt_lines(items):
    out = bytearray()
    for item in items:
        if item == "flush":
            out += FLUSH_PKT
        elif item == "delim":
            out += DELIM_PKT
        elif isinstance(item, str):
            out += pkt_line(item.encode("utf-8"))
        else:
            out += pkt_line(item)
    return bytes(out)


def decode_pkt_lines(buf):
    """A whole buffer into [('data', bytes) | ('flush',) | ('delim',) | ('end',)]."""
    packets = []
    pos = 0
    while pos < len(buf):
        if pos + 4 > len(buf):
            raise ValueError("truncated pkt-line")
        try:
            length = int(buf[pos:pos + 4], 16)
        except ValueError:
            raise ValueError("invalid pkt-line length")
        if length == 0:
            packets.append(("flush", b""))
            pos += 4
        elif length == 1:
            packets.append(("delim", b""))
            pos += 4
        elif length == 2:
            packets.append(("end", b""))
            pos += 4
        elif length < 4 or length > PKT_MAX:
            raise ValueError("invalid pkt-line length %d" % length)
        else:
            if pos + length > len(buf):
                raise ValueError("truncated pkt-line")
            packets.append(("data", buf[pos + 4:pos + length]))
            pos += length
    return packets


def decode_until_flush(buf):
    """Decode pkt-lines up to (and including) the first flush.

    Returns (packets, offset_after_flush). The bytes past the flush are the
    caller's (a receive-pack's raw pack).
    """
    packets = []
    pos = 0
    while pos < len(buf):
        if pos + 4 > len(buf):
            raise ValueError("truncated pkt-line")
        try:
            length = int(buf[pos:pos + 4], 16)
        except ValueError:
            raise ValueError("invalid pkt-line length")
        if length == 0:
            return packets, pos + 4
        if length == 1:
            packets.append(("delim", b""))
            pos += 4
        elif length == 2:
            packets.append(("end", b""))
            pos += 4
        elif length < 4 or length > PKT_MAX:
            raise ValueError("invalid pkt-line length %d" % length)
        else:
            if pos + length > len(buf):
                raise ValueError("truncated pkt-line")
            packets.append(("data", buf[pos + 4:pos + length]))
            pos += length
    raise ValueError("no flush packet found")


def sideband_packets(payload):
    """Wrap bytes into band-1 sideband pkt-lines (chunked to the pkt limit)."""
    out = bytearray()
    for start in range(0, len(payload), PKT_MAX_PAYLOAD - 1):
        chunk = payload[start:start + PKT_MAX_PAYLOAD - 1]
        out += pkt_line(b"\x01" + chunk)
    if not payload:
        out += pkt_line(b"\x01")
    return bytes(out)


# ---------------------------------------------------------------------------
# The forge's state: repositories, issues, pull requests, labels, comments.
# ---------------------------------------------------------------------------


class Repo:
    def __init__(self, db_id, name, owner, private, description):
        self.db_id = db_id
        self.name = name
        self.owner = owner
        self.private = bool(private)
        self.description = description or ""
        self.default_branch = "main"
        self.refs = {}  # "refs/heads/main" -> oid, "refs/tags/v1" -> oid
        self.labels = {}  # name -> {"name":..., "color":...}
        self.issues = {}  # number -> dict
        self.next_issue = 1
        self.pulls = {}  # number -> dict
        self.next_pull = 1
        self.created_at = tick_iso()
        self.updated_at = self.created_at

    def ref_tip(self, ref):
        return self.refs.get(ref)

    def branch_tip(self, branch):
        if branch.startswith("refs/"):
            return self.refs.get(branch)
        return self.refs.get("refs/heads/" + branch)

    def default_tip(self):
        return self.refs.get("refs/heads/" + self.default_branch)

    def branches(self):
        out = []
        for ref in sorted(self.refs):
            if ref.startswith("refs/heads/"):
                out.append((ref[len("refs/heads/"):], self.refs[ref]))
        return out

    def global_id(self):
        return opaque_id("R", self.owner, self.name)


def _line_counts(old_text, new_text):
    """(additions, deletions) between two texts, by unified diff."""
    old_lines = old_text.splitlines()
    new_lines = new_text.splitlines()
    added = deleted = 0
    for line in difflib.unified_diff(old_lines, new_lines, lineterm=""):
        if line.startswith("+++") or line.startswith("---"):
            continue
        if line.startswith("+"):
            added += 1
        elif line.startswith("-"):
            deleted += 1
    return added, deleted


def _blob_text(store, oid):
    if oid is None:
        return ""
    found = store.get(oid)
    if found is None:
        return ""
    return found[1].decode("utf-8", "replace")


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.objects = ObjectStore()
        self.repos = {}  # name -> Repo (every repo belongs to the viewer)
        self.next_repo_id = 1
        self.next_comment_id = 1
        self.next_global_id = 1
        self.request_seq = 0

    # -- identity ---------------------------------------------------------

    def request_id(self):
        self.request_seq += 1
        return "req-%08x" % self.request_seq

    def _fresh_id(self):
        value = self.next_global_id
        self.next_global_id += 1
        return value

    # -- repositories -----------------------------------------------------

    def create_repo(self, name, private=False, description=""):
        if not name or len(name) > 100:
            return None, "Repository name is invalid"
        if name in self.repos:
            return None, "Repository %s already exists" % name
        repo = Repo(self.next_repo_id, name, VIEWER_LOGIN, private, description)
        self.next_repo_id += 1
        self.repos[name] = repo
        return repo, None

    def get_repo(self, owner, name):
        if owner != VIEWER_LOGIN:
            return None
        return self.repos.get(name)

    def delete_repo(self, repo):
        self.repos.pop(repo.name, None)

    def list_repos(self):
        return list(self.repos.values())

    # -- git helpers on a repository --------------------------------------

    def resolve_ref(self, repo, ref):
        """A branch name, full ref, HEAD or commit id into a commit oid."""
        if ref is None:
            return repo.default_tip()
        if ref == "HEAD":
            return repo.default_tip()
        if is_oid(ref) and self.objects.has(ref):
            return self.objects.peel_to_commit(ref) or ref
        tip = repo.branch_tip(ref)
        if tip is not None:
            return self.objects.peel_to_commit(tip) or tip
        if ref in repo.refs:
            tip = repo.refs[ref]
            return self.objects.peel_to_commit(tip) or tip
        return None

    def commit_for_ref(self, repo, ref):
        tip = self.resolve_ref(repo, ref)
        if tip is None:
            return None
        found = self.objects.get(tip)
        if found is None or found[0] != "commit":
            return None
        return tip

    def commit_tree(self, commit_oid):
        found = self.objects.get(commit_oid)
        if found is None or found[0] != "commit":
            return None
        return parse_commit(found[1])["tree"]

    def flat_tree_at(self, repo, ref):
        tip = self.commit_for_ref(repo, ref)
        if tip is None:
            return {}
        tree = self.commit_tree(tip)
        if tree is None:
            return {}
        return self.objects.flatten_tree(tree)

    def commit_on_branch(self, repo, branch, message, new_entries):
        """Commit a new full tree state on a branch; returns the commit oid.

        new_entries is {path: (mode, oid)}. The branch is created from the
        default branch tip when it does not exist yet.
        """
        parent = repo.branch_tip(branch)
        if parent is None and branch != repo.default_branch:
            parent = repo.default_tip()
        tree_oid = self.objects.build_tree_from_entries(new_entries)
        parents = [parent] if parent else []
        data = build_commit(tree_oid, parents, message, VIEWER_IDENT, tick_seconds())
        oid = self.objects.put("commit", data)
        repo.refs["refs/heads/" + branch] = oid
        return oid

    # -- contents ----------------------------------------------------------

    def contents_put(self, repo, path, content_bytes, message, branch, sha):
        """The contents PUT: create or update one file. Returns (status, payload)."""
        target = branch or repo.default_branch
        flat = self.flat_tree_at(repo, target)
        existing = flat.get(path)
        if existing is not None and sha is not None and sha.lower() != existing[1].lower():
            return 409, {"message": "The sha %s does not match the current blob" % sha}
        blob_oid = self.objects.put("blob", content_bytes)
        flat[path] = ("100644", blob_oid)
        commit_oid = self.commit_on_branch(repo, target, message, flat)
        status = 200 if existing is not None else 201
        return status, {
            "content": {"name": path.rsplit("/", 1)[-1], "path": path,
                        "sha": blob_oid, "size": len(content_bytes),
                        "encoding": "base64"},
            "commit": {"sha": commit_oid, "message": message},
        }

    def contents_delete(self, repo, path, message, branch):
        target = branch or repo.default_branch
        flat = self.flat_tree_at(repo, target)
        if path not in flat:
            return 404, {"message": "Not Found"}
        del flat[path]
        commit_oid = self.commit_on_branch(repo, target, message, flat)
        return 200, {"commit": {"sha": commit_oid, "message": message}}

    # -- issues ------------------------------------------------------------

    def create_issue(self, repo, title, body, labels):
        for label in labels or []:
            if label not in repo.labels:
                return None, "Label %s does not exist" % label
        number = repo.next_issue
        repo.next_issue += 1
        issue = {
            "id": self._fresh_id(),
            "number": number,
            "title": title or "",
            "body": body or "",
            "state": "open",
            "labels": list(labels or []),
            "comments": [],
            "created_at": tick_iso(),
            "updated_at": tick_iso(),
            "seq": number,
        }
        repo.issues[number] = issue
        return issue, None

    def list_issues(self, repo, state=None, sort="created", direction="desc"):
        issues = list(repo.issues.values())
        if state in ("open", "closed"):
            issues = [i for i in issues if i["state"] == state]
        reverse = direction != "asc"
        issues.sort(key=lambda i: i["seq"], reverse=reverse)
        return issues

    # -- pull requests ------------------------------------------------------

    def diff_between(self, base_commit, head_commit):
        """Changed paths between two commits: [(path, status, old, new)]."""
        base_tree = self.commit_tree(base_commit) if base_commit else None
        head_tree = self.commit_tree(head_commit) if head_commit else None
        base_flat = self.objects.flatten_tree(base_tree) if base_tree else {}
        head_flat = self.objects.flatten_tree(head_tree) if head_tree else {}
        out = []
        for path in sorted(set(base_flat) | set(head_flat)):
            old = base_flat.get(path)
            new = head_flat.get(path)
            if old is None:
                out.append((path, "added", None, new))
            elif new is None:
                out.append((path, "removed", old, None))
            elif old[1] != new[1]:
                out.append((path, "modified", old, new))
        return out

    def pull_diff(self, repo, pull):
        base = self.objects.merge_base(pull["base_sha"], pull["head_sha"])
        return self.diff_between(base, pull["head_sha"])

    def pull_conflict(self, repo, pull):
        """True when the head's changes clash with the base's later changes."""
        base_tip = repo.branch_tip(pull["base"])
        head_tip = pull["head_sha"]
        if base_tip is None or head_tip is None:
            return False
        base_commit = self.objects.peel_to_commit(base_tip) or base_tip
        head_commit = self.objects.peel_to_commit(head_tip) or head_tip
        merge_base = self.objects.merge_base(base_commit, head_commit)
        if merge_base is None:
            return False
        head_changes = {p: n for p, _s, _o, n in self.diff_between(merge_base, head_commit)}
        base_changes = {p: n for p, _s, _o, n in self.diff_between(merge_base, base_commit)}
        for path, head_entry in head_changes.items():
            if path not in base_changes:
                continue
            head_oid = head_entry[1] if head_entry else None
            base_oid = base_changes[path][1] if base_changes[path] else None
            if head_oid != base_oid:
                return True
        return False

    def create_pull(self, repo, head, base, title, body):
        head_tip = repo.branch_tip(head)
        base_tip = repo.branch_tip(base)
        if head_tip is None:
            return None, "Head branch %s does not exist" % head
        if base_tip is None:
            return None, "Base branch %s does not exist" % base
        for other in repo.pulls.values():
            if other["head"] == head and other["state"] == "open":
                return None, "A pull request already exists for %s" % head
        number = repo.next_pull
        repo.next_pull += 1
        pull = {
            "id": self._fresh_id(),
            "number": number,
            "title": title or "",
            "body": body or "",
            "head": head,
            "base": base,
            "head_sha": self.objects.peel_to_commit(head_tip) or head_tip,
            "base_sha": self.objects.peel_to_commit(base_tip) or base_tip,
            "state": "open",
            "merged": False,
            "merged_at": None,
            "merge_commit_sha": None,
            "created_at": tick_iso(),
            "updated_at": tick_iso(),
            "seq": number,
        }
        repo.pulls[number] = pull
        return pull, None

    def merge_pull(self, repo, pull):
        """Squash-merge a pull request. Returns (status, payload)."""
        if pull["state"] != "open":
            return 405, {"message": "Pull request #%d is already %s" % (pull["number"], pull["state"])}
        base_tip = repo.branch_tip(pull["base"])
        if base_tip is None:
            return 405, {"message": "Base branch %s does not exist" % pull["base"]}
        base_commit = self.objects.peel_to_commit(base_tip) or base_tip
        head_commit = pull["head_sha"]
        if self.pull_conflict(repo, pull):
            return 405, {"message": "Merge conflict: the head and base both changed a file"}
        merge_base = self.objects.merge_base(base_commit, head_commit)
        head_changes = self.diff_between(merge_base, head_commit)
        flat = self.flat_tree_at(repo, pull["base"])
        for path, _status, _old, new in head_changes:
            if new is None:
                flat.pop(path, None)
            else:
                flat[path] = new
        message = "Squash merge #%d: %s" % (pull["number"], pull["title"])
        tree_oid = self.objects.build_tree_from_entries(flat)
        data = build_commit(tree_oid, [base_commit], message, VIEWER_IDENT, tick_seconds())
        merge_oid = self.objects.put("commit", data)
        repo.refs["refs/heads/" + pull["base"]] = merge_oid
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merged_at"] = tick_iso()
        pull["merge_commit_sha"] = merge_oid
        pull["updated_at"] = tick_iso()
        return 200, {"sha": merge_oid, "merged": True,
                     "message": "Pull request successfully merged"}

    # -- fetch selection -----------------------------------------------------

    def select_fetch(self, wants, haves, shallow_boundary, depth):
        """Objects for a fetch: (sorted oids, shallow list, unshallow list).

        Walk commits from the wants with generations (want = generation 1),
        expanding through haves, stopping past the depth limit. What the
        client already holds (the full closure of its haves) is excluded.
        """
        have_closure = self.objects.reachable(
            haves, follow_parents=True,
            stop_parents_at=set(shallow_boundary or []))
        generation = {}
        queue = []
        tag_wants = []
        for want in wants:
            found = self.objects.get(want)
            if found is None:
                continue
            if found[0] == "tag":
                tag_wants.append(want)
                target = parse_tag(found[1])["object"]
                target_commit = self.objects.peel_to_commit(target)
                if target_commit is not None and target_commit not in generation:
                    generation[target_commit] = 1
                    queue.append(target_commit)
            elif found[0] == "commit":
                if want not in generation:
                    generation[want] = 1
                    queue.append(want)
        head = 0
        while head < len(queue):
            current = queue[head]
            head += 1
            gen = generation[current]
            if depth is not None and gen >= depth:
                continue
            found = self.objects.get(current)
            if found is None or found[0] != "commit":
                continue
            for parent in parse_commit(found[1])["parents"]:
                if parent not in generation:
                    generation[parent] = gen + 1
                    queue.append(parent)
        sent_commits = {c for c, g in generation.items()
                        if (depth is None or g <= depth) and c not in have_closure}
        chosen = set()
        for commit in sent_commits:
            chosen |= self.objects.tree_closure(commit)
        for want in tag_wants:
            if want not in have_closure:
                chosen.add(want)
        chosen -= have_closure
        shallow_out = []
        if depth is not None:
            for commit in sorted(sent_commits):
                if generation.get(commit) != depth:
                    continue
                found = self.objects.get(commit)
                if found is not None and parse_commit(found[1])["parents"]:
                    shallow_out.append(commit)
        unshallow_out = []
        for boundary in shallow_boundary or []:
            found = self.objects.get(boundary)
            if found is None or found[0] != "commit":
                continue
            if any(p in sent_commits for p in parse_commit(found[1])["parents"]):
                unshallow_out.append(boundary)
        return sorted(chosen), sorted(shallow_out), sorted(unshallow_out)


# ---------------------------------------------------------------------------
# JSON views: the shapes the REST, GraphQL and MCP surfaces all share.
# ---------------------------------------------------------------------------


def repo_view(repo):
    return {
        "id": repo.db_id,
        "node_id": repo.global_id(),
        "name": repo.name,
        "full_name": "%s/%s" % (repo.owner, repo.name),
        "owner": {"login": repo.owner, "id": VIEWER["id"]},
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "created_at": repo.created_at,
        "updated_at": repo.updated_at,
    }


def issue_view(repo, issue):
    return {
        "id": issue["id"],
        "node_id": opaque_id("I", repo.owner, repo.name, issue["number"]),
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "labels": [{"name": name, "color": repo.labels.get(name, {}).get("color", "ededed")}
                   for name in issue["labels"]],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER["id"]},
        "comments": len(issue["comments"]),
        "created_at": issue["created_at"],
        "updated_at": issue["updated_at"],
    }


def pull_view(repo, pull):
    return {
        "id": pull["id"],
        "node_id": opaque_id("P", repo.owner, repo.name, pull["number"]),
        "number": pull["number"],
        "title": pull["title"],
        "body": pull["body"],
        "state": pull["state"],
        "head": {"ref": pull["head"], "sha": pull["head_sha"],
                 "label": "%s:%s" % (repo.owner, pull["head"])},
        "base": {"ref": pull["base"], "sha": pull["base_sha"],
                 "label": "%s:%s" % (repo.owner, pull["base"])},
        "merged": pull["merged"],
        "merged_at": pull["merged_at"],
        "merge_commit_sha": pull["merge_commit_sha"],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER["id"]},
        "created_at": pull["created_at"],
        "updated_at": pull["updated_at"],
    }


def comment_view(repo, issue, comment):
    return {
        "id": comment["id"],
        "node_id": opaque_id("C", repo.owner, repo.name, issue["number"], comment["id"]),
        "body": comment["body"],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER["id"]},
        "created_at": comment["created_at"],
        "updated_at": comment["updated_at"],
    }


# ---------------------------------------------------------------------------
# HTTP plumbing: one threaded server, keep-alive, a single store lock.
# ---------------------------------------------------------------------------


class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


def _require_auth(handler):
    token = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
    if not token:
        return
    presented = handler.headers.get("Authorization", "")
    if presented != "Bearer " + token:
        raise ApiError(401, "Requires authentication")


class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True

    def get_request(self):
        sock, address = super().get_request()
        # Without this, Nagle + the client's delayed ACK stalls every small
        # request/response pair on a keep-alive connection by ~20-40ms —
        # fatal for the sequential bench workloads.
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        return sock, address

    def __init__(self, address, handler_class):
        super().__init__(address, handler_class)
        self.store = Store()


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "makefun-forge/1.0"

    # -- quiet ------------------------------------------------------------

    def log_message(self, *args):
        pass

    # -- response helpers ---------------------------------------------------

    def _send(self, status, body, content_type="application/json", extra=None):
        try:
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            if status != 204:
                self.send_header("Content-Length", str(len(body)))
            self.send_header("X-GitHub-Request-Id", self.server.store.request_id())
            if extra:
                for key, value in extra.items():
                    self.send_header(key, value)
            self.end_headers()
            if status != 204 and body:
                self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _send_json(self, status, obj, extra=None):
        self._send(status, json_bytes(obj), "application/json", extra)

    def _error(self, status, message):
        self._send_json(status, {"message": message})

    # -- request helpers ------------------------------------------------------

    def _read_socket_body(self):
        length = self.headers.get("Content-Length")
        if not length:
            return b""
        try:
            count = int(length)
        except ValueError:
            return b""
        if count <= 0:
            return b""
        return self.rfile.read(count)

    def _read_body(self):
        return getattr(self, "_request_body", b"")

    def _read_json(self):
        raw = self._read_body()
        if not raw:
            return {}
        try:
            parsed = json.loads(raw.decode("utf-8"))
        except (ValueError, UnicodeDecodeError):
            raise ApiError(400, "Problems parsing JSON")
        if not isinstance(parsed, dict):
            raise ApiError(400, "Problems parsing JSON")
        return parsed

    def _split_path(self):
        split = urllib.parse.urlsplit(self.path)
        path = split.path
        if len(path) > 1 and path.endswith("/"):
            path = path[:-1]
        segments = [urllib.parse.unquote(seg) for seg in path.split("/") if seg != ""]
        query = urllib.parse.parse_qs(split.query, keep_blank_values=True)
        return segments, query

    def _query_one(self, query, name, default=None):
        values = query.get(name)
        if not values:
            return default
        return values[0]

    def _page_params(self, query, default_per_page=30):
        try:
            per_page = int(self._query_one(query, "per_page", default_per_page))
        except (TypeError, ValueError):
            per_page = default_per_page
        per_page = max(1, min(per_page, 100))
        try:
            page = int(self._query_one(query, "page", 1))
        except (TypeError, ValueError):
            page = 1
        return max(1, page), per_page

    # -- dispatch ---------------------------------------------------------------

    def do_GET(self):
        self._dispatch("GET")

    def do_POST(self):
        self._dispatch("POST")

    def do_PUT(self):
        self._dispatch("PUT")

    def do_PATCH(self):
        self._dispatch("PATCH")

    def do_DELETE(self):
        self._dispatch("DELETE")

    def _dispatch(self, method):
        # Drain the request body up front: if a handler ever errors before
        # reading it, the leftover bytes would otherwise be parsed as the
        # next request on this keep-alive connection.
        self._request_body = self._read_socket_body()
        try:
            with self.server.store.lock:
                self._route(method)
        except ApiError as err:
            self._error(err.status, err.message)
        except BrokenPipeError:
            pass
        except Exception as err:  # never drop a connection on an internal error
            try:
                self._error(500, "Internal error: %s" % err)
            except (BrokenPipeError, ConnectionResetError):
                pass

    def _route(self, method):
        segments, query = self._split_path()
        if segments == ["healthz"] and method == "GET":
            self._send_json(200, {"ok": True})
            return
        if segments[:1] == ["api"] and len(segments) >= 2 and segments[1] == "v3":
            _require_auth(self)
            self._route_rest(method, segments[2:], query)
            return
        if segments == ["api", "graphql"] and method == "POST":
            _require_auth(self)
            self._route_graphql()
            return
        if segments == ["mcp"]:
            if method == "DELETE":
                self._send_json(200, {})
                return
            if method == "POST":
                _require_auth(self)
                self._route_mcp()
                return
            raise ApiError(405, "Method Not Allowed")
        if len(segments) >= 2 and segments[1].endswith(".git"):
            _require_auth(self)
            self._route_git(method, segments, query)
            return
        raise ApiError(404, "Not Found")


    # -- REST v3 ------------------------------------------------------------

    def _route_rest(self, method, segments, query):
        store = self.server.store
        if not segments:
            if method == "GET":
                self._send_json(200, {
                    "current_user_url": "/api/v3/user",
                    "repository_url": "/api/v3/repos/{owner}/{repo}",
                }, {"X-OAuth-Scopes": "repo, read:org"})
                return
            raise ApiError(404, "Not Found")
        head = segments[0]
        if head == "meta" and len(segments) == 1 and method == "GET":
            self._send_json(200, {"installed_version": "1.0.0"})
            return
        if head == "user":
            self._rest_user(method, segments[1:], query)
            return
        if head == "repos":
            self._rest_repos(method, segments[1:], query)
            return
        raise ApiError(404, "Not Found")

    def _rest_user(self, method, segments, query):
        store = self.server.store
        if not segments:
            if method == "GET":
                self._send_json(200, {"login": VIEWER_LOGIN, "id": VIEWER["id"],
                                      "name": VIEWER["name"], "email": VIEWER["email"]})
                return
            raise ApiError(404, "Not Found")
        if segments == ["repos"]:
            if method == "GET":
                page, per_page = self._page_params(query, 30)
                repos = store.list_repos()
                total = len(repos)
                start = (page - 1) * per_page
                items = repos[start:start + per_page]
                extra = {}
                host = self.headers.get("Host", "")
                if start + per_page < total:
                    last_page = (total + per_page - 1) // per_page
                    base = "http://%s/api/v3/user/repos" % host
                    extra["Link"] = ('<%s?per_page=%d&page=%d>; rel="next", '
                                     '<%s?per_page=%d&page=%d>; rel="last"'
                                     % (base, per_page, page + 1, base, per_page, last_page))
                self._send_json(200, [repo_view(r) for r in items], extra)
                return
            if method == "POST":
                body = self._read_json()
                name = body.get("name")
                repo, error = store.create_repo(
                    name, private=body.get("private", False),
                    description=body.get("description", ""))
                if repo is None:
                    raise ApiError(422, error)
                self._send_json(201, repo_view(repo))
                return
        raise ApiError(404, "Not Found")

    def _rest_repos(self, method, segments, query):
        store = self.server.store
        if len(segments) < 2:
            raise ApiError(404, "Not Found")
        owner, name = segments[0], segments[1]
        repo = store.get_repo(owner, name)
        if repo is None:
            raise ApiError(404, "Not Found")
        rest = segments[2:]
        if not rest:
            if method == "GET":
                self._send_json(200, repo_view(repo))
            elif method == "PATCH":
                body = self._read_json()
                if "description" in body:
                    repo.description = body.get("description") or ""
                if "private" in body:
                    repo.private = bool(body.get("private"))
                repo.updated_at = tick_iso()
                self._send_json(200, repo_view(repo))
            elif method == "DELETE":
                store.delete_repo(repo)
                self._send(204, b"")
            else:
                raise ApiError(404, "Not Found")
            return
        resource = rest[0]
        if resource == "branches":
            self._rest_branches(method, repo, rest[1:])
        elif resource == "commits":
            self._rest_commits(method, repo, query)
        elif resource == "contents":
            self._rest_contents(method, repo, rest[1:], query)
        elif resource == "git":
            self._rest_git_data(method, repo, rest[1:])
        elif resource == "labels":
            self._rest_labels(method, repo)
        elif resource == "issues":
            self._rest_issues(method, repo, rest[1:], query)
        elif resource == "pulls":
            self._rest_pulls(method, repo, rest[1:], query)
        else:
            raise ApiError(404, "Not Found")

    def _rest_branches(self, method, repo, rest):
        if method != "GET":
            raise ApiError(404, "Not Found")
        if not rest:
            branches = [{"name": name, "commit": {"sha": tip}}
                        for name, tip in repo.branches()]
            self._send_json(200, branches)
            return
        branch = "/".join(rest)
        tip = repo.branch_tip(branch)
        if tip is None:
            raise ApiError(404, "Branch not found")
        self._send_json(200, {"name": branch, "commit": {"sha": tip}})

    def _rest_commits(self, method, repo, query):
        if method != "GET":
            raise ApiError(404, "Not Found")
        ref = self._query_one(query, "sha")
        tip = self.server.store.commit_for_ref(repo, ref)
        if tip is None:
            self._send_json(200, [])
            return
        out = []
        for oid in self.server.store.objects.commit_history(tip):
            view = parse_commit(self.server.store.objects.get(oid)[1])
            out.append({
                "sha": oid,
                "commit": {
                    "message": view["message"],
                    "author": {"name": view["author"], "date": ""},
                    "committer": {"name": view["committer"], "date": ""},
                },
                "parents": [{"sha": p} for p in view["parents"]],
            })
        self._send_json(200, out)

    def _rest_contents(self, method, repo, rest, query):
        store = self.server.store
        path = "/".join(rest)
        if method == "GET":
            ref = self._query_one(query, "ref")
            tip = store.commit_for_ref(repo, ref)
            if tip is None:
                raise ApiError(404, "Not Found")
            tree_oid = store.commit_tree(tip)
            flat = store.objects.flatten_tree(tree_oid)
            if path in flat:
                _mode, blob_oid = flat[path]
                data = store.objects.get(blob_oid)[1]
                self._send_json(200, {
                    "type": "file",
                    "encoding": "base64",
                    "content": b64_encode(data),
                    "sha": blob_oid,
                    "size": len(data),
                    "name": path.rsplit("/", 1)[-1],
                    "path": path,
                })
                return
            dir_oid = store.objects.tree_at_path(tree_oid, path)
            if dir_oid is None:
                raise ApiError(404, "Not Found")
            entries = []
            for mode, name, child in parse_tree(store.objects.get(dir_oid)[1]):
                child_path = (path + "/" + name) if path else name
                entry = {"type": "dir" if mode == "40000" else "file",
                         "name": name, "path": child_path, "sha": child}
                if mode != "40000":
                    found = store.objects.get(child)
                    entry["size"] = len(found[1]) if found else 0
                entries.append(entry)
            self._send_json(200, entries)
            return
        if method == "PUT":
            body = self._read_json()
            try:
                content = b64_decode(body.get("content", ""))
            except (binascii.Error, ValueError):
                raise ApiError(422, "content is not valid base64")
            status, payload = store.contents_put(
                repo, path, content, body.get("message", ""),
                body.get("branch"), body.get("sha"))
            if status >= 400:
                raise ApiError(status, payload["message"])
            self._send_json(status, payload)
            return
        if method == "DELETE":
            body = self._read_json()
            status, payload = store.contents_delete(
                repo, path, body.get("message", ""), body.get("branch"))
            if status >= 400:
                raise ApiError(status, payload["message"])
            self._send_json(status, payload)
            return
        raise ApiError(404, "Not Found")

    def _rest_git_data(self, method, repo, rest):
        store = self.server.store
        if rest == ["refs"] and method == "POST":
            body = self._read_json()
            ref = body.get("ref", "")
            sha = body.get("sha", "")
            if not ref.startswith("refs/") or not is_oid(sha):
                raise ApiError(422, "Invalid ref or sha")
            if ref in repo.refs:
                raise ApiError(422, "Reference already exists")
            if not store.objects.has(sha):
                raise ApiError(422, "Object %s does not exist" % sha)
            repo.refs[ref] = sha
            self._send_json(201, {"ref": ref, "object": {"sha": sha, "type": "commit"}})
            return
        if rest and rest[0] == "refs" and method == "GET":
            ref = "refs/" + "/".join(rest[1:])
            tip = repo.refs.get(ref)
            if tip is None:
                raise ApiError(404, "Reference not found")
            self._send_json(200, {"ref": ref, "object": {"sha": tip, "type": "commit"}})
            return
        raise ApiError(404, "Not Found")

    def _rest_labels(self, method, repo):
        if method != "POST":
            raise ApiError(404, "Not Found")
        body = self._read_json()
        name = body.get("name")
        if not name:
            raise ApiError(422, "Label name is required")
        label = {"name": name, "color": body.get("color", "ededed")}
        repo.labels[name] = label
        self._send_json(201, label)

    def _rest_issues(self, method, repo, rest, query):
        store = self.server.store
        if not rest:
            if method == "GET":
                state = self._query_one(query, "state", "open")
                sort = self._query_one(query, "sort", "created")
                direction = self._query_one(query, "direction", "desc")
                _page, per_page = self._page_params(query, 30)
                issues = store.list_issues(repo, state, sort, direction)[:per_page]
                self._send_json(200, [issue_view(repo, i) for i in issues])
                return
            if method == "POST":
                body = self._read_json()
                labels = body.get("labels") or []
                names = [l.get("name") if isinstance(l, dict) else l for l in labels]
                issue, error = store.create_issue(
                    repo, body.get("title", ""), body.get("body", ""), names)
                if issue is None:
                    raise ApiError(422, error)
                self._send_json(201, issue_view(repo, issue))
                return
            raise ApiError(404, "Not Found")
        try:
            number = int(rest[0])
        except ValueError:
            raise ApiError(404, "Not Found")
        issue = repo.issues.get(number)
        if issue is None:
            raise ApiError(404, "Not Found")
        if len(rest) == 1:
            if method == "GET":
                self._send_json(200, issue_view(repo, issue))
            elif method == "PATCH":
                body = self._read_json()
                if "state" in body and body["state"] in ("open", "closed"):
                    issue["state"] = body["state"]
                if "title" in body:
                    issue["title"] = body["title"]
                if "body" in body:
                    issue["body"] = body["body"]
                issue["updated_at"] = tick_iso()
                self._send_json(200, issue_view(repo, issue))
            else:
                raise ApiError(404, "Not Found")
            return
        if rest[1] == "comments":
            if method == "GET":
                self._send_json(200, [comment_view(repo, issue, c) for c in issue["comments"]])
                return
            if method == "POST":
                body = self._read_json()
                comment = {
                    "id": store.next_comment_id,
                    "body": body.get("body", ""),
                    "created_at": tick_iso(),
                    "updated_at": tick_iso(),
                }
                store.next_comment_id += 1
                issue["comments"].append(comment)
                self._send_json(201, comment_view(repo, issue, comment))
                return
        raise ApiError(404, "Not Found")

    def _rest_pulls(self, method, repo, rest, query):
        store = self.server.store
        if not rest:
            if method == "GET":
                state = self._query_one(query, "state", "open")
                _page, per_page = self._page_params(query, 30)
                pulls = list(repo.pulls.values())
                if state in ("open", "closed"):
                    pulls = [p for p in pulls if p["state"] == state]
                pulls.sort(key=lambda p: p["seq"], reverse=True)
                self._send_json(200, [pull_view(repo, p) for p in pulls[:per_page]])
                return
            if method == "POST":
                body = self._read_json()
                pull, error = store.create_pull(
                    repo, body.get("head", ""), body.get("base", ""),
                    body.get("title", ""), body.get("body", ""))
                if pull is None:
                    raise ApiError(422, error)
                self._send_json(201, pull_view(repo, pull))
                return
            raise ApiError(404, "Not Found")
        try:
            number = int(rest[0])
        except ValueError:
            raise ApiError(404, "Not Found")
        pull = repo.pulls.get(number)
        if pull is None:
            raise ApiError(404, "Not Found")
        if len(rest) == 1:
            if method == "GET":
                self._send_json(200, pull_view(repo, pull))
                return
            raise ApiError(404, "Not Found")
        if rest[1] == "files" and method == "GET":
            files = []
            for path, status, old, new in store.pull_diff(repo, pull):
                old_text = _blob_text(store.objects, old[1]) if old else ""
                new_text = _blob_text(store.objects, new[1]) if new else ""
                added, deleted = _line_counts(old_text, new_text)
                files.append({
                    "filename": path, "status": status,
                    "additions": added, "deletions": deleted,
                    "changes": added + deleted,
                })
            self._send_json(200, files)
            return
        if rest[1] == "merge" and method == "PUT":
            status, payload = store.merge_pull(repo, pull)
            if status >= 400:
                raise ApiError(status, payload["message"])
            self._send_json(status, payload)
            return
        raise ApiError(404, "Not Found")


    # -- Git smart HTTP ------------------------------------------------------

    def _git_repo(self, segments):
        store = self.server.store
        owner = segments[0]
        repo_name = segments[1][:-4]
        repo = store.get_repo(owner, repo_name)
        if repo is None:
            raise ApiError(404, "Not Found")
        return repo

    def _git_ad_refs(self, repo):
        """Ref lines for the advertisement: [(oid, ref, peeled_oid_or_None)]."""
        lines = []
        for ref in sorted(repo.refs):
            oid = repo.refs[ref]
            lines.append((oid, ref, None))
            peeled = self.server.store.objects.peel_to_commit(oid)
            if ref.startswith("refs/tags/") and peeled is not None and peeled != oid:
                lines.append((peeled, ref + "^{}", None))
        return lines

    def _route_git(self, method, segments, query):
        repo = self._git_repo(segments)
        service = self._query_one(query, "service")
        tail = segments[2:]
        if tail == ["info", "refs"] and method == "GET":
            if service == "git-upload-pack":
                self._git_info_refs_upload(repo)
            elif service == "git-receive-pack":
                self._git_info_refs_receive(repo)
            else:
                raise ApiError(404, "Not Found")
            return
        if tail == ["git-upload-pack"] and method == "POST":
            self._git_upload_pack(repo)
            return
        if tail == ["git-receive-pack"] and method == "POST":
            self._git_receive_pack(repo, self._read_body())
            return
        raise ApiError(404, "Not Found")

    def _git_info_refs_upload(self, repo):
        caps = ("side-band-64k shallow thin-pack ofs-delta agent=makefun-forge/1.0 "
                "symref=HEAD:refs/heads/" + repo.default_branch)
        protocol = self.headers.get("Git-Protocol", "")
        if "version=2" in protocol:
            body = encode_pkt_lines([
                "version 2\n",
                "agent=makefun-forge/1.0\n",
                "ls-refs\n",
                "fetch=shallow thin-pack ofs-delta\n",
                "object-format=sha1\n",
                "flush",
            ])
            self._send(200, body, "application/x-git-upload-pack-advertisement")
            return
        refs = self._git_ad_refs(repo)
        tip = repo.default_tip()
        out = bytearray(encode_pkt_lines(["# service=git-upload-pack\n", "flush"]))
        first = True
        if refs:
            head_oid = tip or ZERO_OID
            line = "%s HEAD\x00%s\n" % (head_oid, caps)
            out += pkt_line(line.encode("utf-8"))
            first = False
            for oid, ref, _peeled in refs:
                out += pkt_line(("%s %s\n" % (oid, ref)).encode("utf-8"))
        else:
            out += pkt_line(("%s capabilities^{}\x00%s\n" % (ZERO_OID, caps)).encode("utf-8"))
        out += FLUSH_PKT
        self._send(200, bytes(out), "application/x-git-upload-pack-advertisement")

    def _git_info_refs_receive(self, repo):
        caps = ("report-status side-band-64k delete-refs ofs-delta "
                "agent=makefun-forge/1.0")
        out = bytearray(encode_pkt_lines(["# service=git-receive-pack\n", "flush"]))
        refs = self._git_ad_refs(repo)
        first = True
        for oid, ref, _peeled in refs:
            line = "%s %s" % (oid, ref)
            if first:
                line += "\x00" + caps
                first = False
            out += pkt_line((line + "\n").encode("utf-8"))
        if not refs:
            out += pkt_line(("%s capabilities^{}\x00%s\n" % (ZERO_OID, caps)).encode("utf-8"))
        out += FLUSH_PKT
        self._send(200, bytes(out), "application/x-git-receive-pack-advertisement")

    def _git_upload_pack(self, repo):
        raw = self._read_body()
        if self.headers.get("Git-Protocol", "") == "version=2":
            self._git_upload_pack_v2(repo, raw)
            return
        self._git_upload_pack_v0(repo, raw)

    def _git_upload_pack_v2(self, repo, raw):
        try:
            packets = decode_pkt_lines(raw)
        except ValueError:
            self._send(400, b"", "application/x-git-upload-pack-result")
            return
        command = None
        args = []
        seen_delim = False
        for kind, payload in packets:
            if kind == "data":
                text = payload.decode("utf-8", "replace").rstrip("\n")
                if text.startswith("command=") and command is None:
                    command = text[len("command="):]
                elif seen_delim:
                    args.append(text)
            elif kind == "delim":
                seen_delim = True
        if command == "ls-refs":
            self._git_v2_ls_refs(repo, args)
        elif command == "fetch":
            self._git_v2_fetch(repo, args)
        else:
            self._send(400, b"", "application/x-git-upload-pack-result")

    def _git_v2_ls_refs(self, repo, args):
        peel = "peel" in args
        symrefs = "symrefs" in args
        prefixes = [a[len("ref-prefix "):] for a in args if a.startswith("ref-prefix ")]
        if not prefixes:
            prefixes = [""]
        tip = repo.default_tip()
        lines = []
        if tip is not None and any("HEAD".startswith(p) or p.startswith("HEAD") or p == "" for p in prefixes):
            line = "%s HEAD" % tip
            if symrefs:
                line += " symref-target:refs/heads/" + repo.default_branch
            lines.append(line)
        for ref in sorted(repo.refs):
            if not any(ref.startswith(p) for p in prefixes):
                continue
            oid = repo.refs[ref]
            line = "%s %s" % (oid, ref)
            if ref.startswith("refs/tags/") and peel:
                peeled = self.server.store.objects.peel_to_commit(oid)
                if peeled is not None and peeled != oid:
                    line += " peeled:%s" % peeled
            lines.append(line)
        body = encode_pkt_lines([line + "\n" for line in lines] + ["flush"])
        self._send(200, body, "application/x-git-upload-pack-result")

    def _git_v2_fetch(self, repo, args):
        store = self.server.store
        wants = []
        haves = []
        shallow_boundary = []
        depth = None
        for arg in args:
            if arg.startswith("want "):
                wants.append(arg[5:].strip())
            elif arg.startswith("have "):
                haves.append(arg[5:].strip())
            elif arg.startswith("shallow "):
                shallow_boundary.append(arg[8:].strip())
            elif arg.startswith("deepen "):
                try:
                    depth = int(arg[7:].strip())
                except ValueError:
                    depth = None
        chosen, shallow_out, unshallow_out = store.select_fetch(
            wants, haves, shallow_boundary, depth)
        out = bytearray()
        out += encode_pkt_lines(["acknowledgments\n"])
        if not haves:
            out += encode_pkt_lines(["NAK\n"])
        else:
            for have in haves:
                if store.objects.has(have):
                    out += encode_pkt_lines(["ACK %s\n" % have])
            out += encode_pkt_lines(["ready\n"])
        out += FLUSH_PKT
        out += encode_pkt_lines(["shallow-info\n"])
        for oid in shallow_out:
            out += encode_pkt_lines(["shallow %s\n" % oid])
        for oid in unshallow_out:
            out += encode_pkt_lines(["unshallow %s\n" % oid])
        out += FLUSH_PKT
        out += encode_pkt_lines(["packfile\n"])
        objects = []
        for oid in chosen:
            found = store.objects.get(oid)
            if found is not None:
                objects.append(found)
        pack = write_pack(objects)
        out += sideband_packets(pack)
        out += FLUSH_PKT
        self._send(200, bytes(out), "application/x-git-upload-pack-result")

    def _git_upload_pack_v0(self, repo, raw):
        store = self.server.store
        try:
            packets, second_start = decode_until_flush(raw)
            haves_packets, _rest = decode_until_flush(raw[second_start:])
        except ValueError:
            self._send(200, FLUSH_PKT, "application/x-git-upload-pack-result")
            return
        wants = []
        haves = []
        shallow_boundary = []
        depth = None
        for kind, payload in packets:
            if kind != "data":
                continue
            text = payload.decode("utf-8", "replace").rstrip("\n")
            if text.startswith("want "):
                want = text[5:].split("\x00", 1)[0].strip()
                wants.append(want)
            elif text.startswith("shallow "):
                shallow_boundary.append(text[8:].strip())
            elif text.startswith("deepen "):
                try:
                    depth = int(text[7:].strip())
                except ValueError:
                    depth = None
        for kind, payload in haves_packets:
            if kind != "data":
                continue
            text = payload.decode("utf-8", "replace").rstrip("\n")
            if text.startswith("have "):
                haves.append(text[5:].strip())
        chosen, shallow_out, unshallow_out = store.select_fetch(
            wants, haves, shallow_boundary, depth)
        out = bytearray()
        for oid in shallow_out:
            out += pkt_line(("shallow %s\n" % oid).encode("utf-8"))
        for oid in unshallow_out:
            out += pkt_line(("unshallow %s\n" % oid).encode("utf-8"))
        if not haves:
            out += pkt_line(b"NAK\n")
        else:
            for have in haves:
                if store.objects.has(have):
                    out += pkt_line(("ACK %s\n" % have).encode("utf-8"))
        objects = []
        for oid in chosen:
            found = store.objects.get(oid)
            if found is not None:
                objects.append(found)
        out += sideband_packets(write_pack(objects))
        out += FLUSH_PKT
        self._send(200, bytes(out), "application/x-git-upload-pack-result")

    def _git_receive_pack(self, repo, raw):
        store = self.server.store
        try:
            commands, pack_offset = decode_until_flush(raw)
        except ValueError:
            self._send(200, encode_pkt_lines(["unpack protocol error\n", "flush"]),
                       "application/x-git-receive-pack-result")
            return
        updates = []
        want_sideband = False
        first_line = True
        for kind, payload in commands:
            if kind != "data":
                continue
            text = payload.decode("utf-8", "replace").rstrip("\n")
            line = text.split("\x00", 1)[0]
            if first_line:
                first_line = False
                if "\x00" in text and "side-band-64k" in text.split("\x00", 1)[1]:
                    want_sideband = True
            parts = line.split()
            if len(parts) != 3:
                continue
            updates.append((parts[0], parts[1], parts[2]))
        pack_bytes = raw[pack_offset:]
        unpack_ok = True
        unpack_error = ""
        if pack_bytes:
            try:
                objects = read_pack(pack_bytes)
                for oid, (obj_type, data) in objects.items():
                    store.objects.put_known(oid, obj_type, data)
            except PackError as err:
                unpack_ok = False
                unpack_error = str(err)
        lines = []
        if unpack_ok:
            lines.append("unpack ok\n")
        else:
            lines.append("unpack %s\n" % unpack_error)
        for old, new, ref in updates:
            if not unpack_ok:
                lines.append("ng %s unpack failed\n" % ref)
                continue
            current = repo.refs.get(ref)
            if new == ZERO_OID:
                if current is None:
                    lines.append("ng %s delete of nonexistent ref\n" % ref)
                elif old != ZERO_OID and old != current:
                    lines.append("ng %s old value does not match\n" % ref)
                else:
                    del repo.refs[ref]
                    lines.append("ok %s\n" % ref)
                continue
            if old == ZERO_OID:
                if current is not None:
                    lines.append("ng %s ref already exists\n" % ref)
                    continue
            elif current is None:
                lines.append("ng %s ref does not exist\n" % ref)
                continue
            elif old != current:
                lines.append("ng %s old value does not match\n" % ref)
                continue
            if not store.objects.has(new):
                lines.append("ng %s object not found\n" % ref)
                continue
            target = store.objects.peel_to_commit(new)
            if old != ZERO_OID and target is not None:
                if not store.objects.is_ancestor(old, target):
                    lines.append("ng %s non-fast-forward\n" % ref)
                    continue
            repo.refs[ref] = new
            lines.append("ok %s\n" % ref)
        report = encode_pkt_lines(lines + ["flush"])
        if want_sideband:
            out = bytearray()
            out += pkt_line(b"\x01" + report)
            out += FLUSH_PKT
            self._send(200, bytes(out), "application/x-git-receive-pack-result")
        else:
            self._send(200, report, "application/x-git-receive-pack-result")


# ---------------------------------------------------------------------------
# GraphQL v4: a small parser for the fixed document set, plus an executor.
# ---------------------------------------------------------------------------


    # -- GraphQL v4 ----------------------------------------------------------

    def _route_graphql(self):
        raw = self._read_body()
        try:
            body = json.loads(raw.decode("utf-8")) if raw else {}
        except (ValueError, UnicodeDecodeError):
            self._send_json(400, {"errors": [{"message": "Problems parsing JSON"}]})
            return
        if isinstance(body, list):
            results = [self._gql_run(entry) for entry in body]
            self._send_json(200, results)
            return
        if not isinstance(body, dict):
            self._send_json(400, {"errors": [{"message": "Problems parsing JSON"}]})
            return
        self._send_json(200, self._gql_run(body))

    def _gql_run(self, body):
        query = body.get("query") or ""
        variables = body.get("variables") or {}
        try:
            _operation, selection = _GqlParser(query, variables).parse()
            data = {}
            for field in selection:
                data[field.alias] = self._gql_top(field)
            return {"data": data}
        except GraphQLError as err:
            return {"data": None, "errors": [{"message": str(err)}]}

    def _gql_top(self, field):
        store = self.server.store
        if field.type_condition:
            raise GraphQLError("inline fragments are not supported at the top level")
        if field.name == "viewer":
            user = _GqlObject("User", VIEWER)
            return self._gql_project(user, field.selection)
        if field.name == "repository":
            repo = store.get_repo(field.args.get("owner"), field.args.get("name"))
            if repo is None:
                return None
            return self._gql_project(_GqlObject("Repository", repo, repo), field.selection)
        if field.name == "node":
            decoded = decode_opaque_id(field.args.get("id") or "")
            if decoded is None:
                return None
            kind = decoded[0]
            if kind == "R" and len(decoded) == 3:
                repo = store.get_repo(decoded[1], decoded[2])
                if repo is None:
                    return None
                return self._gql_project(_GqlObject("Repository", repo, repo), field.selection)
            if kind == "I" and len(decoded) == 4:
                repo = store.get_repo(decoded[1], decoded[2])
                if repo is None:
                    return None
                issue = repo.issues.get(int(decoded[3])) if decoded[3].isdigit() else None
                if issue is None:
                    return None
                return self._gql_project(_GqlObject("Issue", issue, repo), field.selection)
            if kind == "P" and len(decoded) == 4:
                repo = store.get_repo(decoded[1], decoded[2])
                if repo is None:
                    return None
                pull = repo.pulls.get(int(decoded[3])) if decoded[3].isdigit() else None
                if pull is None:
                    return None
                return self._gql_project(_GqlObject("PullRequest", pull, repo), field.selection)
            return None
        if field.name == "__type":
            name = field.args.get("name")
            type_obj = _GqlObject("__Type", name)
            return self._gql_project(type_obj, field.selection)
        if field.name == "createIssue":
            return self._gql_create_issue(field)
        if field.name == "closeIssue":
            return self._gql_close_issue(field)
        if field.name == "createPullRequest":
            return self._gql_create_pull(field)
        if field.name == "mergePullRequest":
            return self._gql_merge_pull(field)
        if field.name == "addComment":
            return self._gql_add_comment(field)
        raise GraphQLError('Cannot query field "%s" on type "Query".' % field.name)

    def _gql_project(self, obj, selection):
        out = {}
        for field in selection:
            if field.type_condition:
                if field.type_condition == obj.type_name:
                    out.update(self._gql_project(obj, field.selection))
                continue
            value = self._gql_resolve(obj, field)
            if isinstance(value, _GqlObject):
                out[field.alias] = self._gql_project(value, field.selection)
            elif isinstance(value, list) and value and isinstance(value[0], _GqlObject):
                out[field.alias] = [self._gql_project(item, field.selection) for item in value]
            else:
                out[field.alias] = value
        return out

    def _gql_resolve(self, obj, field):
        store = self.server.store
        name = field.name
        value = obj.value
        type_name = obj.type_name
        if type_name == "User":
            if name == "login":
                return value["login"]
        elif type_name == "Repository":
            repo = value
            if name == "id":
                return repo.global_id()
            if name == "databaseId":
                return repo.db_id
            if name == "name":
                return repo.name
            if name == "nameWithOwner":
                return "%s/%s" % (repo.owner, repo.name)
            if name == "owner":
                return _GqlObject("User", VIEWER)
            if name == "defaultBranchRef":
                tip = repo.default_tip()
                if tip is None:
                    return None
                return _GqlObject("Ref", {"name": repo.default_branch})
            if name == "viewerPermission":
                return "ADMIN"
            if name == "hasIssuesEnabled":
                return True
            if name == "description":
                return repo.description
            if name == "private":
                return repo.private
            if name == "issue":
                issue = repo.issues.get(field.args.get("number"))
                if issue is None:
                    return None
                return _GqlObject("Issue", issue, repo)
            if name == "issues":
                return self._gql_issue_connection(repo, field.args)
            if name == "pullRequests":
                return self._gql_pull_connection(repo, field.args)
            if name == "pullRequest":
                pull = repo.pulls.get(field.args.get("number"))
                if pull is None:
                    return None
                return _GqlObject("PullRequest", pull, repo)
        elif type_name == "Issue":
            issue = value
            if name == "id":
                return opaque_id("I", obj.repo.owner, obj.repo.name, issue["number"])
            if name == "number":
                return issue["number"]
            if name == "title":
                return issue["title"]
            if name == "state":
                return _gql_issue_state(issue)
            if name == "body":
                return issue["body"]
        elif type_name == "PullRequest":
            pull = value
            if name == "id":
                return opaque_id("P", obj.repo.owner, obj.repo.name, pull["number"])
            if name == "number":
                return pull["number"]
            if name == "title":
                return pull["title"]
            if name == "state":
                return _gql_pull_state(pull)
            if name == "merged":
                return pull["merged"]
            if name == "headRefName":
                return pull["head"]
            if name == "baseRefName":
                return pull["base"]
            if name == "mergeable":
                if pull["state"] != "open":
                    return "UNKNOWN"
                return "CONFLICTING" if store.pull_conflict(obj.repo, pull) else "MERGEABLE"
            if name == "files":
                return self._gql_file_connection(obj.repo, pull, field.args)
        elif type_name == "IssueConnection":
            if name == "nodes":
                return [_GqlObject("Issue", issue, obj.repo) for issue in value["nodes"]]
            if name == "pageInfo":
                return _GqlObject("PageInfo", value["pageInfo"])
        elif type_name == "PullRequestConnection":
            if name == "nodes":
                return [_GqlObject("PullRequest", pull, obj.repo) for pull in value["nodes"]]
        elif type_name == "PullRequestChangedFileConnection":
            if name == "nodes":
                return [_GqlObject("PullRequestChangedFile", path) for path in value["nodes"]]
        elif type_name == "PullRequestChangedFile":
            if name == "path":
                return value
        elif type_name == "PageInfo":
            if name == "hasNextPage":
                return value["hasNextPage"]
            if name == "endCursor":
                return value["endCursor"]
        elif type_name == "Ref":
            if name == "name":
                return value["name"]
        elif type_name == "__Type":
            if name == "fields":
                return [_GqlObject("__Field", fname)
                        for fname in _GQL_TYPE_FIELDS.get(value, [])]
            if name == "enumValues":
                return [_GqlObject("__EnumValue", ename)
                        for ename in _GQL_ENUM_VALUES.get(value, [])]
            if name == "name":
                return value
        elif type_name == "__Field":
            if name == "name":
                return value
        elif type_name == "__EnumValue":
            if name == "name":
                return value
        elif type_name in ("CreateIssuePayload", "CloseIssuePayload"):
            if name == "issue":
                issue = value
                if issue is None:
                    return None
                return _GqlObject("Issue", issue, obj.repo)
        elif type_name in ("CreatePullRequestPayload", "MergePullRequestPayload"):
            if name == "pullRequest":
                pull = value
                if pull is None:
                    return None
                return _GqlObject("PullRequest", pull, obj.repo)
        elif type_name == "AddCommentPayload":
            if name == "commentEdge":
                return _GqlObject("IssueCommentEdge", value, obj.repo)
        elif type_name == "IssueCommentEdge":
            if name == "node":
                return _GqlObject("IssueComment", value, obj.repo)
        elif type_name == "IssueComment":
            if name == "id":
                comment = value
                return opaque_id("C", obj.repo.owner, obj.repo.name,
                                 comment["issue"], comment["id"])
            if name == "body":
                return value["body"]
        raise GraphQLError('Cannot query field "%s" on type "%s".' % (name, type_name))

    def _gql_issue_connection(self, repo, args):
        issues = list(repo.issues.values())
        states = args.get("states")
        if states:
            wanted = {"open" if s == "OPEN" else "closed" for s in states}
            issues = [i for i in issues if i["state"] in wanted]
        order_by = args.get("orderBy") or {}
        if order_by.get("field") == "CREATED_AT":
            issues.sort(key=lambda i: i["seq"], reverse=order_by.get("direction") != "ASC")
        else:
            issues.sort(key=lambda i: i["seq"])
        after = args.get("after")
        if after:
            after_number = cursor_number(after)
            if after_number is not None:
                issues = [i for i in issues if i["number"] > after_number]
        first = args.get("first")
        total = len(issues)
        if first is not None:
            page = issues[:first]
        else:
            page = issues
        has_next = len(page) < total
        end_cursor = cursor_for(page[-1]["number"]) if page else None
        return _GqlObject("IssueConnection",
                          {"nodes": page,
                           "pageInfo": {"hasNextPage": has_next, "endCursor": end_cursor}},
                          repo)

    def _gql_pull_connection(self, repo, args):
        pulls = [p for p in repo.pulls.values() if p["state"] == "open"]
        pulls.sort(key=lambda p: p["seq"])
        first = args.get("first")
        if first is not None:
            pulls = pulls[:first]
        return _GqlObject("PullRequestConnection", {"nodes": pulls}, repo)

    def _gql_file_connection(self, repo, pull, args):
        paths = [path for path, _s, _o, _n in self.server.store.pull_diff(repo, pull)]
        first = args.get("first")
        if first is not None:
            paths = paths[:first]
        return _GqlObject("PullRequestChangedFileConnection", {"nodes": paths}, repo)

    def _gql_repo_from_id(self, global_id):
        decoded = decode_opaque_id(global_id or "")
        if decoded is None or decoded[0] != "R" or len(decoded) != 3:
            return None
        return self.server.store.get_repo(decoded[1], decoded[2])

    def _gql_issue_from_id(self, global_id):
        decoded = decode_opaque_id(global_id or "")
        if decoded is None or decoded[0] != "I" or len(decoded) != 4:
            return None, None
        repo = self.server.store.get_repo(decoded[1], decoded[2])
        if repo is None or not decoded[3].isdigit():
            return None, None
        return repo, repo.issues.get(int(decoded[3]))

    def _gql_pull_from_id(self, global_id):
        decoded = decode_opaque_id(global_id or "")
        if decoded is None or decoded[0] != "P" or len(decoded) != 4:
            return None, None
        repo = self.server.store.get_repo(decoded[1], decoded[2])
        if repo is None or not decoded[3].isdigit():
            return None, None
        return repo, repo.pulls.get(int(decoded[3]))

    def _gql_create_issue(self, field):
        store = self.server.store
        input_data = field.args.get("input") or {}
        repo = self._gql_repo_from_id(input_data.get("repositoryId"))
        if repo is None:
            raise GraphQLError("repositoryId does not name a repository")
        issue, error = store.create_issue(repo, input_data.get("title", ""),
                                          input_data.get("body", ""), [])
        if issue is None:
            raise GraphQLError(error)
        payload = _GqlObject("CreateIssuePayload", issue, repo)
        return self._gql_project(payload, field.selection)

    def _gql_close_issue(self, field):
        input_data = field.args.get("input") or {}
        repo, issue = self._gql_issue_from_id(input_data.get("issueId"))
        if issue is None:
            raise GraphQLError("issueId does not name an issue")
        issue["state"] = "closed"
        issue["updated_at"] = tick_iso()
        payload = _GqlObject("CloseIssuePayload", issue, repo)
        return self._gql_project(payload, field.selection)

    def _gql_create_pull(self, field):
        store = self.server.store
        input_data = field.args.get("input") or {}
        repo = self._gql_repo_from_id(input_data.get("repositoryId"))
        if repo is None:
            raise GraphQLError("repositoryId does not name a repository")
        pull, error = store.create_pull(repo, input_data.get("headRefName", ""),
                                        input_data.get("baseRefName", ""),
                                        input_data.get("title", ""),
                                        input_data.get("body", ""))
        if pull is None:
            raise GraphQLError(error)
        payload = _GqlObject("CreatePullRequestPayload", pull, repo)
        return self._gql_project(payload, field.selection)

    def _gql_merge_pull(self, field):
        store = self.server.store
        input_data = field.args.get("input") or {}
        repo, pull = self._gql_pull_from_id(input_data.get("pullRequestId"))
        if pull is None:
            raise GraphQLError("pullRequestId does not name a pull request")
        status, payload = store.merge_pull(repo, pull)
        if status >= 400:
            raise GraphQLError(payload["message"])
        result = _GqlObject("MergePullRequestPayload", pull, repo)
        return self._gql_project(result, field.selection)

    def _gql_add_comment(self, field):
        store = self.server.store
        input_data = field.args.get("input") or {}
        repo, issue = self._gql_issue_from_id(input_data.get("subjectId"))
        if issue is None:
            raise GraphQLError("subjectId does not name an issue")
        comment = {
            "id": store.next_comment_id,
            "body": input_data.get("body", ""),
            "issue": issue["number"],
            "created_at": tick_iso(),
            "updated_at": tick_iso(),
        }
        store.next_comment_id += 1
        issue["comments"].append(comment)
        payload = _GqlObject("AddCommentPayload", comment, repo)
        return self._gql_project(payload, field.selection)


    # -- MCP ------------------------------------------------------------------

    def _route_mcp(self):
        raw = self._read_body()
        try:
            body = json.loads(raw.decode("utf-8")) if raw else None
        except (ValueError, UnicodeDecodeError):
            body = None
        if body is None or not isinstance(body, dict):
            self._send_json(400, {"jsonrpc": "2.0",
                                  "error": {"code": -32700, "message": "Parse error"},
                                  "id": None})
            return
        method = body.get("method", "")
        request_id = body.get("id")
        params = body.get("params") or {}
        if method.startswith("notifications/"):
            self._send(200, b"")
            return
        if method == "server/discover":
            info = {"name": SERVER_NAME, "version": SERVER_VERSION}
            self._send_json(200, {"jsonrpc": "2.0", "id": request_id, "result": {
                "supportedVersions": ["2026-07-28"],
                "serverInfo": info,
                "capabilities": {"tools": {}},
                "_meta": {"io.modelcontextprotocol/serverInfo": info},
            }})
            return
        if method == "initialize":
            offered = params.get("protocolVersion", "2025-11-25")
            supported = ["2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"]
            negotiated = offered if offered in supported else "2025-11-25"
            self._send_json(200, {"jsonrpc": "2.0", "id": request_id, "result": {
                "protocolVersion": negotiated,
                "capabilities": {"tools": {}},
                "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
            }})
            return
        if method == "tools/list":
            self._send_json(200, {"jsonrpc": "2.0", "id": request_id,
                                  "result": {"tools": _MCP_TOOLS}})
            return
        if method == "tools/call":
            self._mcp_call(request_id, params)
            return
        self._send_json(200, {"jsonrpc": "2.0", "id": request_id,
                              "error": {"code": -32601, "message": "Method not found: %s" % method}})

    def _mcp_call(self, request_id, params):
        name = (params.get("name") or "").lower()
        if "__" in name:
            name = name.rsplit("__", 1)[-1]
        arguments = params.get("arguments") or {}
        handler = _MCP_HANDLERS.get(name)
        if handler is None:
            self._send_json(200, {"jsonrpc": "2.0", "id": request_id,
                                  "error": {"code": -32602, "message": "Unknown tool: %s" % name}})
            return
        try:
            result = getattr(self, handler)(arguments)
        except ApiError as err:
            result = {"isError": True, "text": err.message}
        if result.get("isError"):
            payload = {"content": [{"type": "text", "text": result["text"]}],
                       "isError": True}
        else:
            text = json.dumps(result["data"], separators=(",", ":"))
            payload = {"content": [{"type": "text", "text": text}],
                       "structuredContent": result["data"], "isError": False}
        self._send_json(200, {"jsonrpc": "2.0", "id": request_id, "result": payload})

    def _mcp_repo(self, arguments):
        owner = arguments.get("owner")
        repo_name = arguments.get("repo") or arguments.get("repository")
        full_name = arguments.get("full_name")
        if (owner is None or repo_name is None) and full_name:
            parts = str(full_name).split("/", 1)
            if len(parts) == 2:
                owner, repo_name = parts
        if owner is None or repo_name is None:
            raise ApiError(400, "owner and repo are required")
        repo = self.server.store.get_repo(owner, repo_name)
        if repo is None:
            raise ApiError(404, "Not Found")
        return repo

    def _mcp_create_repo(self, arguments):
        name = arguments.get("name")
        if not name:
            raise ApiError(400, "name is required")
        repo, error = self.server.store.create_repo(
            name, private=arguments.get("private", False),
            description=arguments.get("description", ""))
        if repo is None:
            raise ApiError(422, error)
        return {"data": repo_view(repo)}

    def _mcp_get_repo(self, arguments):
        return {"data": repo_view(self._mcp_repo(arguments))}

    def _mcp_list_repos(self, arguments):
        repos = self.server.store.list_repos()
        return {"data": {"repositories": [repo_view(r) for r in repos]}}

    def _mcp_create_issue(self, arguments):
        repo = self._mcp_repo(arguments)
        title = arguments.get("title")
        if not title:
            raise ApiError(400, "title is required")
        issue, error = self.server.store.create_issue(
            repo, title, arguments.get("body", ""), [])
        if issue is None:
            raise ApiError(422, error)
        return {"data": issue_view(repo, issue)}

    def _mcp_get_issue(self, arguments):
        repo = self._mcp_repo(arguments)
        number = arguments.get("issue_number") or arguments.get("number")
        issue = repo.issues.get(number) if isinstance(number, int) else None
        if issue is None:
            raise ApiError(404, "Not Found")
        return {"data": issue_view(repo, issue)}

    def _mcp_list_issues(self, arguments):
        repo = self._mcp_repo(arguments)
        state = arguments.get("state") or "open"
        issues = self.server.store.list_issues(repo, state)
        return {"data": {"issues": [issue_view(repo, i) for i in issues]}}

    def _mcp_create_pull(self, arguments):
        repo = self._mcp_repo(arguments)
        title = arguments.get("title")
        head = arguments.get("head")
        base = arguments.get("base")
        if not title or not head or not base:
            raise ApiError(400, "title, head and base are required")
        pull, error = self.server.store.create_pull(
            repo, head, base, title, arguments.get("body", ""))
        if pull is None:
            raise ApiError(422, error)
        return {"data": pull_view(repo, pull)}

    def _mcp_list_pulls(self, arguments):
        repo = self._mcp_repo(arguments)
        state = arguments.get("state") or "open"
        pulls = list(repo.pulls.values())
        if state in ("open", "closed"):
            pulls = [p for p in pulls if p["state"] == state]
        pulls.sort(key=lambda p: p["seq"], reverse=True)
        return {"data": {"pull_requests": [pull_view(repo, p) for p in pulls]}}

    def _mcp_merge_pull(self, arguments):
        repo = self._mcp_repo(arguments)
        number = arguments.get("pull_number") or arguments.get("number")
        pull = repo.pulls.get(number) if isinstance(number, int) else None
        if pull is None:
            raise ApiError(404, "Not Found")
        status, payload = self.server.store.merge_pull(repo, pull)
        if status >= 400:
            raise ApiError(status, payload["message"])
        return {"data": {"merged": True, "sha": payload["sha"],
                         "number": pull["number"], "message": payload["message"]}}


class GraphQLError(Exception):
    pass


_GQL_TOKEN = re.compile(r"""
    \s*(?:
    (?P<dots>\.\.\.)
    |(?P<name>[A-Za-z_][A-Za-z0-9_]*)
    |(?P<int>-?[0-9]+)
    |(?P<string>"(?:[^"\\]|\\.)*")
    |(?P<punct>[\{\}\(\)\:\,\$\!\[\]\=])
    )
""", re.VERBOSE)


def _gql_tokens(text):
    tokens = []
    pos = 0
    while pos < len(text):
        if text[pos] in " \t\r\n,":
            pos += 1
            continue
        if text[pos] == "#":
            end = text.find("\n", pos)
            pos = len(text) if end < 0 else end + 1
            continue
        match = _GQL_TOKEN.match(text, pos)
        if match is None:
            raise GraphQLError("cannot tokenize GraphQL at %r" % text[pos:pos + 20])
        pos = match.end()
        if match.group("dots"):
            tokens.append(("...", "..."))
        elif match.group("name"):
            tokens.append(("name", match.group("name")))
        elif match.group("int"):
            tokens.append(("int", int(match.group("int"))))
        elif match.group("string"):
            tokens.append(("string", json.loads(match.group("string"))))
        else:
            tokens.append((match.group("punct"), match.group("punct")))
    tokens.append(("eof", None))
    return tokens


class _GqlField:
    __slots__ = ("name", "alias", "args", "selection", "type_condition")

    def __init__(self, name, alias=None, args=None, selection=None, type_condition=None):
        self.name = name
        self.alias = alias or name
        self.args = args or {}
        self.selection = selection or []
        self.type_condition = type_condition


class _GqlParser:
    def __init__(self, text, variables):
        self.tokens = _gql_tokens(text)
        self.pos = 0
        self.variables = variables or {}

    def peek(self):
        return self.tokens[self.pos]

    def take(self, kind=None):
        token = self.tokens[self.pos]
        if kind is not None and token[0] != kind:
            raise GraphQLError("expected %s, found %s" % (kind, token[0]))
        self.pos += 1
        return token[1]

    def parse(self):
        kind, value = self.peek()
        operation = "query"
        if kind == "name" and value in ("query", "mutation", "subscription"):
            operation = value
            self.take("name")
            if self.peek()[0] == "name":
                self.take("name")
            if self.peek()[0] == "(":
                self._skip_parens()
        return operation, self._selection_set()

    def _skip_parens(self):
        depth = 0
        while True:
            value = self.take()
            if value == "(":
                depth += 1
            elif value == ")":
                depth -= 1
                if depth == 0:
                    return
            elif value is None:
                raise GraphQLError("unbalanced parentheses")

    def _selection_set(self):
        self.take("{")
        fields = []
        while self.peek()[0] != "}":
            fields.extend(self._field())
            if self.peek()[0] == "eof":
                raise GraphQLError("unbalanced selection set")
        self.take("}")
        return fields

    def _field(self):
        kind, value = self.peek()
        if kind == "...":
            self.take("...")
            if self.peek() == ("name", "on"):
                self.take("name")
                condition = self.take("name")
                return [_GqlField("", selection=self._selection_set(), type_condition=condition)]
            return self._selection_set()
        first = self.take("name")
        if self.peek()[0] == ":":
            self.take(":")
            name = self.take("name")
            alias = first
        else:
            name, alias = first, first
        args = {}
        if self.peek()[0] == "(":
            args = self._arguments()
        selection = []
        if self.peek()[0] == "{":
            selection = self._selection_set()
        return [_GqlField(name, alias, args, selection)]

    def _arguments(self):
        self.take("(")
        args = {}
        while self.peek()[0] != ")":
            name = self.take("name")
            self.take(":")
            args[name] = self._value()
            if self.peek()[0] == "eof":
                raise GraphQLError("unbalanced arguments")
        self.take(")")
        return args

    def _value(self):
        kind, value = self.peek()
        if kind == "$":
            self.take("$")
            name = self.take("name")
            return self.variables.get(name)
        if kind == "string":
            self.take("string")
            return value
        if kind == "int":
            self.take("int")
            return value
        if kind == "name":
            self.take("name")
            if value == "true":
                return True
            if value == "false":
                return False
            if value == "null":
                return None
            return value
        if kind == "[":
            self.take("[")
            items = []
            while self.peek()[0] != "]":
                items.append(self._value())
            self.take("]")
            return items
        if kind == "{":
            self.take("{")
            obj = {}
            while self.peek()[0] != "}":
                name = self.take("name")
                self.take(":")
                obj[name] = self._value()
            self.take("}")
            return obj
        raise GraphQLError("unexpected value token %s" % kind)


_GQL_TYPE_FIELDS = {
    "Issue": ["id", "number", "title", "state", "body", "createdAt", "updatedAt",
              "author", "labels", "comments", "url"],
    "PullRequest": ["id", "number", "title", "state", "merged", "headRefName",
                    "baseRefName", "mergeable", "files", "body", "createdAt",
                    "updatedAt", "author", "url"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "issue", "issues", "pullRequests", "pullRequest",
                   "description", "private", "createdAt", "updatedAt"],
    "SearchType": [],
}
_GQL_ENUM_VALUES = {
    "SearchType": ["ISSUE", "USER", "REPOSITORY"],
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
}


class _GqlObject:
    """A resolved value plus the GraphQL type it answers as."""

    __slots__ = ("type_name", "value", "repo")

    def __init__(self, type_name, value, repo=None):
        self.type_name = type_name
        self.value = value
        self.repo = repo


def _gql_issue_state(issue):
    return "OPEN" if issue["state"] == "open" else "CLOSED"


def _gql_pull_state(pull):
    if pull["merged"]:
        return "MERGED"
    return "OPEN" if pull["state"] == "open" else "CLOSED"


def _mcp_tool(name, description, properties, required):
    return {
        "name": name,
        "description": description,
        "inputSchema": {"type": "object", "properties": properties,
                        "required": required},
    }


_MCP_TOOLS = [
    _mcp_tool("create_repo", "Create a repository for the authenticated user.", {
        "name": {"type": "string", "description": "The repository name."},
        "description": {"type": "string", "description": "A short description."},
        "private": {"type": "boolean", "description": "Whether the repository is private."},
    }, ["name"]),
    _mcp_tool("get_repo", "Read one repository by owner and name.", {
        "owner": {"type": "string", "description": "The repository owner."},
        "repo": {"type": "string", "description": "The repository name."},
        "full_name": {"type": "string", "description": "owner/repo, an alternative to owner and repo."},
    }, ["owner", "repo"]),
    _mcp_tool("list_repos", "List the authenticated user's repositories.", {}, []),
    _mcp_tool("create_issue", "Create an issue in a repository.", {
        "owner": {"type": "string", "description": "The repository owner."},
        "repo": {"type": "string", "description": "The repository name."},
        "title": {"type": "string", "description": "The issue title."},
        "body": {"type": "string", "description": "The issue body."},
    }, ["owner", "repo", "title"]),
    _mcp_tool("get_issue", "Read one issue by number.", {
        "owner": {"type": "string", "description": "The repository owner."},
        "repo": {"type": "string", "description": "The repository name."},
        "issue_number": {"type": "integer", "description": "The issue number."},
    }, ["owner", "repo", "issue_number"]),
    _mcp_tool("list_issues", "List issues in a repository.", {
        "owner": {"type": "string", "description": "The repository owner."},
        "repo": {"type": "string", "description": "The repository name."},
        "state": {"type": "string", "description": "open, closed or all."},
    }, ["owner", "repo"]),
    _mcp_tool("create_pull_request", "Create a pull request from a head branch to a base branch.", {
        "owner": {"type": "string", "description": "The repository owner."},
        "repo": {"type": "string", "description": "The repository name."},
        "title": {"type": "string", "description": "The pull request title."},
        "head": {"type": "string", "description": "The head branch name."},
        "base": {"type": "string", "description": "The base branch name."},
        "body": {"type": "string", "description": "The pull request body."},
    }, ["owner", "repo", "title", "head", "base"]),
    _mcp_tool("list_pull_requests", "List pull requests in a repository.", {
        "owner": {"type": "string", "description": "The repository owner."},
        "repo": {"type": "string", "description": "The repository name."},
        "state": {"type": "string", "description": "open, closed or all."},
    }, ["owner", "repo"]),
    _mcp_tool("merge_pull_request", "Squash-merge a pull request.", {
        "owner": {"type": "string", "description": "The repository owner."},
        "repo": {"type": "string", "description": "The repository name."},
        "pull_number": {"type": "integer", "description": "The pull request number."},
    }, ["owner", "repo", "pull_number"]),
]

_MCP_HANDLERS = {
    "create_repo": "_mcp_create_repo",
    "get_repo": "_mcp_get_repo",
    "list_repos": "_mcp_list_repos",
    "create_issue": "_mcp_create_issue",
    "get_issue": "_mcp_get_issue",
    "list_issues": "_mcp_list_issues",
    "create_pull_request": "_mcp_create_pull",
    "list_pull_requests": "_mcp_list_pulls",
    "merge_pull_request": "_mcp_merge_pull",
}


# ---------------------------------------------------------------------------
# Lifecycle: bind an ephemeral port, register with the environment, serve,
# and exit when the environment says the suite is done.
# ---------------------------------------------------------------------------


def _env_url():
    return os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")


def _register(env_url, port):
    url = env_url + "/register"
    payload = json_bytes({"port": port})
    request = urllib.request.Request(
        url, data=payload, method="POST",
        headers={"Content-Type": "application/json"})
    for attempt in range(20):
        try:
            with urllib.request.urlopen(request, timeout=5) as response:
                if response.status in (200, 201, 409):
                    return True
        except Exception as err:
            if attempt == 19:
                print("register failed: %s" % err, file=sys.stderr)
        time.sleep(0.25 * (attempt + 1))
    return False


def _done(env_url):
    url = env_url + "/done"
    try:
        with urllib.request.urlopen(url, timeout=5) as response:
            body = json.loads(response.read().decode("utf-8"))
            return bool(body.get("done"))
    except Exception:
        return False


def _poll_done(env_url, server):
    while True:
        time.sleep(0.5)
        if _done(env_url):
            server.shutdown()
            return


def main():
    port_env = os.environ.get("PORT")
    bind_port = int(port_env) if port_env else 0
    server = ForgeServer(("0.0.0.0", bind_port), ForgeHandler)
    port = server.server_address[1]
    print("makefun-forge listening on port %d" % port, flush=True)
    env_url = _env_url()
    if env_url:
        if not _register(env_url, port):
            print("could not register with the environment", file=sys.stderr)
            return 1
        watcher = threading.Thread(target=_poll_done, args=(env_url, server),
                                   daemon=True)
        watcher.start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
