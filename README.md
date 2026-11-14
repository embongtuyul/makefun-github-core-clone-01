# GitHub-compatible git forge

A standalone GitHub-compatible git forge in one Python process, stdlib only —
no git binary, no UI, no outside service. Built for the make.fun
`github-core-clone-01` competition.

## What it serves

- **Git smart HTTP** at `/{owner}/{repo}.git` — upload-pack protocol v2
  (`ls-refs`, `fetch`, shallow/deepen) and receive-pack v0, over a real
  object store (loose objects + packfiles, refs, OFS/REF delta resolution).
- **REST v3** at `/api/v3` — repos (CRUD, branches, commits, git/refs),
  contents (PUT/DELETE with sha handling), labels, issues, pull requests
  with squash merge and conflict detection.
- **GraphQL v4** at `/api/graphql` — `viewer`, `repository`, `issue(s)`,
  `pullRequest(s)`, mutations (`createIssue`, `closeIssue`,
  `createPullRequest`, `mergePullRequest`, `addComment`), `node(id:)`,
  introspection, cursor pagination, operation batching.
- **MCP** at `/mcp` — JSON-RPC 2.0 Streamable HTTP, modern
  `server/discover` (revision 2026-07-28) with legacy `initialize`
  fallback; tools `create_repo`, `get_repo`, `create_issue`,
  `list_issues`, `create_pull_request`, `merge_pull_request`.

## Wire contract

Binds an ephemeral port, POSTs `{"port": N}` to `$MAKEFUN_ENV_URL/register`,
long-polls GET `$MAKEFUN_ENV_URL/done`, exits 0 when done. Every call needs
`Authorization: Bearer $MAKEFUN_SHOP_TOKEN` (missing token = 401). Every
REST reply is `application/json` with a non-empty `X-GitHub-Request-Id`.

## Run

```sh
MAKEFUN_SHOP_TOKEN=<token> python3 main.py
```

## Local conformance

Against the kit's sealed suite (`sdk/run.ts`):

- 120/120 checks pass — feature 600/600, agent 200/200.
- With `--perf`: total score **938–945 / 1000** (two fresh-server runs:
  perf 138 and 145). Per workload (best run): push 36, clone 32,
  read 39, write 38 points vs the house reference medians.
  See `~/workspace/makefun/kits/github-core-clone-01-kit/`.

## License

MIT — see `LICENSE`.
