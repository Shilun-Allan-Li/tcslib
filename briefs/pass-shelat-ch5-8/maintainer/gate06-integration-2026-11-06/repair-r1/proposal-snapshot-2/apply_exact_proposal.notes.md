# Exact proposal normalizer: preparation review

**PREPARED / NOT RUN against the library.** Tool: `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/gate06/repairs/apply_exact_proposal.py`.
Frozen tool SHA-256: `125c58457708317015dd0cce9695b83521644bdbbda3841e5cc855fc63923951`. Length: 128 lines.
Only the tool and these notes were written by this invocation. No library edits, Git apply,
Lean/cache/build command, CLI apply run, or external agent program execution occurred.

## Interface

Dry-run is the default. It reads the current target bytes, parses the original proposal as
data, composes its exact hunks in memory, and creates a fresh three-context `.patch` plus
`.json` plan. The artifact parent directory must already exist. The prefix is literal:
`.patch` and `.json` are appended; both artifacts must be new. Every creation uses exclusive
`open("x")`; retries and later apply runs need a new prefix.

```sh
python3 -I -B .lake/ps-maintainer/gate06/repairs/apply_exact_proposal.py   .lake/ps-maintainer/gate06/repairs/HashAndSign-correct-coin-transport.patch   --out-prefix .lake/ps-maintainer/gate06/repairs/HashAndSign-correct-exact-dry-r1
```

After maintainer review, root alone may add `--apply` with a fresh output prefix. `--root`
defaults to this script's Gate06 checkout root; an explicit root can be supplied. The apply
flag denotes the parent maintainer's authorized operation; it is not an OS-superuser check.
The agent preparing this tool did not use that flag or invoke the CLI.

## Exactness and guards

`parse_patch(text)` and `plan(files, changes)` are pure APIs with no filesystem/Git effects.
The parser accepts only existing `a/TCSlib/...lean` -> identical `b/...` paths. An optional
same-path `diff --git` banner is accepted; renames, modes/index metadata, duplicate file
sections, foreign/traversal paths, CRLF, unterminated lines and no-newline markers are
rejected. Empty-old-segment insertion hunks are unsupported because they have no unique
exact anchor. Every declared old/new row count must equal the actual count. **No automatic
recount is performed.**

For each hunk, the entire old segment must occur literally once in the current in-memory
file, including overlapping occurrences, and start on a line boundary. No fuzz, whitespace
ignoring or near-match search is used. Hunks compose sequentially in memory. Original line
numbers can differ from current positions; the metadata records both proposal starts and
the exact matched line after prior hunks. Original/proposed file SHA-256, original proposal
SHA-256 and canonical-patch SHA-256 are recorded.

`difflib.unified_diff(..., n=3)` emits the canonical current-to-proposed patch. This gives
Git valid context for the HashAndSign middle-hunk case without changing the proposed code.
Targets must be regular files without symlinked path components. Artifacts are kept outside
TCSlib and existing artifacts are never overwritten.

With `--apply`, all target paths and original bytes are checked before `git apply --check`
and checked again before `git apply`. Both commands consume the same canonical bytes from
memory through stdin, so editing a saved patch cannot alter the applied payload. Git runs
without index/staging options. No source write occurs before the check succeeds. The JSON
records the plan and `apply_requested`, not a claim of successful application; a successful
CLI prints `applied`, while failures return nonzero. A failed attempt preserves its plan
artifacts and a retry needs a fresh prefix.

## Static/pure validation

Syntax was checked with `ast.parse` and `compile`; definitions were loaded under a non-main
namespace using Python `-I -B`, so no CLI, Git subprocess or bytecode cache ran in validation.
Twenty-eight pure checks passed, covering canonical round trips, multi-file edits, sequential
relocation, duplicate/overlapping/partial-line matches, exact whitespace, unsafe paths,
renames/modes, duplicate file sections, LF requirements, unsupported empty anchors, no-op
proposals, and current proposal banners.

The original `PRFMAC-correct-coin-transport.patch` is rejected explicitly:
`declared 16/19, actual 15/18`. Its separately supplied recount artifact parses. The normalizer
will not silently accept or repair the malformed original.

The real HashAndSign proposal was composed as data against the captured generator state,
plus the existing local-let and signer proposals. Its two exact matches were at lines291
and310 after prior hunks, despite old proposal starts272 and285. Canonical reparse/application
reproduced the exact intended source bytes:

* input SHA-256: `9871bf89421f8ac5a366f823846991fa16ff18ae14f7a58974d12c0e967f24b6`;
* proposed SHA-256: `1ac55fe2bbdf277f0d79de9afa55ae42371b584fb9131ad55d7f45dcca158a7f`.

No actual Git acceptance/apply or native elaboration is claimed. Root reviews this frozen
tool before running it; all source/native queue coordination remains root-owned.
