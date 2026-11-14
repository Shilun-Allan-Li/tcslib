# dl-crh — checkpoint 1 escalation

**Status: stopped at the missing-reader escalation required by the issued brief.**
`Authentication.dlHash_crh` is still admitted. No compression lemma, reduction,
or collision-resistance proof is submitted. The target statement is unchanged;
no mathematical counterexample is claimed.

## Provenance and checkout

- Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.
- Proof base and local `fill/dl-crh` HEAD:
  `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
- Campaign branch fetched from `https://github.com/Shilun-Allan-Li/tcslib.git`.
- Separate worktree:
  `/Users/seyoonr/.codex/worktrees/ps-dl-crh/tcslib-exchange`.
- Lean pin: `leanprover/lean4:v4.25.0`; Mathlib:
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- All seven issued pack checksums and all 170 issue-source checksums pass.
  Raw logs: `evidence/logs/pack-verification.log` and
  `evidence/logs/source-inspection.log`.
- The local proof branch has zero commits beyond the issue base and has never
  been pushed. Deliveries are restricted to `inbox/fills/dl-crh/` on the exchange.

## Exact stop and reader requests

The brief requires a checkpoint when a reader of a foreign definition is
missing. `dlHashIdx_eq` exposes a call of `Candidates.expGenFun`, for which the
base exports only an efficiency theorem. There is no published raw behavior
reader. The first missing obligation is:

```lean
-- hn : G.n₀ ≤ n; r : G.gen.Coins n
pairFstD (expGenFun G
  (NUPPT.layout (List.replicate n true) [] [] (List.ofFn r))) =
  G.gen.runAt n [] r
```

The next related gap is `Candidates.expSampleRaw`, directly called by
`dlHashGenFun_eq`: it also has only an efficiency theorem. The existing bundled
machine readers `expGen_runAt` and `expSampler_runAt` cannot bridge to these raw
calls without unfolding a foreign wrapper or using an unpublished equation.

Request provider-side `expGenFun_eq` and `expSampleRaw_eq`, or equivalent
raw-layout readers. Exact proposed statements, the derivation obstacle, and the
resumption request are in `evidence/reader-request.md`. Both direct body
equations are provider-side `rfl` lemmas; none was introduced into an owned
helper, since that would violate Rule 10. Two independent read-only agents
confirmed the source search. No external proof code was consulted.

## Changes, overlap, and scope

- Changed/new Lean files: **none**. No sketch, module-title, statement, or simp
  attribute edits were made before the stop.
- New declarations: **none**. Promotion requests: the two reader requests above
  in `Candidates/DiscreteLog.lean`; no generic probability/list/machine helpers.
- Overlap items: **none**. No public or private proof was copied or re-derived.
- `src/TCSlib/Cryptography/Hashing/FromDiscreteLog.lean` is an unchanged issue-base
  snapshot. The complete `git format-patch` series is empty; its raw stdout is
  included and `patches/README.md` explains this.
- Checkpoint 1's mathematical goals remain open. Checkpoint 2 and the final key
  distribution step were not attempted after the mandated stop. Their edge
  cases have not been certified.

## Host and checks

Native diagnostic `evidence/logs/preflight.log` records macOS, 12 logical CPUs,
19,327,352,832 bytes of physical memory, and 266,047,056 available 1024-byte disk
blocks on APFS at both the worktree and `/private/tmp`: **272,432,185,344 bytes
free**, above the 12 GiB floor. `nproc`, Linux cgroup counters, `/proc/meminfo`,
GNU `df -B1`, and `df -T` are unavailable on this host; native `sysctl`,
`vm_stat`, `memory_pressure -Q`, `df -k`, and `mount` are recorded instead.
`memory_pressure -Q` reported 50% system-wide memory free. This is not asserted
to be Linux `MemAvailable`, and the prescribed headroom formula is not
certified. Other sessions had active Lake commands; none was interrupted.

No Lean, Lake, toolchain installation, cache fetch, package reuse/symlink, or
bootstrap was started by this worker. No dependency tree was copied or reused.
The stop is a **reader escalation**, not an E-RES assertion. A continuation
must resolve the readers and satisfy the environment addendum before checking.

- The 170-module order and 87 narrowed Mathlib roots are retained verbatim.
- Bootstrap, module checks, final sweep, compiled sorry comparison, target/all
  stored-constant axiom output, full-closure base/final seals A/B (with
  `PolyExpr.eval` excluded and sealed), and paired controls were **not run**.
  There is no changed/new Lean proof to certify, and no prerequisites were
  built. No failure or pass is invented for these checks.
- Explicit-unfold scan of changed/new Lean files: empty scope; no probe or seal
  sources were generated or run. The source search that establishes the reader
  request is delivered with its reproduction tool and raw output.
- `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`
  ran on the unchanged issue tree: exit 1, **216 existing FAIL, 102 WARN, 301
  files**. No new FAIL is possible with the verified zero source diff. Its raw
  log and the exact tool bytes are delivered. No lint fix outside scope was made.
- `evidence/results.jsonl` records performed checks and skipped checks explicitly.

## Evidence completeness and continuation

`evidence/SHA256SUMS` covers every evidence file except itself. Root
`SHA256SUMS` covers every payload file except itself, including the evidence
manifest. The packaging tool verifies exact path-set equality and all hashes;
the ZIP has `dl-crh/` at its root. All generated evidence and tools are included;
there are no omitted raw probe/seal/control logs because none were generated.

This delivery is reviewable escalation evidence, **not a completed fill**.
Continuation requires provider readers and an updated base or issued overlay.
