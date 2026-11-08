# Fill `cleanup-part2` — REPORT

**Status: CHECKPOINT 0 (environment and baseline).** See the per-milestone sections below.

## Identity

| item | value |
|---|---|
| issue pack | `exchange/pass-shelat-ch5-8` at `5b1d70d558542bf491680b4b9ee2379038bbfd3f`, `outbox/fills/cleanup-part2/`; `SHA256SUMS` SHA-256 `078baef661c1152179603b7f1495000fc7287c47164f6fc06baf7b7c855c3e37` (matches the dispatch), all 298 entries OK |
| attachment manifests | `inputs/DELIVERY-MANIFEST.json` `994c8dc0…`, `inputs/INPUTS-MANIFEST.json` `31252c05…`, `external-bootstrap-r1/DELIVERY-MANIFEST.json` `70dd1a40…`, `environment-tools/MANIFEST.json` `40006423…`, `environment-tools/RUNBOOK.md` `4102e174…` — all equal to the brief's pins |
| records snapshot (dispatch) | `0a874231cd3eaa370132970fbf6f5882f5b66e47` on `cryptography/pass-shelat-ch2-4` (cited by the dispatch; not needed for any check) |
| source ancestor | `1aa5506f58f77c215e56d24311ec33bd931cacf1`; `TCSlib/` tree `6ea8b3246478524165b3226c935b12a73853f47b` (verified) |
| fill branch | local `fill/cleanup-part2` in the own clone `/workspace/cp2/src`, created at the ancestor; never rebased/merged; never pushed |
| worker | one Claude session, no subagents or delegated workers |

## Checkpoint 0: environment and baseline (complete)

### Mode, paths and preflight

* Default own-clone/own-package mode: one source clone `/workspace/cp2/src` (fresh `git clone` of
  `github.com/Shilun-Allan-Li/tcslib`, branch `fill/cleanup-part2` at the ancestor), its own
  `.lake/packages`, one olean tree `TCSLIB_OLEANS=/workspace/cp2/src/.lake/cleanup-part2-oleans`.
  The exchange checkout `/workspace/tcslib` carries payloads only. A detached drafting worktree
  `/workspace/cp2/draft` (same repository, ancestor commit) held text drafts only; it ran no Lean,
  Lake, cache or package command.
* Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1, `memory.limit_in_bytes`
  9223372036854771712 (no effective limit), in use = usage − total_cache + total_shmem =
  38,019,072 B; headroom = `MemAvailable` 16,445,435,904 B = **15.32 GiB** (floor 4 GiB): PASS.
  Clone filesystem ext4 `/dev/vda`, free 19,097,227,264 B = **17.79 GiB** (floor 12 GiB): PASS.
  Clone, `.lake`, olean tree, cache store and `TMPDIR` (unset → `/tmp`) are all on ext4; no tmpfs.
* Toolchain: Lean 4.25.0 (`leanprover/lean4:v4.25.0`, the pin), real binary
  `/root/.elan/toolchains/leanprover--lean4---v4.25.0/bin/lean`, SHA-256
  `8fadc3ed92cc9decb94c96ee9c0876e91e03a3a5e69138f32114f02789e2766c`, already installed under elan
  on this host. The host has no `/usr/bin/time`; the platform equivalent used everywhere is the
  checker wrapper `tools/chk.py`, which records the child tree's peak RSS from `os.wait4`
  (`ru_maxrss`, KiB), the PID, start/end/elapsed, rc, parsed error count, the source SHA-256, the
  direct prerequisites' object paths and SHA-256 (tree, package build dirs, toolchain library),
  and requires a fresh nonempty object (SHA-256 recorded). Ordinary PATH for every check:
  `/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin`.

### Cache and packages

* Cache store before the fetch (`evidence/logs/cache-store.log`): `/root/.cache/mathlib` existed
  with 3,088 files, 148,719,300 B — archives of earlier fill sessions on this host (E-PAD, S2),
  named by hash; not downloaded by this session.
* Narrowed fetch with **all 389 roots** of `external-bootstrap-r1/mathlib-full-union-roots.txt`
  (`evidence/logs/mathlib-roots.txt`), `TAR_OPTIONS=--no-same-owner lake exe cache get <roots>`
  (`evidence/logs/cache-get.log`): the first Lake command cloned the manifest packages
  (PFR, mathlib, LeanAPAP, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq,
  batteries, Cli) at their pinned revisions; "Attempting to download 523 file(s)", 523/523
  downloaded, "Decompressing 3609 file(s)", "Completed successfully!", exit 0. Run alone.
* Package check (`evidence/logs/packages-check.log`): every present package's origin URL and HEAD
  equal `lake-manifest.json`; ABSENT: `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`; last
  line "RESULT PASS: every present package matches the manifest". Zero-length package oleans:
  none (`zero-oleans.log`). Cache probe `import Mathlib.Algebra.BigOperators.Field` (first root)
  through the checker: PASS, 24.5 s, 1,662 MiB (`cache-probe.log`).

### External PFR route (31 checks) and owner/identity probe

* Reviewed before use: `environment-tools/prepare_pfr.py`, `pfr_lean.py`, the probe source and
  `RUNBOOK.md` (hashes equal the manifest). `prepare_pfr.py` (`evidence/logs/prepare-pfr.log`)
  verified the 31 source hashes/Git blobs, package pins (all present MATCH, four ABSENT), the
  order and PFR options, and created only `<tree>/PFR -> .lake/packages/PFR/PFR` plus the runtime
  config/entry (config SHA-256 `c0dd0079…`, saved as `evidence/logs/pfr-runtime-config.json`);
  `source_aliases_created: false`, `native_execution_performed: false`.
* **31/31 PFR modules PASS** (`evidence/logs/pfr-bootstrap.log`, per-module logs under
  `evidence/logs/modules/.lake/packages/PFR/…`, records in `checks-checkpoint0-env.jsonl`), in
  `external-bootstrap-r1/bootstrap-order.txt` order, one checker invocation each, the adapter
  PATH scoped to that single invocation (`tools/pfr31.sh` → `tools/chk.py --pfr`); 77.4 s total,
  peak 3,057 MiB; loop stops on the first failure (none).
* **Owner/identity probe under ordinary PATH** (`environment-tools/PFRIdentityProbe.source.txt`
  copied byte-identically to `.lake/cleanup-part2-probes/PFRIdentityProbe.lean`): PASS, 37.0 s,
  2,940 MiB, fresh object SHA-256 `dbfe9657…`; all 31 `PFR-MODULE` headers equal; owners
  `KLDiv` ↦ `PFR.Kullback`, `ProbabilityTheory.entropy` ↦ `PFR.ForMathlib.Entropy.Basic`,
  `ProbabilityTheory.uniformOn_apply_singleton_of_mem` ↦ `PFR.Mathlib.Probability.UniformOn`;
  `PFR-MODULES 31; PFR-PRIVATE 0; EOF` (a zero private count, retained as observed).

### Baseline native replay at the ancestor (complete)

* `inputs/orders/root-prerequisites-order.txt` (1,035 modules) in order, then `TCSlib`, then
  `audits/pass-shelat/Checks` (whose 422 prerequisites are a subset), one checker invocation per
  module (`tools/baseline.sh`, `evidence/logs/baseline-build.log`; per-module logs
  `evidence/logs/baseline/modules/…`; records `checks-baseline.jsonl`; summary
  `baseline-summary.json`).
* Disclosed harness corrections: (1) a first attempt was stopped after 85 modules because the
  wrapper's import parser read a docstring line beginning with "import the" as an import; it is
  kept as `baseline-attempt1-INVALID/` and `checks-baseline-attempt1-INVALID.jsonl` and the run
  was restarted from module 1 with a header-only parser. (2) In the restarted run the wrapper's
  prerequisite resolver did not search the toolchain library, so `TCSlib/Complexity/Formulas/CNF`
  (`import Std.Sat.CNF`) and its 79 dependents were recorded `SKIPPED_MISSING_PREREQUISITES` —
  never compiled, never counted; after the fix `tools/baseline_resume.sh` checked exactly those
  80 modules in root order, then the two aggregates (`baseline-build-resume.log`).
* **Result: all 1,035 root prerequisites, `TCSlib` and `audits/pass-shelat/Checks` PASS** (1,119
  records, 1,037 modules, 82 superseded skip records); peak RSS 4,722,988 KiB; 6,008 s of checks;
  slowest `ClassP/BinaryArith/DetMod` 998.8 s. **No E-BASE.** Checks: 111.3 s, 3,765 MiB.

### Baseline source, admission, axiom, C3, closure and seal data

* Lexical admissions at the ancestor (`tools/admissions.py`, `evidence/logs/admissions-baseline.json`):
  510 `sorry` + 1 `sorryAx` (the quoted Name in `Tactics/Haves.lean`), 0 `admit`/`axiom`
  tokens; the 511 occurrences equal `inputs/lexical-admission-occurrences.json` exactly
  (path, line, column, token), each attributed to its enclosing declaration.
* Census probe (`evidence/probes/BaseCensus.source.txt`, importing all 221 owned modules; PASS,
  289.3 s; outputs in `evidence/census/baseline/`, large tables xz-compressed in the payload):
  name table 374,508 constants (`names.tsv`); **axioms of all 19,932 stored constants of the
  221 owned modules** (private/generated/matcher/axiom-free rows included; `axioms.tsv`):
  6,768 `[propext, Classical.choice, Quot.sound]`, 6,301 axiom-free, 4,969 `[propext, Quot.sound]`,
  1,768 `[propext]`, 72 `[Quot.sound]`, 15 `[Classical.choice]`, 10 `[propext, Classical.choice]`,
  **29 with `sorryAx`**; C3 over the same 19,932 roots: 102 foreign generated-equation reference
  pairs (`c3.tsv`); conservative import-closure seal lists for all 221 owned modules from the
  compiled import table (`closure.tsv`). Earlier census attempts 1–3 are retained as INVALID
  (a misplaced generated command and a shadowing error; a stdout-capture stall; a slow
  per-module closure pass, all killed before completion).
* **Baseline whole-file seals** of the 97 consumer files and the provider `ClassNP/PolyTime`
  (planned reader change) at the ancestor (`tools/mkseal.py`, `tools/sealrun.py`;
  `evidence/logs/seal-baseline.json`, `seal-baseline-summary.json`, probes in
  `evidence/probes/seal-baseline-probes.tar.xz`): seal inserted immediately after the imports;
  constant-AST Name requests (exact components), each checked for existence/home/kind,
  installed-status verified, already-irreducible counted separately, EOF marker; **98/98 valid
  harnesses** (no seal-command diagnostic, EOF reached in all); 90,740 requests = 90,031 active +
  709 already irreducible; **501 failing declarations (688 diagnostics) in 80 files; 18 files
  without failure**. No name/home filter: every non-instance, non-reducible definition (matchers
  included) of the TCSlib import closure is sealed; instances and reducible abbreviations (which
  the attribute cannot seal) are the only kinds not requested.
* Explicit-source baseline (`tools/explicit_scan.py`, `evidence/logs/explicit-scan-baseline.json`)
  over the 97 consumer files: 669 foreign TCSlib definition entries (+6 ambiguous) and 98
  Core/Mathlib definition entries in simp/rw/unfold/dsimp/delta lists; 381 of the foreign ones
  have an existing owner reader (`<name>_def`/`_eq`).

## Work state at checkpoint 0

The milestone-1/2 source changes have been drafted (61 owned files: shared block bijection and
readers, `decodeFin_eq_some_iff`, `StateLoop.polyTimeComputable_stateIterate`,
`uexp_le_of_statClose`, `ColSimMachine.polyTimeComputable_next`, `decodeOracleMove` case
readers, the PPT relocation and `NUPPT.ofPolyTime` re-expression, DL10/11/13/14/15/17, E/F/K/L,
G7/G10/G18/G25 and five M keys) but **not yet checked**; they are not in this checkpoint's
patch series (the fill branch has no commit yet; `src/` equals the ancestor).

**Next:** compile the drafted changes serially (milestones 1–2), then the inherited-read batches.

**Ready for review as checkpoint 0 — environment, PFR route and full ancestor baseline validated;
no source change delivered yet (limitation: cleanup work starts at checkpoint 1).**

