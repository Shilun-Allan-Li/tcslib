# DW-10 seal-debt inventory (`dw10-seal-inventory`): checkpoint 1

Lead: Claude (cloud worker). **Checkpoint 1**: see *Scope of this checkpoint* below; the final follows.
The job is checks only: no file under `TCSlib/`, `audits/`, `scripts/` or the lakefile was changed, no Lean branch was created
or committed, no PR was opened; there are no `patches/` or `src/`. Every Lean probe ran through `scripts/lean_check_tree.sh`
(the bootstrap) or `evidence/tools/seal/runner_full.py` (`lean -DmaxErrors=0`, no `-o`).

## Base, pins and environment

| Item | Value |
|---|---|
| Issue base | `f472accd5e000a53d0fbe02b5414435429ce4a70` (an ancestor of the records tip) |
| Lean equality | `git diff --quiet a6d01b1bd1a92e2ac0be9999689467fea7e4e77b f472accd5e000a53d0fbe02b5414435429ce4a70 -- TCSlib TCSlib.lean audits lakefile.lean lake-manifest.json lean-toolchain` exits 0; `TCSlib` tree `06b51ea90a9a0ef49e1dc3e7034ba32ec9b75fe6` at both |
| Records tip used (`cryptography/pass-shelat-ch2-4`) | `cbc44b6e4ff3036860a77cc6a1c3bca0b0d33428`; no `.lean`, `lean-toolchain` or `lake-manifest.json` change after the base. Records pin of the prompt `4367db3c9f3c0b4dd81117ab001e6707aa42c0c5`: `issued-r1/` equals the pack (plus `dispatch.md`); all 21 record hashes of the brief verified |
| Exchange tip used | `d4cfd2f893fb9b448c5d997f037d6ba055cbc031` (the pack: `shasum -a 256 -c SHA256SUMS` 21/21 OK) |
| `main` | `a954201d421a61994e02e36ff3cf4b16dce53f5d` at the start (`workflow.md` §6 read there); `b986b8620fc6117034462212df7070c80a79ff65` after #353 (§4.1 *Lean parallelism*) |
| Toolchain | Lean 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), Lake 5.0.0-src+cdd38ac, installed by elan |
| Mathlib | `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` (manifest); package check: RESULT present=11 mismatches=0 absent=«doc-gen4»,UnicodeBasic,BibtexQuery,MD4Lean |
| Cache | narrowed `lake exe cache get` on the 119 roots (`roots.txt`, recomputed and equal): Attempting to download 2418 file(s) from leanprover-community/mathlib4 cache; Decompressing 2418 file(s); rc=0. Store before the fetch: store: /root/.cache/mathlib; exists: no (0 files, 0 bytes) (all archives fetched by this session). 0 empty oleans; root probe `import Mathlib.Algebra.BigOperators.Field` rc 0 |
| Preflight | nproc 4; cgroup v1 with no memory limit, so headroom = MemAvailable 15.12 GiB (floor 4 GiB); disk 25.32 GiB free on ext4 `/dev/vda` (floor 12 GiB). A first attempt measured 11.39 GiB with the lead's full worktrees (logged with a wrong `PASS` label, annotated in `logs/preflight-attempt1.log`); the lead's own worktrees were made sparse and the preflight re-run passed before any cache or Lean work |
| Bootstrap | `order.txt` (613 modules) one module at a time: TOTAL modules 613; rc!=0 0; errors 0; error_substr 0; sorry warnings 22 in 9 modules (base-sorries.txt: 22 in 9, per-module counts equal); every source equals `SOURCE-SHA256SUMS` (`build/summary.txt`) |
| Olean tree | 613 `.olean`, map `build/olean-tree-map.txt`, SHA-256 `99979c3d2053e6b9f7c74c23c397fe426bacff0a8a8f46a49535fb10f7b35a41`; made read-only (uid 0 bypasses the mode bits: `build/readonly-note.txt`); restore check: (at the final) |

## Parallelism (user override and ruling, 2026-11-17)

The brief's "one Lean process at a time on the host, through one lock" was overridden by the user during the run ("I'm overriding
the 'one Lean process at a time on the host' rule ... Be mindful of making sure each Lean process has enough memory"), then by
Seyoon's ruling (`workflow.md` §4.1 *Lean parallelism*, main #353): cloud workers run a pool of at most nproc Lean processes,
keeping about 2 GB (15%) available. Before the override, the bootstrap, the collectors, the scan kinds probes, the locator, the
first 12 seal probes and the first controls pretest ran strictly one at a time. Afterwards the seals ran in a pool of 4 workers
(lock slots w1..w4 as the counting semaphore; claim files so no probe runs twice; a probe starts only when MemAvailable is at least
4.5 GiB): `seals/PARALLEL.txt`. Measured (30 s samples, `logs/memsample.log`): at most 4 Lean processes at once, minimum
MemAvailable 12.6 GiB, peak private (anonymous) memory of one Lean process 518 MiB, peak RSS
3.20 GiB (mostly shared olean mappings). The running seal phase was not interrupted to switch over (the ruling's
instruction); the pool is recorded per phase in `seals/PARALLEL.txt`.

## Who did what

- **Lead (Claude, cloud):** everything at this checkpoint: preflight, toolchain, cache, bootstrap and tree map, the collectors and
  owner check, the item location, the scan, the seal generation, the seal runs (one process, then the parallel pool of four
  workers after the user's override), the controls, the reader index, the reconciliation and this report.
- **Sub-agents:** none has run yet. Lean is no longer the bottleneck since the parallelism ruling, so sub-agents are planned only
  for the classification review of the open items (A: SecureComputation, ZeroKnowledge; B: Encryption, Authentication, Games,
  Hashing, Randomness, Implications, Pseudorandom), analysis-only, with their logs under `evidence/subagents/<name>/`.


## Method and tool changes

The suite is the bb1-sim adaptation (exchange `d929cc21ec817b2518d57a7262e42744728f029a`, tree `e25f7bf0c9b78e764917868ad52a5f4044d0dcd2`) and
DW-5's (`dw5-evidence.zip`, `12abc05a…`, verified), copied into `evidence/tools/`; every change is recorded in the tool's header.
The archived Gate 06/10 instrumenter (`seal/review/archived-gate10-tools/`) is unmodified (`archived-gate10-tools.SHA256SUMS`).
- **Collectors** (`collect/b1..b5`, 87/87/87/87/86 owners in build order, `collect/batches.tsv`): `NmCollect.template.lean`
  adapted to add COEINST records (the one coercion instance found is `TCSlib.InformationTheory.FinDist.instCoeFunForallReal`),
  ROOT flags and own-module type references (owner check, controls) and ROOT `eqn_refs` (check 5). All rc 0, 0 errors.
- **Seals**: `mkseals_ab.py` / `mkseals_coe.py` unchanged, `SEAL_CHUNK=2000` for every probe. Variant deduplication
  (`tools/qbuild.py`): coe-A always runs; strict-A when its bytes differ from coe-A; B when it differs from A after the label
  normalization `SealB_` -> `SealA_` (the labels differ by construction, so byte equality is checked after that normalization; both
  SHA-256 values are in `seals/dedup.json`). Request counts reproduce the recorded ones exactly (IterateFind 595, ModuleHost 241,
  IterateFindHost 251, Yao coe-A 3,046). `tools/sealtab.py` maps every error to its source line and declaration and checks
  every install/EOF record (requested = verified, summed over chunk parts).
- **Scan**: `scan1_g40.py` + archived `scan_explicit.py` + `scan2.py` unchanged, `touched.py` with the empty tree as base (every
  declaration touched). The kinds probe of batch b2 overflowed Lean's stack (137k candidate names in one string literal, rc 134;
  kept as `scan/b2-attempt1/`); b2 ran as b2a/b2b. The archived lexer inventories `unfold`, `delta`, `rw`/`rwa`/`erw`/`nth_rw`,
  the `simp` family, `norm_num`, `field_simp`, `push_cast`; `show`/`change` reads are definitional and are caught by the seals
  (DW10-W4).
- **Item location** (`locate/`): every input item's name resolved in the elaborated environment (handed-off files included):
  {'confirmed': 1770, 'not-found': 9}; the 9 not found are exactly the NO-DECLARATION rows (attempt 1 queried private names verbatim; kept).
- **Generated-equation reads** (`eqrefs.tsv`): from the collectors' `eqn_refs` (`eq_<n>`, `eq_def`, `eq_unfold`, `splitter`).
- **Controls** (`controls/`): `tools/mkctl_dw10.py`, one pair per owner, 20 harnesses of up to 25 owners, unsealed pretest first
  (attempt 1 stopped after a 48-minute unbounded `rfl`; attempt 2 bounds every control body by `maxHeartbeats 400000`).
- **Reader index** (`readers/`): every TCSlib theorem `<P>_*` (or lower-camel) whose type mentions a definition P; the classification
  uses as published readers `_eq`, `_def`, `_apply`, `_iff`, `_eq_def` and run/contract lemmas.
- **Reconciliation** (`tools/reconcile.py`, matching rules in its header) and the report (`tools/report_tables.py`, this file).

## Owner check (Checks, step 2)

```
# Owner check (brief, Checks step 2), dw10-seal-inventory, from the five collectors at base f472accd5e000a53d0fbe02b5414435429ce4a70
owners checked: 434; owners.txt decls == static scanner (derivation/leanindex.py at the base): 434/434
static declarations: 9954; collector source-level declarations: 10269; stored constants (all, incl. generated): 16208
COLLECTOR_NOT_IN_STATIC	generated def (deriving, structural recursion, enum)	17
COLLECTOR_NOT_IN_STATIC	generated def (notation/syntax declaration)	11
COLLECTOR_NOT_IN_STATIC	generated theorem (congr_simp, brecOn.eq)	124
COLLECTOR_NOT_IN_STATIC	generated theorem (simps projection lemma)	162
COLLECTOR_NOT_IN_STATIC	instance (deriving / anonymous instance; static blind spot)	23
STATIC_NOT_IN_COLLECTOR	static @[ext] structure lemma name (filtered as generated ext)	2
UNEXPLAINED (OTHER): 0
Campaign files missed by the derivation (origins.tsv: created by a pass-shelat PR other than #186/#280, or the 2026-10-28 direct commit, and not in owners.txt/list-only.txt): 0
Conclusion: no owner differs from owners.txt beyond the static scanner's known blind spots; no owner-set question is raised.
```

## Scope of this checkpoint

Checkpoint 1 (brief: "the bootstrap, all collectors, and the seals and scan of every owner that holds an input item"):
- done for all 434 owners: the bootstrap (613 modules), the five collectors, the owner check, the item location, the
  explicit-unfold scan, the generated-equation extraction and the reader index;
- seals (all four variants, deduplicated) done for the 96 owners that hold an input item (the 91 owners with
  `ledger_items_at_base` > 0 and the 5 owners of `named-findings.tsv`, 96 together), plus every further owner the four workers finished
  before the snapshot; `seals.tsv` marks every other owner-variant `NOT_RUN`;
- `inventory.tsv` gives every one of the 1,779 input rows a status (608 HANDED-OFF from the records); classes are the tool's
  first assessment (`tools/reconcile.py`), to be reviewed for the final; NEW rows are listed for the sealed owners and the scan
  (all owners) only, so NEW seal rows are incomplete at this checkpoint;
- the controls (20 harnesses, strict and coe, with their unsealed pretest) are running; their table comes with the final;
- remaining for the final: the seals of the other owners, the controls, the classification review, the tree restore check and
  the complete evidence.


## Totals and lists

### Seals

Owners sealed (all four variants recorded): 102 of 434. Probes: 1736 owner-variants, 347 run, 63 deduplicated (identical probe bytes, or identical after the SealA_/SealB_ label normalization).

| variant | owners | requests (sum) | requests (max) | failing owners | failing declarations | errors | failing decls by tier | install/EOF incomplete |
|---|---|---|---|---|---|---|---|---|
| strict-A | 103 | 109627 | 3047 | 55 | 240 | 345 | T1 233 / T2 7 | 0 |
| strict-B | 102 | 109129 | 3048 | 72 | 369 | 563 | T1 362 / T2 7 | 0 |
| coe-A | 103 | 109540 | 3046 | 52 | 233 | 330 | T1 230 / T2 3 | 0 |
| coe-B | 102 | 109042 | 3047 | 69 | 362 | 548 | T1 359 / T2 3 | 0 |

### Explicit-unfold scan

Items: 36127; foreign TCSlib definition items 135 (T1 133, T2 2); by kind: THEOREM/theorem 26796, LOCAL_OR_UNRESOLVED/None 6673, OWNED_DEFINITION/semireducible 2449, FOREIGN_TCSLIB_DEFINITION/semireducible 135, SIMPROC/semireducible 42, FOREIGN_CORE_MATHLIB_DEFINITION/semireducible 19, OWNED_DEFINITION/irreducible 10, FOREIGN_CORE_MATHLIB_DEFINITION/reducible 2, OWNED_DEFINITION/abbrev 1

### Status by source

| source | HANDED-OFF | FIXED_SINCE | STILL_OPEN | CHANGED | NEW | NOT_CHECKED | total |
|---|---|---|---|---|---|---|---|
| #248-historical | 9 | 603 | 106 | 46 | 0 | 0 | 764 |
| #248-current | 437 | 35 | 285 | 56 | 0 | 0 | 813 |
| provider-pair | 102 | 0 | 21 | 1 | 0 | 0 | 124 |
| SG-F07 | 0 | 0 | 9 | 0 | 0 | 0 | 9 |
| SY-F07 | 2 | 0 | 9 | 0 | 0 | 0 | 11 |
| C-F02 | 58 | 0 | 0 | 0 | 0 | 0 | 58 |
| new | 0 | 0 | 0 | 0 | 229 | 0 | 229 |
| total | 608 | 638 | 430 | 103 | 229 | 0 | 2008 |

### Class by tier (open items)

| tier | STAGE2 | STAGE2-PROVIDER-READER | SEAL-B-ONLY | STRICT-ONLY (notation, no fix) | STATEMENT |
|---|---|---|---|---|---|
| T1 | 553 | 2 | 134 | 4 | 42 |
| T2 | 13 | 0 | 0 | 5 | 0 |

### Named findings against their records

| finding | rows | statuses |
|---|---|---|
| SG-F07 | 9 | STILL_OPEN 9 |
| SY-F07 | 11 | HANDED-OFF 2, STILL_OPEN 9 |
| C-F02 | 58 | HANDED-OFF 58 |

### Stage 2 fix list, by file

**TCSlib/Complexity/ClassP/BinaryArith/Unary.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:1 | `<outside src:37>` | first error l.37: failed to set X, X is currently X, X expected; providers Complexity.Poly | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| NEW:2 | `<outside src:38>` | first error l.38: failed to set X, X is currently X, X expected; providers Turing.pairEnco | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |

**TCSlib/Complexity/Randomized/Build/IterateFind.lean** (23 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:3 | `Complexity.IterateFind.computesFunInTime_find` | first error l.602: Unknown constant X | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0051 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.359: Unknown constant `Turing.FinTM.State | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0052 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.359: Invalid dotted identifier notation:  | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0053 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.377: Application type mismatch: The argum | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0054 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.379: Type mismatch (#248 inherited_reache | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0055 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.386: Application type mismatch: The argum | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0056 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.387: Type mismatch (#248 inherited_reache | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0057 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.430: Application type mismatch: The argum | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0058 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.431: Type mismatch (#248 inherited_reache | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0059 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.536: Tactic `introN` failed: There are no | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0060 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.552: Invalid `⟨...⟩` notation: The expect | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| SEAL-0061 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.553: No goals to be solved (#248 inherite | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0051 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0051 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0052 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0052 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0053 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0053 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0054 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0054 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0055 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0055 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0056 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0056 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0057 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0057 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0058 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0058 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0059 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0059 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0060 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0060 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |
| EFF72:SEAL-0061 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0061 Complexity.IterateFind.polyTimeComputable_find (home at rulin | use Complexity.IterateFind.hostCtrl_eq (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean) | #347 |

**TCSlib/Complexity/Randomized/Build/IterateFindHost.lean** (26 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:128 | `Complexity.IterateFind.copy_clean` | 219 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:129 | `Complexity.IterateFind.copy_clean` | 219 simp Turing.stateWord | use Turing.stateWord_eq (TCSlib/Complexity/TuringMachine/Build/Loop.lean) | - |
| NEW:130 | `Complexity.IterateFind.copy_clean` | 246 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:131 | `Complexity.IterateFind.copy_clean` | 248 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:132 | `Complexity.IterateFind.copy_clean` | 248 simp Turing.stateWord | use Turing.stateWord_eq (TCSlib/Complexity/TuringMachine/Build/Loop.lean) | - |
| NEW:133 | `Complexity.IterateFind.copy_clean` | 250 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:135 | `Complexity.IterateFind.copy_finish` | 189 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:136 | `Complexity.IterateFind.copy_finish` | 196 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:137 | `Complexity.IterateFind.copy_finish` | 199 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:138 | `Complexity.IterateFind.copy_finish` | 201 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:139 | `Complexity.IterateFind.copy_rewind` | 162 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:140 | `Complexity.IterateFind.copy_rewind` | 169 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:141 | `Complexity.IterateFind.copy_rewind` | 173 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:142 | `Complexity.IterateFind.copy_rewind` | 175 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:143 | `Complexity.IterateFind.copy_step` | 100 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:144 | `Complexity.IterateFind.copy_step` | 108 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:145 | `Complexity.IterateFind.copy_step` | 111 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:146 | `Complexity.IterateFind.copy_step` | 115 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:147 | `Complexity.IterateFind.copy_turn` | 129 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:148 | `Complexity.IterateFind.copy_turn` | 136 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:149 | `Complexity.IterateFind.copy_turn` | 140 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:150 | `Complexity.IterateFind.copy_turn` | 142 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:151 | `Complexity.IterateFind.host_branch` | 342 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:152 | `Complexity.IterateFind.host_branch` | 342 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:153 | `Complexity.IterateFind.host_branch` | 342 simp Turing.stateWord | use Turing.stateWord_eq (TCSlib/Complexity/TuringMachine/Build/Loop.lean) | - |
| NEW:154 | `Complexity.IterateFind.host_branch` | 342 simp Turing.FinTM.bufferTape | use Turing.FinTM.bufferTape_eq (TCSlib/Complexity/TuringMachine/Simulation.lean) | - |

**TCSlib/Complexity/Randomized/Build/PairSplit.lean** (54 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:155 | `Turing.FinTM.split_computes` | 643 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:156 | `Turing.FinTM.split_computes` | 643 simp Turing.Cfg.init | use Turing.Cfg.init_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:4 | `Turing.FinTM.split_copy` | first error l.401: Application type mismatch: The argument; providers Turing.Action.apply, | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:157 | `Turing.FinTM.split_copy` | 396 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:158 | `Turing.FinTM.split_copy` | 399 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:159 | `Turing.FinTM.split_copy` | 402 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:160 | `Turing.FinTM.split_copy` | 408 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:161 | `Turing.FinTM.split_copy` | 415 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:162 | `Turing.FinTM.split_dbl_append` | 341 simp Turing.dbl | use Turing.dbl_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:5 | `Turing.FinTM.split_run` | first error l.585: 'change' tactic failed, pattern; providers Turing.Action.apply,Turing.A | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:163 | `Turing.FinTM.split_run` | 578 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:164 | `Turing.FinTM.split_run` | 581 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:165 | `Turing.FinTM.split_run` | 581 simp Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:166 | `Turing.FinTM.split_run` | 588 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:167 | `Turing.FinTM.split_run` | 591 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:168 | `Turing.FinTM.split_run` | 591 simp Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:169 | `Turing.FinTM.split_run` | 606 simpa Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:170 | `Turing.FinTM.split_run` | 610 simpa Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:171 | `Turing.FinTM.split_run` | 620 simpa Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:172 | `Turing.FinTM.split_run` | 624 simp Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:6 | `Turing.FinTM.split_sep` | first error l.440: Application type mismatch: The argument; providers Turing.Action.apply, | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:173 | `Turing.FinTM.split_sep` | 434 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:174 | `Turing.FinTM.split_sep` | 441 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:175 | `Turing.FinTM.split_sep` | 443 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:176 | `Turing.FinTM.split_sep` | 446 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:177 | `Turing.FinTM.split_sep` | 449 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:178 | `Turing.FinTM.split_sep` | 452 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:179 | `Turing.FinTM.split_sep` | 455 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:180 | `Turing.FinTM.split_sep` | 456 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:7 | `Turing.FinTM.split_tail` | first error l.476: Application type mismatch: The argument; providers Turing.Action.apply, | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:181 | `Turing.FinTM.split_tail` | 471 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:182 | `Turing.FinTM.split_tail` | 477 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:183 | `Turing.FinTM.split_tail` | 478 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:184 | `Turing.FinTM.split_tail` | 479 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:185 | `Turing.FinTM.split_tail` | 485 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:186 | `Turing.FinTM.split_tail` | 493 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:8 | `Turing.PairParse.apply_cfg_advance` | first error l.148: Application type mismatch: The argument; providers Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:9 | `Turing.PairParse.apply_cfg_stay` | first error l.137: Application type mismatch: The argument; providers Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:10 | `Turing.PairParse.cfg_workTapeSymbols` | first error l.126: Type mismatch; providers Turing.Cfg.workTapeSymbols,Turing.FinTM.buffer | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:11 | `Turing.PairParse.parse_block` | first error l.195: 'change' tactic failed, pattern; providers Turing.MultiTapeTM.runFrom,T | use Turing.MultiTapeTM.runFrom_zero (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:188 | `Turing.PairParse.parse_block` | 197 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:189 | `Turing.PairParse.parse_block` | 210 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:12 | `Turing.PairParse.parse_first` | first error l.165: Application type mismatch: The argument; providers Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:190 | `Turing.PairParse.parse_first` | 160 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:191 | `Turing.PairParse.parse_first` | 167 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:13 | `Turing.PairParse.rewind_run` | first error l.235: Application type mismatch: The argument; providers Turing.Action.apply, | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:192 | `Turing.PairParse.rewind_run` | 233 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:193 | `Turing.PairParse.rewind_run` | 234 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:194 | `Turing.PairParse.rewind_run` | 236 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:195 | `Turing.PairParse.rewind_run` | 237 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:196 | `Turing.PairParse.rewind_run` | 244 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_output (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:197 | `Turing.PairParse.rewind_run` | 245 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:198 | `Turing.PairParse.rewind_run` | 248 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:199 | `Turing.PairParse.rewind_run` | 249 simp Turing.Action.apply | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |

**TCSlib/Complexity/Randomized/Build/UnaryMul.lean** (19 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:14 | `Turing.FinTM.exists_unaryMulTM` | first error l.409: Application type mismatch: The argument; providers Turing.FinTM.Compute | use Turing.FinTM.computesFunInTime_iff (TCSlib/Complexity/TuringMachine/Finite.lean) | - |
| NEW:15 | `Turing.FinTM.mul_back` | first error l.159: Application type mismatch: The argument | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| NEW:200 | `Turing.FinTM.mul_computes` | 369 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:201 | `Turing.FinTM.mul_computes` | 369 simp Turing.Cfg.init | use Turing.Cfg.init_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:202 | `Turing.FinTM.mul_computes` | 370 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:203 | `Turing.FinTM.mul_computes` | 370 simp Turing.Cfg.init | use Turing.Cfg.init_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:204 | `Turing.FinTM.mul_computes` | 371 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:205 | `Turing.FinTM.mul_computes` | 371 simp Turing.Cfg.init | use Turing.Cfg.init_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:206 | `Turing.FinTM.mul_computes` | 372 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:207 | `Turing.FinTM.mul_computes` | 372 simp Turing.Cfg.init | use Turing.Cfg.init_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:208 | `Turing.FinTM.mul_computes` | 373 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:209 | `Turing.FinTM.mul_computes` | 373 simp Turing.Cfg.init | use Turing.Cfg.init_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:16 | `Turing.FinTM.mul_run` | first error l.304: 'change' tactic failed, pattern; providers Turing.MultiTapeTM.runFrom,T | use Turing.MultiTapeTM.runFrom_zero (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:210 | `Turing.FinTM.mul_run` | 300 simp Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:211 | `Turing.FinTM.mul_run` | 308 simp Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:212 | `Turing.FinTM.mul_run` | 326 simpa Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:213 | `Turing.FinTM.mul_run` | 330 simpa Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:214 | `Turing.FinTM.mul_run` | 346 simpa Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| NEW:215 | `Turing.FinTM.mul_run` | 350 simp Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |

**TCSlib/Complexity/Randomized/Primitives.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:18 | `Complexity.polyTimeComputable_unaryMulFun` | first error l.138: Invalid X notation: The expected type; providers Complexity.PolyTimeCom | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| NEW:20 | `Turing.FinTM.computesFunInTime_unaryMul` | first error l.120: Application type mismatch: The argument; providers Turing.pairDecode | use Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |

**TCSlib/Complexity/Randomized/SeedMajority/Enumeration.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:216 | `Complexity.SeedMajority.exists_countingTM` | 71 simp Complexity.P | use Complexity.P_def (TCSlib/Complexity/ClassP/P.lean) | - |

**TCSlib/Complexity/Randomized/UnaryPolynomial.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:21 | `<outside src:38>` | first error l.38: failed to set X, X is currently X, X expected; providers Turing.FinTM.Co | use Turing.FinTM.computesFunInTime_iff (TCSlib/Complexity/TuringMachine/Finite.lean) | - |

**TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean** (20 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0090 | `Turing.ModuleHost.clean_emit` | Turing.ModuleHost.clean_emit l.345: Tactic `rcases` failed: `hf : PolyTimeComputable f` is | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| EFF72:SEAL-0090 | `Turing.ModuleHost.clean_emit` | efficiency-72 pair SEAL-0090 Turing.ModuleHost.clean_emit (home at ruling TCSlib.Complexit | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0089 | `Turing.ModuleHost.clean_install` | Turing.ModuleHost.clean_install l.321: Tactic `rcases` failed: `hf : PolyTimeComputable f` | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| EFF72:SEAL-0089 | `Turing.ModuleHost.clean_install` | efficiency-72 pair SEAL-0089 Turing.ModuleHost.clean_install (home at ruling TCSlib.Comple | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0095 | `Turing.ModuleHost.host_call` | Turing.ModuleHost.host_call l.537: Type mismatch: After simplification, term (#248 inherit | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| EFF72:SEAL-0095 | `Turing.ModuleHost.host_call` | efficiency-72 pair SEAL-0095 Turing.ModuleHost.host_call (home at ruling TCSlib.Complexity | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| SEAL-0094 | `Turing.ModuleHost.host_seam` | Turing.ModuleHost.host_seam l.499: Application type mismatch: The argument (#248 inherited | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| EFF72:SEAL-0094 | `Turing.ModuleHost.host_seam` | efficiency-72 pair SEAL-0094 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| SEAL-0091 | `Turing.ModuleHost.pad_apply` | Turing.ModuleHost.pad_apply l.393: Application type mismatch: The argument (#248 inherited | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| EFF72:SEAL-0091 | `Turing.ModuleHost.pad_apply` | efficiency-72 pair SEAL-0091 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| SEAL-0092 | `Turing.ModuleHost.pad_run` | Turing.ModuleHost.pad_run l.417: 'change' tactic failed, pattern (#248 inherited_same_step | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| EFF72:SEAL-0092 | `Turing.ModuleHost.pad_run` | efficiency-72 pair SEAL-0092 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| SEAL-0093 | `Turing.ModuleHost.pad_seam` | Turing.ModuleHost.pad_seam l.426: Application type mismatch: The argument (#248 inherited_ | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| EFF72:SEAL-0093 | `Turing.ModuleHost.pad_seam` | efficiency-72 pair SEAL-0093 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| SEAL-0087 | `Turing.ModuleHost.stop_clean` | Turing.ModuleHost.stop_clean l.184: Tactic `rfl` failed: The left-hand side (#248 inherite | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| SEAL-0088 | `Turing.ModuleHost.stop_clean` | Turing.ModuleHost.stop_clean l.193: Type mismatch (#248 inherited_same_step_after_other_re | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| EFF72:SEAL-0087 | `Turing.ModuleHost.stop_clean` | efficiency-72 pair SEAL-0087 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| EFF72:SEAL-0088 | `Turing.ModuleHost.stop_clean` | efficiency-72 pair SEAL-0088 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| SEAL-0086 | `Turing.ModuleHost.stop_step` | Turing.ModuleHost.stop_step l.161: Tactic `rfl` failed: The left-hand side (#248 inherited | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| EFF72:SEAL-0086 | `Turing.ModuleHost.stop_step` | efficiency-72 pair SEAL-0086 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Action.apply_state (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |

**TCSlib/Complexity/TuringMachine/Build/WordTiming.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:22 | `<outside src:33>` | first error l.33: failed to set X, X is currently X, X expected; providers Turing.FinTM.Co | use Turing.FinTM.computesFunInTime_iff (TCSlib/Complexity/TuringMachine/Finite.lean) | - |
| NEW:23 | `<outside src:34>` | first error l.34: failed to set X, X is currently X, X expected; providers Turing.pairEnco | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |

**TCSlib/Cryptography/Asymptotic/Collections.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:33 | `TCSlib.Cryptography.FunFamily.toCollection_sampleClose` | TCSlib.Cryptography.FunFamily.toCollection_sampleClose (lines 563; #248 OPEN_TYPED_COINS) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0183 | `TCSlib.Cryptography.FunFamily.toCollection_sampleClose` | TCSlib.Cryptography.FunFamily.toCollection_sampleClose l.564: Type mismatch (#248 inherite | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |

**TCSlib/Cryptography/Asymptotic/Ensembles.lean** (20 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:49 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies (lines 516, 551, 582, 585; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0189 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies l.524: typeclass instance problem is stuck, it  | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0190 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies l.559: unsolved goals (#248 inherited_same_step | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0191 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies l.591: Application type mismatch: The argument  | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0192 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies l.594: Type mismatch (#248 inherited_same_step_ | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:45 | `TCSlib.Cryptography.Ensemble.Indist.symm` | TCSlib.Cryptography.Ensemble.Indist.symm (lines 334; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0185 | `TCSlib.Cryptography.Ensemble.Indist.symm` | TCSlib.Cryptography.Ensemble.Indist.symm l.342: Type mismatch (#248 inherited_same_native_ | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:48 | `TCSlib.Cryptography.Ensemble.Indist.trans` | TCSlib.Cryptography.Ensemble.Indist.trans (lines 459; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0188 | `TCSlib.Cryptography.Ensemble.Indist.trans` | TCSlib.Cryptography.Ensemble.Indist.trans l.467: Application type mismatch: The argument ( | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:46 | `TCSlib.Cryptography.Ensemble.IndistLit.toIndist` | TCSlib.Cryptography.Ensemble.IndistLit.toIndist (lines 403; #248 OPEN_TYPED_COINS) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0186 | `TCSlib.Cryptography.Ensemble.IndistLit.toIndist` | TCSlib.Cryptography.Ensemble.IndistLit.toIndist l.411: Type mismatch (#248 inherited_same_ | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| H:44 | `TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible` | TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible (lines 273; #248 OPEN_INCOMPLETE | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0184 | `TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible` | TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible l.281: Type mismatch (#248 inher | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:47 | `TCSlib.Cryptography.hybrid_lemma` | TCSlib.Cryptography.hybrid_lemma (lines 447; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0187 | `TCSlib.Cryptography.hybrid_lemma` | TCSlib.Cryptography.hybrid_lemma l.455: Application type mismatch: The argument (#248 inhe | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:50 | `TCSlib.Cryptography.predict_eq` | TCSlib.Cryptography.predict_eq (lines 629; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0193 | `TCSlib.Cryptography.predict_eq` | TCSlib.Cryptography.predict_eq l.638: Tactic `rfl` failed: The left-hand side (#248 inheri | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:51 | `TCSlib.Cryptography.prediction_lemma` | TCSlib.Cryptography.prediction_lemma (lines 662, 668; #248 OPEN_INCOMPLETE) | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0194 | `TCSlib.Cryptography.prediction_lemma` | TCSlib.Cryptography.prediction_lemma l.671: typeclass instance problem is stuck, it is oft | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0195 | `TCSlib.Cryptography.prediction_lemma` | TCSlib.Cryptography.prediction_lemma l.677: Type mismatch (#248 inherited_same_native_step | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |

**TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean** (8 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0196 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_equiv` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_equiv l.82: Type mismatch (#248 inheri | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0197 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_fst` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_fst l.89: Type mismatch (#248 inherite | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0204 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_multicopyRed_congr` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_multicopyRed_congr l.501: Type mismatch (#24 | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0205 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_multicopyRed_congr` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_multicopyRed_congr l.506: Type mismatch (#24 | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0199 | `TCSlib.Cryptography.EnsembleLemmas.distAdv_eq_zero_of_subsingleton` | TCSlib.Cryptography.EnsembleLemmas.distAdv_eq_zero_of_subsingleton l.128: Application type | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0206 | `TCSlib.Cryptography.EnsembleLemmas.exists_copiesRed` | TCSlib.Cryptography.EnsembleLemmas.exists_copiesRed l.806: Tactic `rfl` failed: The left-h | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0202 | `TCSlib.Cryptography.EnsembleLemmas.exists_pushRed` | TCSlib.Cryptography.EnsembleLemmas.exists_pushRed l.309: Application type mismatch: The ar | use Complexity.NUPPT.combineAdvice_nil (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0198 | `TCSlib.Cryptography.EnsembleLemmas.statClose_of_subsingleton` | TCSlib.Cryptography.EnsembleLemmas.statClose_of_subsingleton l.118: Tactic `introN` failed | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:217 | `TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc` | 105 simp TCSlib.Cryptography.uexp | use TCSlib.Cryptography.uexp_def (TCSlib/Cryptography/Foundations/Probability.lean) | - |

**TCSlib/Cryptography/Asymptotic/HardCore/Functions.lean** (12 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:71 | `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad` | TCSlib.Cryptography.FunFamily.StrongOneWay.glPad (lines 815; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.glPadInvMachine_eq (or _iff/_apply) in TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean; related: TCSlib.Cryptography.glPadInvMachine_runAt | - |
| SEAL-0232 | `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad` | TCSlib.Cryptography.FunFamily.StrongOneWay.glPad l.827: Type mismatch (#248 inherited_reac | add TCSlib.Cryptography.glPadInvMachine_eq (or _iff/_apply) in TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean; related: TCSlib.Cryptography.glPadInvMachine_runAt | - |
| H:72 | `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore` | TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore (lines 874, 874; #248 OPEN_INCOM | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0233 | `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore` | TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore l.897: Type mismatch (#248 inher | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:69 | `TCSlib.Cryptography.FunFamily.glBit_append` | TCSlib.Cryptography.FunFamily.glBit_append (lines 742; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.HardcoreBit.glBit_eq (or _iff/_apply) in TCSlib/Cryptography/HardcoreBit/InnerProduct.lean | - |
| SEAL-0230 | `TCSlib.Cryptography.FunFamily.glBit_append` | TCSlib.Cryptography.FunFamily.glBit_append l.744: Tactic `rfl` failed: The left-hand side  | add TCSlib.Cryptography.HardcoreBit.glBit_eq (or _iff/_apply) in TCSlib/Cryptography/HardcoreBit/InnerProduct.lean | - |
| H:68 | `TCSlib.Cryptography.FunFamily.glPad_f` | TCSlib.Cryptography.FunFamily.glPad_f (lines 735; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.HardcoreBit.glPad_apply (TCSlib/Cryptography/HardcoreBit/InnerProduct.lean) | - |
| SEAL-0229 | `TCSlib.Cryptography.FunFamily.glPad_f` | TCSlib.Cryptography.FunFamily.glPad_f l.737: Tactic `rfl` failed: The left-hand side (#248 | use TCSlib.Cryptography.HardcoreBit.glPad_apply (TCSlib/Cryptography/HardcoreBit/InnerProduct.lean) | - |
| H:70 | `TCSlib.Cryptography.FunFamily.glPad_f_bijective` | TCSlib.Cryptography.FunFamily.glPad_f_bijective (lines 792; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.HardcoreBit.glPad_apply (TCSlib/Cryptography/HardcoreBit/InnerProduct.lean) | - |
| SEAL-0231 | `TCSlib.Cryptography.FunFamily.glPad_f_bijective` | TCSlib.Cryptography.FunFamily.glPad_f_bijective l.795: Tactic `rfl` failed: The left-hand  | use TCSlib.Cryptography.HardcoreBit.glPad_apply (TCSlib/Cryptography/HardcoreBit/InnerProduct.lean) | - |
| H:62 | `TCSlib.Cryptography.not_hardCore_const` | TCSlib.Cryptography.not_hardCore_const (lines 263, 267, 267; #248 OPEN_INCOMPLETE) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0220 | `TCSlib.Cryptography.not_hardCore_const` | TCSlib.Cryptography.not_hardCore_const l.264: typeclass instance problem is stuck, it is o | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |

**TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:74 | `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` | TCSlib.Cryptography.Collection.OneWay.glPad_hardCore (lines 355, 356; #248 OPEN_INCOMPLETE | use TCSlib.Cryptography.Collection.hardCore_iff (TCSlib/Cryptography/Asymptotic/Collections.lean) | - |
| SEAL-0236 | `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` | TCSlib.Cryptography.Collection.OneWay.glPad_hardCore l.356: Invalid `⟨...⟩` notation: The  | use TCSlib.Cryptography.Collection.hardCore_iff (TCSlib/Cryptography/Asymptotic/Collections.lean) | - |
| SEAL-0237 | `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` | TCSlib.Cryptography.Collection.OneWay.glPad_hardCore l.357: No goals to be solved (#248 in | use TCSlib.Cryptography.Collection.hardCore_iff (TCSlib/Cryptography/Asymptotic/Collections.lean) | - |
| H:73 | `TCSlib.Cryptography.Collection.glPad_sample_runAtL` | TCSlib.Cryptography.Collection.glPad_sample_runAtL (lines 178, 175; #248 OPEN_TYPED_COINS) | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| SEAL-0234 | `TCSlib.Cryptography.Collection.glPad_sample_runAtL` | TCSlib.Cryptography.Collection.glPad_sample_runAtL l.178: Function expected at (#248 inher | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| SEAL-0235 | `TCSlib.Cryptography.Collection.glPad_sample_runAtL` | TCSlib.Cryptography.Collection.glPad_sample_runAtL l.175: unsolved goals (#248 inherited_s | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| H:75 | `TCSlib.Cryptography.PermCollection.OneWay.glPad` | TCSlib.Cryptography.PermCollection.OneWay.glPad (lines 419; #248 OPEN_INCOMPLETE) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0238 | `TCSlib.Cryptography.PermCollection.OneWay.glPad` | TCSlib.Cryptography.PermCollection.OneWay.glPad l.420: Application type mismatch: The argu | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| H:76 | `TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore` | TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore (lines 425; #248 OPEN_INCOMPLETE) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0239 | `TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore` | TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore l.426: Application type mismatch: | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| H:77 | `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad` | TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad (lines 483; #248 OPEN_INCOMPLETE) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0240 | `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad` | TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad l.484: Application type mismatch: The  | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| H:78 | `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore` | TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore (lines 492; #248 OPEN_INCOMPL | use TCSlib.Cryptography.Collection.hardCore_iff (TCSlib/Cryptography/Asymptotic/Collections.lean) | - |
| SEAL-0241 | `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore` | TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore l.493: Application type misma | use TCSlib.Cryptography.Collection.hardCore_iff (TCSlib/Cryptography/Asymptotic/Collections.lean) | - |

**TCSlib/Cryptography/Asymptotic/HardCoreGL.lean** (8 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:79 | `TCSlib.Cryptography.GLLoop.orbit_eq` | TCSlib.Cryptography.GLLoop.orbit_eq (lines 368; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.SelXor.input_eq (or _iff/_apply) in TCSlib/Cryptography/Asymptotic/HardCoreLoops.lean | - |
| SEAL-0242 | `TCSlib.Cryptography.GLLoop.orbit_eq` | TCSlib.Cryptography.GLLoop.orbit_eq l.370: Type mismatch (#248 inherited_same_step_after_o | add TCSlib.Cryptography.SelXor.input_eq (or _iff/_apply) in TCSlib/Cryptography/Asymptotic/HardCoreLoops.lean | - |
| H:81 | `TCSlib.Cryptography.glMachine_runAt` | TCSlib.Cryptography.glMachine_runAt (lines 752; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.HardcoreBit.majority_def (TCSlib/Cryptography/HardcoreBit/PairwiseIndependence.lean) | - |
| SEAL-0244 | `TCSlib.Cryptography.glMachine_runAt` | TCSlib.Cryptography.glMachine_runAt l.755: Tactic `rewrite` failed: Did not find an occurr | use TCSlib.Cryptography.HardcoreBit.majority_def (TCSlib/Cryptography/HardcoreBit/PairwiseIndependence.lean) | - |
| H:82 | `TCSlib.Cryptography.ofFn_glCoinsEquiv` | TCSlib.Cryptography.ofFn_glCoinsEquiv (lines 848; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0245 | `TCSlib.Cryptography.ofFn_glCoinsEquiv` | TCSlib.Cryptography.ofFn_glCoinsEquiv l.842: Tactic `rfl` failed: The left-hand side (#248 | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:80 | `TCSlib.Cryptography.unaryMulFun_poly` | TCSlib.Cryptography.unaryMulFun_poly (lines 488; #248 OPEN_INCOMPLETE) | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0243 | `TCSlib.Cryptography.unaryMulFun_poly` | TCSlib.Cryptography.unaryMulFun_poly l.490: Invalid `⟨...⟩` notation: The expected type `P | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |

**TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:87 | `TCSlib.Cryptography.statClose_glPadSampler` | TCSlib.Cryptography.statClose_glPadSampler (lines 772, 777, 770; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0248 | `TCSlib.Cryptography.statClose_glPadSampler` | TCSlib.Cryptography.statClose_glPadSampler l.809: 'show' tactic failed, pattern (#248 inhe | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |

**TCSlib/Cryptography/Asymptotic/OneWayYao.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:104 | `TCSlib.Cryptography.OneWay.YaoMachine.ans_layout` | TCSlib.Cryptography.OneWay.YaoMachine.ans_layout (lines 677, 690; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0253 | `TCSlib.Cryptography.OneWay.YaoMachine.ans_layout` | TCSlib.Cryptography.OneWay.YaoMachine.ans_layout l.704: Tactic `rfl` failed: The left-hand | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:103 | `TCSlib.Cryptography.OneWay.YaoMachine.length_g_iterate_le` | TCSlib.Cryptography.OneWay.YaoMachine.length_g_iterate_le (lines 442; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.inCoins_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0250 | `TCSlib.Cryptography.OneWay.YaoMachine.length_g_iterate_le` | TCSlib.Cryptography.OneWay.YaoMachine.length_g_iterate_le l.449: Type mismatch (#248 inher | use Complexity.NUPPT.inCoins_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| H:105 | `TCSlib.Cryptography.OneWay.YaoMachine.statClose_sampleAll` | TCSlib.Cryptography.OneWay.YaoMachine.statClose_sampleAll (lines 750; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0254 | `TCSlib.Cryptography.OneWay.YaoMachine.statClose_sampleAll` | TCSlib.Cryptography.OneWay.YaoMachine.statClose_sampleAll l.764: Type mismatch (#248 inher | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0251 | `TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_poly` | TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_poly l.456: Type mismatch (#248 inherited_sam | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0252 | `TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_poly` | TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_poly l.457: unsolved goals (#248 inherited_sa | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| H:106 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction (lines 907, 912, 916, 927, 935; #248 OPEN_T | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0255 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.923: Application type mismatch: The argum | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0256 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.928: Application type mismatch: The argum | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0257 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.932: Application type mismatch: The argum | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0258 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.943: Application type mismatch: The argum | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0259 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.951: Application type mismatch: The argum | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |

**TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:218 | `TCSlib.Cryptography.uprob_comp_eq_probTrue_map` | 52 rw TCSlib.InformationTheory.FinDist.probTrue | use TCSlib.InformationTheory.FinDist.probTrue_eq (TCSlib/InformationTheory/FinDist.lean) | - |
| NEW:228 | `TCSlib.Cryptography.uprob_comp_eq_probTrue_map` | TCSlib.InformationTheory.FinDist.probTrue.eq_1 | use TCSlib.InformationTheory.FinDist.probTrue_eq (TCSlib/InformationTheory/FinDist.lean) | - |

**TCSlib/Cryptography/Asymptotic/Universal.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:120 | `TCSlib.Cryptography.clockedAnswer_eq_cons_of_computesInTime` | TCSlib.Cryptography.clockedAnswer_eq_cons_of_computesInTime (lines 132, 133; #248 OPEN_MAC | use Turing.CodeTM.toFinTM_k (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| SEAL-0281 | `TCSlib.Cryptography.clockedAnswer_eq_cons_of_computesInTime` | TCSlib.Cryptography.clockedAnswer_eq_cons_of_computesInTime l.132: Type mismatch (#248 inh | use Turing.CodeTM.toFinTM_k (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| SEAL-0282 | `TCSlib.Cryptography.clockedAnswer_eq_cons_of_computesInTime` | TCSlib.Cryptography.clockedAnswer_eq_cons_of_computesInTime l.133: Type mismatch (#248 inh | use Turing.CodeTM.toFinTM_k (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| H:121 | `TCSlib.Cryptography.clockedAnswer_eq_false_of_not_computesInTime` | TCSlib.Cryptography.clockedAnswer_eq_false_of_not_computesInTime (lines 144; #248 OPEN_MAC | use Turing.CodeTM.toFinTM_k (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| SEAL-0283 | `TCSlib.Cryptography.clockedAnswer_eq_false_of_not_computesInTime` | TCSlib.Cryptography.clockedAnswer_eq_false_of_not_computesInTime l.144: Application type m | use Turing.CodeTM.toFinTM_k (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| H:125 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge (lines 748, 749, 754, 756, 784, 786; #248 OPEN_ | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0285 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.744: Application type mismatch: The argument  | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0286 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.745: Application type mismatch: The argument  | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0287 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.750: Application type mismatch: The argument  | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0288 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.752: Type mismatch (#248 inherited_same_nativ | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0289 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.780: Application type mismatch: The argument  | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0290 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.782: Application type mismatch: The argument  | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| H:122 | `TCSlib.Cryptography.ofFn_getD_eq_take` | TCSlib.Cryptography.ofFn_getD_eq_take (lines 259; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.padFin_def (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| SEAL-0284 | `TCSlib.Cryptography.ofFn_getD_eq_take` | TCSlib.Cryptography.ofFn_getD_eq_take l.259: Type mismatch (#248 inherited_same_native_ste | use TCSlib.Cryptography.padFin_def (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |

**TCSlib/Cryptography/Asymptotic/UniversalLemmas.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0291 | `Complexity.NUPPT.exists_reparam_pre_post` | Complexity.NUPPT.exists_reparam_pre_post l.112: Application type mismatch: The argument (# | add Complexity.NUPPT.ofPolyTime_eq (or _iff/_apply) in TCSlib/Complexity/Randomized/PPT.lean; related: Complexity.NUPPT.ofPolyTime_uniform | - |
| SEAL-0292 | `Complexity.NUPPT.exists_reparam_pre_post_adv` | Complexity.NUPPT.exists_reparam_pre_post_adv l.160: Application type mismatch: The argumen | add Complexity.NUPPT.ofPolyTime_eq (or _iff/_apply) in TCSlib/Complexity/Randomized/PPT.lean; related: Complexity.NUPPT.ofPolyTime_uniform | - |

**TCSlib/Cryptography/Asymptotic/UniversalPadding.lean** (5 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:131 | `TCSlib.Cryptography.PadQuad.exists_family` | TCSlib.Cryptography.PadQuad.exists_family (lines 527; #248 OPEN_INCOMPLETE) | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0301 | `TCSlib.Cryptography.PadQuad.exists_family` | TCSlib.Cryptography.PadQuad.exists_family l.548: Application type mismatch: The argument ( | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:129 | `TCSlib.Cryptography.PadQuad.invProbAt_family_le` | TCSlib.Cryptography.PadQuad.invProbAt_family_le (lines 313, 346; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0299 | `TCSlib.Cryptography.PadQuad.invProbAt_family_le` | TCSlib.Cryptography.PadQuad.invProbAt_family_le l.314: Type mismatch (#248 inherited_same_ | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0300 | `TCSlib.Cryptography.PadQuad.invProbAt_family_le` | TCSlib.Cryptography.PadQuad.invProbAt_family_le l.347: Tactic `rewrite` failed: Did not fi | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |

**TCSlib/Cryptography/Candidates/Concrete.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| C3-0004 | `TCSlib.Cryptography.Candidates.rbl_loop_poly` | _private.TCSlib.Cryptography.Candidates.Concrete.0.Complexity.polyTimeComputable_iterateFi | add Complexity.polyTimeComputable_iterateFind.match_1_eq (or _iff/_apply) in TCSlib/Complexity/Randomized/Repetition.lean | - |

**TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| C1-0284 | `TCSlib.Cryptography.Candidates.dlb_instance` | 2656 simp Complexity.P | use Complexity.P_def (TCSlib/Complexity/ClassP/P.lean) | - |

**TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean** (10 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:108 | `TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly` | TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly (lines 289; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.inArg_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0268 | `TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly` | TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly l.289: Application type mismatch | use Complexity.NUPPT.inArg_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| H:109 | `TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL` | TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL (lines 333; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0269 | `TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL` | TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL l.333: Tactic `rfl` failed: The  | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:107 | `TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff` | TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff (lines 268, 276; #248 OPEN_INCO | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0266 | `TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff` | TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff l.268: Type mismatch (#248 inhe | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0267 | `TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff` | TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff l.276: Type mismatch (#248 inhe | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:110 | `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` | TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure (lines 554, 530; #248 OPEN_I | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0270 | `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` | TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure l.554: Application type mism | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0271 | `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` | TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure l.530: unsolved goals (#248  | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |

**TCSlib/Cryptography/Encryption/PublicKey/Hybrid.lean** (5 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:115 | `TCSlib.Cryptography.distAdv_tuple_le_mul` | TCSlib.Cryptography.distAdv_tuple_le_mul (lines 620; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.PrivateKeyScheme.encodeList_nil (TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean) | - |
| SEAL-0276 | `TCSlib.Cryptography.distAdv_tuple_le_mul` | TCSlib.Cryptography.distAdv_tuple_le_mul l.631: Type mismatch (#248 inherited_same_step_af | use TCSlib.Cryptography.PrivateKeyScheme.encodeList_nil (TCSlib/Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean) | - |
| H:116 | `TCSlib.Cryptography.exists_hybridBound` | TCSlib.Cryptography.exists_hybridBound (lines 695, 703; #248 OPEN_TYPED_COINS) | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0277 | `TCSlib.Cryptography.exists_hybridBound` | TCSlib.Cryptography.exists_hybridBound l.707: unsolved goals (#248 inherited_same_step_aft | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0278 | `TCSlib.Cryptography.exists_hybridBound` | TCSlib.Cryptography.exists_hybridBound l.715: Type mismatch (#248 inherited_same_step_afte | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |

**TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:114 | `TCSlib.Cryptography.blockEncFun_flatten` | TCSlib.Cryptography.blockEncFun_flatten (lines 217; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0275 | `TCSlib.Cryptography.blockEncFun_flatten` | TCSlib.Cryptography.blockEncFun_flatten l.218: Tactic `rfl` failed: The left-hand side (#2 | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |

**TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean** (6 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:113 | `TCSlib.Cryptography.acceptProb_owpGenNot_unit` | TCSlib.Cryptography.acceptProb_owpGenNot_unit (lines 808; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0274 | `TCSlib.Cryptography.acceptProb_owpGenNot_unit` | TCSlib.Cryptography.acceptProb_owpGenNot_unit l.808: Type mismatch (#248 inherited_reviewe | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:112 | `TCSlib.Cryptography.acceptProb_owpGen_unit` | TCSlib.Cryptography.acceptProb_owpGen_unit (lines 800; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.owpGen_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0273 | `TCSlib.Cryptography.acceptProb_owpGen_unit` | TCSlib.Cryptography.acceptProb_owpGen_unit l.800: Type mismatch (#248 inherited_reviewed_c | add TCSlib.Cryptography.owpGen_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| H:111 | `TCSlib.Cryptography.predProb_pkPredictor_eq` | TCSlib.Cryptography.predProb_pkPredictor_eq (lines 792; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0272 | `TCSlib.Cryptography.predProb_pkPredictor_eq` | TCSlib.Cryptography.predProb_pkPredictor_eq l.792: Type mismatch (#248 inherited_reviewed_ | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |

**TCSlib/Cryptography/HardcoreBit/InnerProduct.lean** (5 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:140 | `TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter` | TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter (lines 229, 228; #248 OPEN_INCOMPL | use TCSlib.Cryptography.predProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0303 | `TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter` | TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter l.242: Application type mismatch:  | use TCSlib.Cryptography.predProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0304 | `TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter` | TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter l.241: unsolved goals (#248 inheri | use TCSlib.Cryptography.predProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:139 | `TCSlib.Cryptography.HardcoreBit.uprob_recover_le_invProb` | TCSlib.Cryptography.HardcoreBit.uprob_recover_le_invProb (lines 165; #248 OPEN_INCOMPLETE) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0302 | `TCSlib.Cryptography.HardcoreBit.uprob_recover_le_invProb` | TCSlib.Cryptography.HardcoreBit.uprob_recover_le_invProb l.178: typeclass instance problem | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |

**TCSlib/Cryptography/NumberTheory/Primality.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0305 | `TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt` | TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt l.928: Type mismatch (#248 inher | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |

**TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:52 | `TCSlib.Cryptography.GGMRed.length_lookStep_iterate_le` | TCSlib.Cryptography.GGMRed.length_lookStep_iterate_le (lines 400; #248 OPEN_INCOMPLETE) | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0208 | `TCSlib.Cryptography.GGMRed.length_lookStep_iterate_le` | TCSlib.Cryptography.GGMRed.length_lookStep_iterate_le l.401: Type mismatch (#248 inherited | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| H:53 | `TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc` | TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc (lines 439; #248 OPEN_INCOMPLETE) | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0210 | `TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc` | TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc l.440: Tactic `rfl` failed: The left-ha | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0209 | `TCSlib.Cryptography.GGMRed.lookup_poly` | TCSlib.Cryptography.GGMRed.lookup_poly l.423: Type mismatch (#248 inherited_same_native_st | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0207 | `TCSlib.Cryptography.GGMRed.stateLoopFun_poly` | TCSlib.Cryptography.GGMRed.stateLoopFun_poly l.300: Type mismatch (#248 inherited_same_nat | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| EFF72:SEAL-0207 | `TCSlib.Cryptography.GGMRed.stateLoopFun_poly` | efficiency-72 pair SEAL-0207 TCSlib.Cryptography.GGMRed.stateLoopFun_poly (home at ruling  | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |

**TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean** (17 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:56 | `TCSlib.Cryptography.GGMRed.concrete_succ` | TCSlib.Cryptography.GGMRed.concrete_succ (lines 112, 113; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GGMRed.buildTreeQ_succ (TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean) | - |
| SEAL-0213 | `TCSlib.Cryptography.GGMRed.concrete_succ` | TCSlib.Cryptography.GGMRed.concrete_succ l.112: Tactic `rfl` failed: The left-hand side (# | use TCSlib.Cryptography.GGMRed.buildTreeQ_succ (TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean) | - |
| SEAL-0214 | `TCSlib.Cryptography.GGMRed.concrete_succ` | TCSlib.Cryptography.GGMRed.concrete_succ l.113: Tactic `rfl` failed: The left-hand side (# | use TCSlib.Cryptography.GGMRed.buildTreeQ_succ (TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean) | - |
| H:55 | `TCSlib.Cryptography.GGMRed.concrete_zero` | TCSlib.Cryptography.GGMRed.concrete_zero (lines 101, 101; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GGMRed.verdictOf_eq (TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean) | - |
| SEAL-0211 | `TCSlib.Cryptography.GGMRed.concrete_zero` | TCSlib.Cryptography.GGMRed.concrete_zero l.101: Tactic `rfl` failed: The left-hand side (# | use TCSlib.Cryptography.GGMRed.verdictOf_eq (TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean) | - |
| SEAL-0212 | `TCSlib.Cryptography.GGMRed.concrete_zero` | TCSlib.Cryptography.GGMRed.concrete_zero l.101: Tactic `rfl` failed: The left-hand side (# | use TCSlib.Cryptography.GGMRed.verdictOf_eq (TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean) | - |
| H:61 | `TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher` | TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher (lines 784; #248 OPEN_INCOMPLETE) | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0219 | `TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher` | TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher l.775: Type mismatch (#248 inherite | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:58 | `TCSlib.Cryptography.GGMRed.move_eq` | TCSlib.Cryptography.GGMRed.move_eq (lines 381; #248 OPEN_INCOMPLETE) | use Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0216 | `TCSlib.Cryptography.GGMRed.move_eq` | TCSlib.Cryptography.GGMRed.move_eq l.368: Tactic `rfl` failed: The left-hand side (#248 in | use Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| H:59 | `TCSlib.Cryptography.GGMRed.orbit_eq_encState` | TCSlib.Cryptography.GGMRed.orbit_eq_encState (lines 541; #248 OPEN_INCOMPLETE) | use Complexity.StateLoop.orbit_succ (TCSlib/Complexity/Randomized/Build/StateLoop.lean) | - |
| SEAL-0217 | `TCSlib.Cryptography.GGMRed.orbit_eq_encState` | TCSlib.Cryptography.GGMRed.orbit_eq_encState l.530: Type mismatch (#248 inherited_same_nat | use Complexity.StateLoop.orbit_succ (TCSlib/Complexity/Randomized/Build/StateLoop.lean) | - |
| C3-0002 | `TCSlib.Cryptography.GGMRed.queryOf_eq_some_iff` | _private.TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run.0.TCSlib.Cryptograp | add TCSlib.Cryptography.GGMRed.queryOf.match_1_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean | - |
| C3-0003 | `TCSlib.Cryptography.GGMRed.queryOf_eq_some_iff` | _private.TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run.0.TCSlib.Cryptograp | add TCSlib.Cryptography.GGMRed.queryOf.match_1_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean | - |
| NEW:229 | `TCSlib.Cryptography.GGMRed.queryOf_eq_some_iff` | _private.TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run.0.TCSlib.Cryptograp | add TCSlib.Cryptography.GGMRed.queryOf.match_1_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean | - |
| H:60 | `TCSlib.Cryptography.GGMRed.runAt_ggmRedMachine` | TCSlib.Cryptography.GGMRed.runAt_ggmRedMachine (lines 752; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0218 | `TCSlib.Cryptography.GGMRed.runAt_ggmRedMachine` | TCSlib.Cryptography.GGMRed.runAt_ggmRedMachine l.742: Tactic `rfl` failed: The left-hand s | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |

**TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Defs.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0262 | `TCSlib.Cryptography.Ensemble.Indist.pseudorandom` | TCSlib.Cryptography.Ensemble.Indist.pseudorandom l.105: Application type mismatch: The arg | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0260 | `TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv` | TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv l.94: Type mismatch (#248 inherited_s | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| SEAL-0261 | `TCSlib.Cryptography.Ensemble.uniform_pseudorandom` | TCSlib.Cryptography.Ensemble.uniform_pseudorandom l.99: Type mismatch (#248 inherited_same | use TCSlib.Cryptography.Ensemble.pseudorandom_iff (TCSlib/Cryptography/Asymptotic/Ensembles.lean) | - |
| SEAL-0264 | `TCSlib.Cryptography.PRG.Easy.samplable` | TCSlib.Cryptography.PRG.Easy.samplable l.198: Invalid `⟨...⟩` notation: The expected type  | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0265 | `TCSlib.Cryptography.PRG.Easy.samplable` | TCSlib.Cryptography.PRG.Easy.samplable l.199: No goals to be solved (#248 inherited_same_n | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| C1-0277 | `TCSlib.Cryptography.PRG.Easy.samplable` | 203 simp Complexity.NUPPT.advInput | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0263 | `TCSlib.Cryptography.PRG.secure_iff` | TCSlib.Cryptography.PRG.secure_iff l.189: Type mismatch (#248 inherited_same_native_step) | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |

**TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean** (3 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:63 | `TCSlib.Cryptography.exists_owpPredictorSnoc` | TCSlib.Cryptography.exists_owpPredictorSnoc (lines 389, 395; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0221 | `TCSlib.Cryptography.exists_owpPredictorSnoc` | TCSlib.Cryptography.exists_owpPredictorSnoc l.390: Type mismatch (#248 inherited_reviewed_ | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0222 | `TCSlib.Cryptography.exists_owpPredictorSnoc` | TCSlib.Cryptography.exists_owpPredictorSnoc l.396: Tactic `rfl` failed: The left-hand side | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |

**TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean** (6 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:65 | `TCSlib.Cryptography.prgAdv_fst` | TCSlib.Cryptography.prgAdv_fst (lines 529; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0224 | `TCSlib.Cryptography.prgAdv_fst` | TCSlib.Cryptography.prgAdv_fst l.530: Tactic `rfl` failed: The left-hand side (#248 inheri | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:66 | `TCSlib.Cryptography.prg_expand` | TCSlib.Cryptography.prg_expand (lines 589; #248 OPEN_TYPED_COINS) | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0225 | `TCSlib.Cryptography.prg_expand` | TCSlib.Cryptography.prg_expand l.595: Tactic `rfl` failed: The left-hand side (#248 inheri | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0226 | `TCSlib.Cryptography.prg_expand` | TCSlib.Cryptography.prg_expand l.608: Application type mismatch: The argument (#248 inheri | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0227 | `TCSlib.Cryptography.prg_expand` | TCSlib.Cryptography.prg_expand l.619: Type mismatch (#248 inherited_reached_in_baseline_pr | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |

**TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:219 | `TCSlib.Cryptography.SecureComputation.sliceMultiMessageSecure_of_prfOut` | 301 dsimp Complexity.P | use Complexity.P_def (TCSlib/Complexity/ClassP/P.lean) | - |

**TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GarbledRun.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:220 | `TCSlib.Cryptography.SecureComputation.YaoHybridProof.garbledRunWith_poly` | 117 simpa Complexity.P | use Complexity.P_def (TCSlib/Complexity/ClassP/P.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/Commitment.lean** (13 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:146 | `TCSlib.Cryptography.exists_bitComPredictor` | TCSlib.Cryptography.exists_bitComPredictor (lines 596, 600, 604; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0309 | `TCSlib.Cryptography.exists_bitComPredictor` | TCSlib.Cryptography.exists_bitComPredictor l.603: Type mismatch (#248 inherited_reviewed_c | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0310 | `TCSlib.Cryptography.exists_bitComPredictor` | TCSlib.Cryptography.exists_bitComPredictor l.607: Tactic `rfl` failed: The left-hand side  | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0311 | `TCSlib.Cryptography.exists_bitComPredictor` | TCSlib.Cryptography.exists_bitComPredictor l.611: Tactic `rfl` failed: The left-hand side  | add TCSlib.Cryptography.owpPair_eq (or _iff/_apply) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| H:147 | `TCSlib.Cryptography.exists_bitRed_bound` | TCSlib.Cryptography.exists_bitRed_bound (lines 712; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.FunFamily.blocks_apply (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| SEAL-0312 | `TCSlib.Cryptography.exists_bitRed_bound` | TCSlib.Cryptography.exists_bitRed_bound l.719: Tactic `rfl` failed: The left-hand side (#2 | use TCSlib.Cryptography.FunFamily.blocks_apply (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| H:145 | `TCSlib.Cryptography.exists_multiRed_bound` | TCSlib.Cryptography.exists_multiRed_bound (lines 308; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0308 | `TCSlib.Cryptography.exists_multiRed_bound` | TCSlib.Cryptography.exists_multiRed_bound l.315: Type mismatch (#248 inherited_same_step_a | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:148 | `TCSlib.Cryptography.owpComStr_eq_loopOut` | TCSlib.Cryptography.owpComStr_eq_loopOut (lines 843, 844; #248 OPEN_INCOMPLETE) | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0313 | `TCSlib.Cryptography.owpComStr_eq_loopOut` | TCSlib.Cryptography.owpComStr_eq_loopOut l.850: Tactic `rfl` failed: The left-hand side (# | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0314 | `TCSlib.Cryptography.owpComStr_eq_loopOut` | TCSlib.Cryptography.owpComStr_eq_loopOut l.851: Type mismatch (#248 inherited_same_native_ | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:149 | `TCSlib.Cryptography.owpComStr_polyTimeComputable` | TCSlib.Cryptography.owpComStr_polyTimeComputable (lines 870; #248 OPEN_INCOMPLETE) | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0315 | `TCSlib.Cryptography.owpComStr_polyTimeComputable` | TCSlib.Cryptography.owpComStr_polyTimeComputable l.882: Application type mismatch: The arg | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean** (4 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0321 | `TCSlib.Cryptography.CommitmentLemmas.ComLoop.emit_init_of_lt` | TCSlib.Cryptography.CommitmentLemmas.ComLoop.emit_init_of_lt l.499: Type mismatch (#248 in | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0316 | `TCSlib.Cryptography.CommitmentLemmas.acceptProb_eq_uexp_fst` | TCSlib.Cryptography.CommitmentLemmas.acceptProb_eq_uexp_fst l.97: Tactic `rfl` failed: The | add TCSlib.Cryptography.EnsembleLemmas.swapAux_eq (or _iff/_apply) in TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean | - |
| SEAL-0317 | `TCSlib.Cryptography.CommitmentLemmas.distAdv_comm` | TCSlib.Cryptography.CommitmentLemmas.distAdv_comm l.122: Type mismatch (#248 inherited_sam | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0320 | `TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append` | TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append l.234: Tactic `rfl` failed: The lef | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/Defs.lean** (16 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:152 | `TCSlib.Cryptography.AbortRetry.attempt_poly` | TCSlib.Cryptography.AbortRetry.attempt_poly (lines 394; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.inParam_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0324 | `TCSlib.Cryptography.AbortRetry.attempt_poly` | TCSlib.Cryptography.AbortRetry.attempt_poly l.394: Type mismatch (#248 inherited_same_nati | use Complexity.NUPPT.inParam_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| H:153 | `TCSlib.Cryptography.AbortRetry.exists_retrySimulator` | TCSlib.Cryptography.AbortRetry.exists_retrySimulator (lines 440, 438; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0325 | `TCSlib.Cryptography.AbortRetry.exists_retrySimulator` | TCSlib.Cryptography.AbortRetry.exists_retrySimulator l.440: Tactic `rfl` failed: The left- | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0326 | `TCSlib.Cryptography.AbortRetry.exists_retrySimulator` | TCSlib.Cryptography.AbortRetry.exists_retrySimulator l.438: Application type mismatch: The | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:154 | `TCSlib.Cryptography.AbortRetry.statClose_retry` | TCSlib.Cryptography.AbortRetry.statClose_retry (lines 513; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0327 | `TCSlib.Cryptography.AbortRetry.statClose_retry` | TCSlib.Cryptography.AbortRetry.statClose_retry l.513: Tactic `introN` failed: There are no | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| H:155 | `TCSlib.Cryptography.PerfectZKAbort.statZK` | TCSlib.Cryptography.PerfectZKAbort.statZK (lines 629, 641, 643; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.Protocol.viewV_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0328 | `TCSlib.Cryptography.PerfectZKAbort.statZK` | TCSlib.Cryptography.PerfectZKAbort.statZK l.629: Invalid rewrite argument: Expected an equ | use TCSlib.Cryptography.Protocol.viewV_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0329 | `TCSlib.Cryptography.PerfectZKAbort.statZK` | TCSlib.Cryptography.PerfectZKAbort.statZK l.641: Application type mismatch: The argument ( | use TCSlib.Cryptography.Protocol.viewV_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0330 | `TCSlib.Cryptography.PerfectZKAbort.statZK` | TCSlib.Cryptography.PerfectZKAbort.statZK l.643: Tactic `introN` failed: There are no addi | use TCSlib.Cryptography.Protocol.viewV_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| H:156 | `TCSlib.Cryptography.negligible_inv_pow_sqrt_div` | TCSlib.Cryptography.negligible_inv_pow_sqrt_div (lines 673; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| SEAL-0331 | `TCSlib.Cryptography.negligible_inv_pow_sqrt_div` | TCSlib.Cryptography.negligible_inv_pow_sqrt_div l.673: Tactic `introN` failed: There are n | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| H:151 | `TCSlib.Cryptography.perfectZK_zeroRounds` | TCSlib.Cryptography.perfectZK_zeroRounds (lines 291, 292; #248 OPEN_INCOMPLETE) | add Complexity.NUPPT.ofPolyTimeUniform_eq (or _iff/_apply) in TCSlib/Complexity/Randomized/PPT.lean; related: Complexity.NUPPT.ofPolyTimeUniform_uniform | - |
| SEAL-0322 | `TCSlib.Cryptography.perfectZK_zeroRounds` | TCSlib.Cryptography.perfectZK_zeroRounds l.291: Application type mismatch: The argument (# | add Complexity.NUPPT.ofPolyTimeUniform_eq (or _iff/_apply) in TCSlib/Complexity/Randomized/PPT.lean; related: Complexity.NUPPT.ofPolyTimeUniform_uniform | - |
| SEAL-0323 | `TCSlib.Cryptography.perfectZK_zeroRounds` | TCSlib.Cryptography.perfectZK_zeroRounds l.292: No goals to be solved (#248 inherited_same | add Complexity.NUPPT.ofPolyTimeUniform_eq (or _iff/_apply) in TCSlib/Complexity/Randomized/PPT.lean; related: Complexity.NUPPT.ofPolyTimeUniform_uniform | - |

**TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| C1-0300 | `TCSlib.Cryptography.EncodingMachines.bitsToNat_eq_blockVal` | 225 simp TCSlib.Cryptography.bitsToNat | use TCSlib.Cryptography.bitsToNat_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0301 | `TCSlib.Cryptography.EncodingMachines.bitsToNat_eq_blockVal` | 228 unfold TCSlib.Cryptography.bitsToNat | use TCSlib.Cryptography.bitsToNat_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0306 | `TCSlib.Cryptography.EncodingMachines.fisherYates_val_eq` | 684 unfold TCSlib.Cryptography.fisherYates | use TCSlib.Cryptography.fisherYates_succ (TCSlib/Cryptography/Asymptotic/Permutations.lean) | - |
| C1-0307 | `TCSlib.Cryptography.EncodingMachines.permFromCoins_getD_val` | 721 unfold TCSlib.Cryptography.permFromCoins | add TCSlib.Cryptography.permFromCoins_eq (or _iff/_apply) in TCSlib/Cryptography/Asymptotic/Permutations.lean; related: TCSlib.Cryptography.permFromCoins_eq_none_iff, TCSlib.Cryptography.permFromCoins_eq_some_iff, TCSlib.Cryptography.permFromCoins_uniform_of_some | - |
| C1-0303 | `TCSlib.Cryptography.EncodingMachines.rejectionSample_eq_dite` | 618 unfold TCSlib.Cryptography.rejectionSample | use TCSlib.Cryptography.rejectionSample_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0304 | `TCSlib.Cryptography.EncodingMachines.rejectionSample_eq_dite` | 625 unfold TCSlib.Cryptography.uniformFromBits | use TCSlib.Cryptography.uniformFromBits_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0305 | `TCSlib.Cryptography.EncodingMachines.rejectionSample_eq_dite` | 631 unfold TCSlib.Cryptography.uniformFromBits | use TCSlib.Cryptography.uniformFromBits_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean** (19 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:162 | `TCSlib.Cryptography.Riso_witnessRelation` | TCSlib.Cryptography.Riso_witnessRelation (lines 340; #248 OPEN_INCOMPLETE) | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| SEAL-0333 | `TCSlib.Cryptography.Riso_witnessRelation` | TCSlib.Cryptography.Riso_witnessRelation l.346: Type mismatch (#248 inherited_same_native_ | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| H:173 | `TCSlib.Cryptography.giProtocolRep_proverBounded` | TCSlib.Cryptography.giProtocolRep_proverBounded (lines 943; #248 OPEN_INCOMPLETE) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0344 | `TCSlib.Cryptography.giProtocolRep_proverBounded` | TCSlib.Cryptography.giProtocolRep_proverBounded l.954: Type mismatch (#248 inherited_same_ | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| H:172 | `TCSlib.Cryptography.giProtocol_proverBounded` | TCSlib.Cryptography.giProtocol_proverBounded (lines 938; #248 OPEN_INCOMPLETE) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0343 | `TCSlib.Cryptography.giProtocol_proverBounded` | TCSlib.Cryptography.giProtocol_proverBounded l.949: Type mismatch (#248 inherited_same_nat | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| H:175 | `TCSlib.Cryptography.gi_efficientProverProofErr` | TCSlib.Cryptography.gi_efficientProverProofErr (lines 969; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.GI.giProver_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean; related: TCSlib.Cryptography.GI.giProver_next_nil, TCSlib.Cryptography.GI.giProver_efficient, TCSlib.Cryptography.GI.giProver_length_le | - |
| SEAL-0347 | `TCSlib.Cryptography.gi_efficientProverProofErr` | TCSlib.Cryptography.gi_efficientProverProofErr l.980: Application type mismatch: The argum | add TCSlib.Cryptography.GI.giProver_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean; related: TCSlib.Cryptography.GI.giProver_next_nil, TCSlib.Cryptography.GI.giProver_efficient, TCSlib.Cryptography.GI.giProver_length_le | - |
| H:176 | `TCSlib.Cryptography.gi_rep_efficientProverProof` | TCSlib.Cryptography.gi_rep_efficientProverProof (lines 986; #248 OPEN_INCOMPLETE) | use BoolCircuit.decodeNat_nil (TCSlib/Complexity/CircuitComplexity/UnaryCode.lean) | - |
| SEAL-0348 | `TCSlib.Cryptography.gi_rep_efficientProverProof` | TCSlib.Cryptography.gi_rep_efficientProverProof l.997: Application type mismatch: The argu | use BoolCircuit.decodeNat_nil (TCSlib/Complexity/CircuitComplexity/UnaryCode.lean) | - |
| H:174 | `TCSlib.Cryptography.gniProtocol_proverBounded` | TCSlib.Cryptography.gniProtocol_proverBounded (lines 949, 950; #248 OPEN_INCOMPLETE) | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0345 | `TCSlib.Cryptography.gniProtocol_proverBounded` | TCSlib.Cryptography.gniProtocol_proverBounded l.960: Type mismatch (#248 inherited_same_na | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0346 | `TCSlib.Cryptography.gniProtocol_proverBounded` | TCSlib.Cryptography.gniProtocol_proverBounded l.961: Type mismatch (#248 inherited_same_na | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| H:171 | `TCSlib.Cryptography.gni_interactiveProof` | TCSlib.Cryptography.gni_interactiveProof (lines 931; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.gniVerifierRep_next (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0342 | `TCSlib.Cryptography.gni_interactiveProof` | TCSlib.Cryptography.gni_interactiveProof l.942: Application type mismatch: The argument (# | use TCSlib.Cryptography.GI.gniVerifierRep_next (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| H:170 | `TCSlib.Cryptography.gni_interactiveProofErr` | TCSlib.Cryptography.gni_interactiveProofErr (lines 912; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.GI.gniVerifier_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean; related: TCSlib.Cryptography.GI.gniVerifier_next_nil, TCSlib.Cryptography.GI.gniVerifier_next_one, TCSlib.Cryptography.GI.gniVerifier_efficient | - |
| SEAL-0341 | `TCSlib.Cryptography.gni_interactiveProofErr` | TCSlib.Cryptography.gni_interactiveProofErr l.923: Application type mismatch: The argument | add TCSlib.Cryptography.GI.gniVerifier_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean; related: TCSlib.Cryptography.GI.gniVerifier_next_nil, TCSlib.Cryptography.GI.gniVerifier_next_one, TCSlib.Cryptography.GI.gniVerifier_efficient | - |
| H:163 | `TCSlib.Cryptography.permCoinLen_le` | TCSlib.Cryptography.permCoinLen_le (lines 375; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.permBits_eq (TCSlib/Cryptography/Asymptotic/Permutations.lean) | - |
| SEAL-0334 | `TCSlib.Cryptography.permCoinLen_le` | TCSlib.Cryptography.permCoinLen_le l.390: Type mismatch (#248 inherited_same_native_step) | use TCSlib.Cryptography.permBits_eq (TCSlib/Cryptography/Asymptotic/Permutations.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete.lean** (4 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0349 | `TCSlib.Cryptography.GI.negligible_mul_permFailBound` | TCSlib.Cryptography.GI.negligible_mul_permFailBound l.62: Type mismatch (#248 inherited_sa | add TCSlib.Cryptography.GI.instanceVertices_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean; related: TCSlib.Cryptography.GI.instanceVertices_length_encInstance | - |
| C1-0308 | `TCSlib.Cryptography.GI.negligible_mul_permFailBound` | 67 unfold TCSlib.Cryptography.GI.permFailBound | add TCSlib.Cryptography.GI.permFailBound_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean; related: TCSlib.Cryptography.GI.permFailBound_nonneg | - |
| SEAL-0350 | `TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le` | TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le l.208: Invalid `⟨...⟩` notation: The expected | use TCSlib.Cryptography.GI.isomorphic_iff (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0351 | `TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le` | TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le l.211: Invalid `⟨...⟩` notation: The expected | use TCSlib.Cryptography.GI.isomorphic_iff (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean** (4 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0355 | `TCSlib.Cryptography.GI.dec_sndD_last` | TCSlib.Cryptography.GI.dec_sndD_last l.315: Application type mismatch: The argument (#248  | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0353 | `TCSlib.Cryptography.GI.iterate_pairSndD_nil` | TCSlib.Cryptography.GI.iterate_pairSndD_nil l.89: Type mismatch (#248 inherited_same_nativ | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0352 | `TCSlib.Cryptography.GI.length_pairSndD_le` | TCSlib.Cryptography.GI.length_pairSndD_le l.75: Tactic `rfl` failed: The left-hand side (# | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0354 | `TCSlib.Cryptography.GI.pairSndD_encodeMsgs` | TCSlib.Cryptography.GI.pairSndD_encodeMsgs l.95: Tactic `rfl` failed: The left-hand side ( | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean** (3 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0358 | `TCSlib.Cryptography.GI.giVerifierRep_efficient` | TCSlib.Cryptography.GI.giVerifierRep_efficient l.321: 'show' tactic failed, pattern (#248  | use Complexity.NUPPT.inCoins_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0356 | `TCSlib.Cryptography.GI.gi_verdict_iff` | TCSlib.Cryptography.GI.gi_verdict_iff l.305: Type mismatch (#248 inherited_same_native_ste | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0357 | `TCSlib.Cryptography.GI.gi_verdict_iff` | TCSlib.Cryptography.GI.gi_verdict_iff l.305: Type mismatch (#248 inherited_same_native_ste | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:183 | `TCSlib.Cryptography.GI.gi_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_efficientProverProofErr (lines 305, 330, 332, 308, 334; #248 OPE | use TCSlib.Cryptography.GI.giProtocol_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0361 | `TCSlib.Cryptography.GI.gi_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_efficientProverProofErr l.316: Application type mismatch: The ar | use TCSlib.Cryptography.GI.giProtocol_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0362 | `TCSlib.Cryptography.GI.gi_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_efficientProverProofErr l.316: Type mismatch (#248 inherited_rea | use TCSlib.Cryptography.GI.giProtocol_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0363 | `TCSlib.Cryptography.GI.gi_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_efficientProverProofErr l.346: Type mismatch (#248 inherited_rea | use TCSlib.Cryptography.GI.giProtocol_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| H:182 | `TCSlib.Cryptography.GI.gni_interactiveProofErr` | TCSlib.Cryptography.GI.gni_interactiveProofErr (lines 178, 181, 187; #248 OPEN_TYPED_COINS | use TCSlib.Cryptography.GI.gniProtocol_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0359 | `TCSlib.Cryptography.GI.gni_interactiveProofErr` | TCSlib.Cryptography.GI.gni_interactiveProofErr l.186: Application type mismatch: The argum | use TCSlib.Cryptography.GI.gniProtocol_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0360 | `TCSlib.Cryptography.GI.gni_interactiveProofErr` | TCSlib.Cryptography.GI.gni_interactiveProofErr l.186: Type mismatch (#248 inherited_reache | use TCSlib.Cryptography.GI.gniProtocol_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean** (11 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:184 | `TCSlib.Cryptography.GI.gniProver_next_enc` | TCSlib.Cryptography.GI.gniProver_next_enc (lines 130; #248 OPEN_INCOMPLETE) | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0364 | `TCSlib.Cryptography.GI.gniProver_next_enc` | TCSlib.Cryptography.GI.gniProver_next_enc l.130: 'show' tactic failed, pattern (#248 inher | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| H:189 | `TCSlib.Cryptography.GI.gniRep_accept_le` | TCSlib.Cryptography.GI.gniRep_accept_le (lines 386; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.GI.encInstance_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0368 | `TCSlib.Cryptography.GI.gniRep_accept_le` | TCSlib.Cryptography.GI.gniRep_accept_le l.377: Tactic `rfl` failed: The left-hand side (#2 | use TCSlib.Cryptography.GI.encInstance_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| H:190 | `TCSlib.Cryptography.GI.gni_interactiveProofErrRep` | TCSlib.Cryptography.GI.gni_interactiveProofErrRep (lines 420, 423, 429; #248 OPEN_INCOMPLE | use TCSlib.Cryptography.GI.gniProtocolRep_V (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0369 | `TCSlib.Cryptography.GI.gni_interactiveProofErrRep` | TCSlib.Cryptography.GI.gni_interactiveProofErrRep l.411: Type mismatch (#248 inherited_sam | use TCSlib.Cryptography.GI.gniProtocolRep_V (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0370 | `TCSlib.Cryptography.GI.gni_interactiveProofErrRep` | TCSlib.Cryptography.GI.gni_interactiveProofErrRep l.414: Tactic `rcases` failed: `a✝ : Lni | use TCSlib.Cryptography.GI.gniProtocolRep_V (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0371 | `TCSlib.Cryptography.GI.gni_interactiveProofErrRep` | TCSlib.Cryptography.GI.gni_interactiveProofErrRep l.420: Tactic `rcases` failed: `x✝ : Iso | use TCSlib.Cryptography.GI.gniProtocolRep_V (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| H:188 | `TCSlib.Cryptography.GI.statClose_pi` | TCSlib.Cryptography.GI.statClose_pi (lines 302, 323; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0366 | `TCSlib.Cryptography.GI.statClose_pi` | TCSlib.Cryptography.GI.statClose_pi l.293: Tactic `introN` failed: There are no additional | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0367 | `TCSlib.Cryptography.GI.statClose_pi` | TCSlib.Cryptography.GI.statClose_pi l.314: Tactic `introN` failed: There are no additional | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean** (9 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:202 | `TCSlib.Cryptography.GI.giRep_accept_le` | TCSlib.Cryptography.GI.giRep_accept_le (lines 433; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.GI.decGraphAt_apply (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0374 | `TCSlib.Cryptography.GI.giRep_accept_le` | TCSlib.Cryptography.GI.giRep_accept_le l.425: 'show' tactic failed, pattern (#248 inherite | use TCSlib.Cryptography.GI.decGraphAt_apply (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| H:198 | `TCSlib.Cryptography.GI.giVerifierRep_next_end_enc` | TCSlib.Cryptography.GI.giVerifierRep_next_end_enc (lines 197; #248 OPEN_INCOMPLETE) | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0372 | `TCSlib.Cryptography.GI.giVerifierRep_next_end_enc` | TCSlib.Cryptography.GI.giVerifierRep_next_end_enc l.198: Type mismatch (#248 inherited_rea | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0373 | `TCSlib.Cryptography.GI.giVerifierRep_next_end_enc` | TCSlib.Cryptography.GI.giVerifierRep_next_end_enc l.195: unsolved goals (#248 inherited_re | use Complexity.pairSndD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| H:203 | `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr (lines 448, 477, 479, 451, 481; #248 | use TCSlib.Cryptography.GI.giProtocolRep_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0375 | `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr l.445: Application type mismatch: Th | use TCSlib.Cryptography.GI.giProtocolRep_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0376 | `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr l.445: Type mismatch (#248 inherited | use TCSlib.Cryptography.GI.giProtocolRep_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0377 | `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr l.480: Type mismatch (#248 inherited | use TCSlib.Cryptography.GI.giProtocolRep_P (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean** (4 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0381 | `TCSlib.Cryptography.exists_giSimulator` | TCSlib.Cryptography.exists_giSimulator l.533: Type mismatch (#248 inherited_same_native_st | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0383 | `TCSlib.Cryptography.gi_hvzk` | TCSlib.Cryptography.gi_hvzk l.594: Application type mismatch: The argument (#248 inherited | add TCSlib.Cryptography.HVZK_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/Defs.lean | - |
| SEAL-0382 | `TCSlib.Cryptography.gi_statZK` | TCSlib.Cryptography.gi_statZK l.566: Tactic `introN` failed: There are no additional binde | add TCSlib.Cryptography.Riso_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean; related: TCSlib.Cryptography.Riso_witnessRelation | - |
| SEAL-0380 | `TCSlib.Cryptography.statClose_giSimTrunc` | TCSlib.Cryptography.statClose_giSimTrunc l.472: Type mismatch (#248 inherited_same_native_ | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean** (18 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:207 | `TCSlib.Cryptography.GIZK.attemptStr_ofFn` | TCSlib.Cryptography.GIZK.attemptStr_ofFn (lines 351, 348; #248 OPEN_TYPED_COINS) | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0387 | `TCSlib.Cryptography.GIZK.attemptStr_ofFn` | TCSlib.Cryptography.GIZK.attemptStr_ofFn l.340: Type mismatch (#248 inherited_same_step_af | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0388 | `TCSlib.Cryptography.GIZK.attemptStr_ofFn` | TCSlib.Cryptography.GIZK.attemptStr_ofFn l.336: unsolved goals (#248 inherited_same_step_a | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| H:209 | `TCSlib.Cryptography.GIZK.giProver_next_cons` | TCSlib.Cryptography.GIZK.giProver_next_cons (lines 407; #248 OPEN_INCOMPLETE) | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0390 | `TCSlib.Cryptography.GIZK.giProver_next_cons` | TCSlib.Cryptography.GIZK.giProver_next_cons l.396: 'show' tactic failed, pattern (#248 inh | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| H:208 | `TCSlib.Cryptography.GIZK.giProver_next_nil` | TCSlib.Cryptography.GIZK.giProver_next_nil (lines 398; #248 OPEN_INCOMPLETE) | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0389 | `TCSlib.Cryptography.GIZK.giProver_next_nil` | TCSlib.Cryptography.GIZK.giProver_next_nil l.387: 'show' tactic failed, pattern (#248 inhe | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| H:211 | `TCSlib.Cryptography.GIZK.negligible_delta` | TCSlib.Cryptography.GIZK.negligible_delta (lines 562, 568; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.instanceVertices_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean; related: TCSlib.Cryptography.instanceVertices_length_encInstance | - |
| SEAL-0392 | `TCSlib.Cryptography.GIZK.negligible_delta` | TCSlib.Cryptography.GIZK.negligible_delta l.551: Type mismatch (#248 inherited_same_step_a | add TCSlib.Cryptography.instanceVertices_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean; related: TCSlib.Cryptography.instanceVertices_length_encInstance | - |
| SEAL-0393 | `TCSlib.Cryptography.GIZK.negligible_delta` | TCSlib.Cryptography.GIZK.negligible_delta l.557: Type mismatch (#248 inherited_same_step_a | add TCSlib.Cryptography.instanceVertices_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean; related: TCSlib.Cryptography.instanceVertices_length_encInstance | - |
| H:204 | `TCSlib.Cryptography.GIZK.samplePerm_ofFn_castLE` | TCSlib.Cryptography.GIZK.samplePerm_ofFn_castLE (lines 155; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.permBits_eq (TCSlib/Cryptography/Asymptotic/Permutations.lean) | - |
| SEAL-0384 | `TCSlib.Cryptography.GIZK.samplePerm_ofFn_castLE` | TCSlib.Cryptography.GIZK.samplePerm_ofFn_castLE l.143: Application type mismatch: The argu | use TCSlib.Cryptography.permBits_eq (TCSlib/Cryptography/Asymptotic/Permutations.lean) | - |
| H:206 | `TCSlib.Cryptography.GIZK.statClose_pi` | TCSlib.Cryptography.GIZK.statClose_pi (lines 183; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0386 | `TCSlib.Cryptography.GIZK.statClose_pi` | TCSlib.Cryptography.GIZK.statClose_pi l.171: Tactic `introN` failed: There are no addition | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| H:205 | `TCSlib.Cryptography.GIZK.statClose_samplePerm_long` | TCSlib.Cryptography.GIZK.statClose_samplePerm_long (lines 164; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0385 | `TCSlib.Cryptography.GIZK.statClose_samplePerm_long` | TCSlib.Cryptography.GIZK.statClose_samplePerm_long l.152: Tactic `introN` failed: There ar | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| H:210 | `TCSlib.Cryptography.GIZK.statClose_typed_string` | TCSlib.Cryptography.GIZK.statClose_typed_string (lines 511; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.GIZK.sim_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean) | - |
| SEAL-0391 | `TCSlib.Cryptography.GIZK.statClose_typed_string` | TCSlib.Cryptography.GIZK.statClose_typed_string l.500: Tactic `introN` failed: There are n | use TCSlib.Cryptography.GIZK.sim_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean** (8 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:212 | `TCSlib.Cryptography.GIZK.decGraphAt_padSq` | TCSlib.Cryptography.GIZK.decGraphAt_padSq (lines 167; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.decGraphAt_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean; related: TCSlib.Cryptography.decGraphAt_encGraph | - |
| SEAL-0394 | `TCSlib.Cryptography.GIZK.decGraphAt_padSq` | TCSlib.Cryptography.GIZK.decGraphAt_padSq l.181: Type mismatch (#248 inherited_same_native | add TCSlib.Cryptography.decGraphAt_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean; related: TCSlib.Cryptography.decGraphAt_encGraph | - |
| H:213 | `TCSlib.Cryptography.GIZK.decGraph_eq_of_sqrt` | TCSlib.Cryptography.GIZK.decGraph_eq_of_sqrt (lines 186; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.decGraph_eq (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean) | - |
| SEAL-0395 | `TCSlib.Cryptography.GIZK.decGraph_eq_of_sqrt` | TCSlib.Cryptography.GIZK.decGraph_eq_of_sqrt l.200: Tactic `rfl` failed: The left-hand sid | use TCSlib.Cryptography.decGraph_eq (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean) | - |
| H:216 | `TCSlib.Cryptography.GIZK.exists_simulator` | TCSlib.Cryptography.GIZK.exists_simulator (lines 459; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0397 | `TCSlib.Cryptography.GIZK.exists_simulator` | TCSlib.Cryptography.GIZK.exists_simulator l.493: Application type mismatch: The argument ( | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:215 | `TCSlib.Cryptography.GIZK.sim_poly` | TCSlib.Cryptography.GIZK.sim_poly (lines 440; #248 OPEN_INCOMPLETE) | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0396 | `TCSlib.Cryptography.GIZK.sim_poly` | TCSlib.Cryptography.GIZK.sim_poly l.474: Type mismatch (#248 inherited_same_native_step) | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:221 | `TCSlib.Cryptography.exists_witnessRelation_of_mem_NP` | 333 simp Turing.MultiTapeTM.indicator | use Turing.MultiTapeTM.indicator_def (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:222 | `TCSlib.Cryptography.npProtocol_efficientP` | 468 simp Complexity.NUPPT.advInput | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| NEW:223 | `TCSlib.Cryptography.npProtocol_efficientV` | 455 simp Complexity.NUPPT.advInput | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| NEW:224 | `TCSlib.Cryptography.npProtocol_outV` | 413 simp TCSlib.Cryptography.Protocol.outV | use TCSlib.Cryptography.Protocol.outV_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| NEW:225 | `TCSlib.Cryptography.npProtocol_outV` | 413 simp TCSlib.Cryptography.Protocol.transcriptWith | use TCSlib.Cryptography.Protocol.transcriptWith_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| NEW:226 | `TCSlib.Cryptography.npProtocol_outV` | 413 simp TCSlib.Cryptography.exec | use TCSlib.Cryptography.exec_succ (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| NEW:227 | `TCSlib.Cryptography.npProtocol_outV` | 413 simp TCSlib.Cryptography.moverIsV | use TCSlib.Cryptography.moverIsV_def (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/NP.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:221 | `TCSlib.Cryptography.LevinReduction.efficientProverProofErr` | TCSlib.Cryptography.LevinReduction.efficientProverProofErr (lines 436; #248 OPEN_TYPED_COI | add TCSlib.Cryptography.LevinTransfer.coinTrunc_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean | - |
| SEAL-0401 | `TCSlib.Cryptography.LevinReduction.efficientProverProofErr` | TCSlib.Cryptography.LevinReduction.efficientProverProofErr l.437: Application type mismatc | add TCSlib.Cryptography.LevinTransfer.coinTrunc_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean | - |
| H:222 | `TCSlib.Cryptography.LevinReduction.zk` | TCSlib.Cryptography.LevinReduction.zk (lines 499; #248 OPEN_INCOMPLETE) | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0402 | `TCSlib.Cryptography.LevinReduction.zk` | TCSlib.Cryptography.LevinReduction.zk l.500: Tactic `introN` failed: There are no addition | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:219 | `TCSlib.Cryptography.Strategy.pullback_efficient` | TCSlib.Cryptography.Strategy.pullback_efficient (lines 253; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0398 | `TCSlib.Cryptography.Strategy.pullback_efficient` | TCSlib.Cryptography.Strategy.pullback_efficient l.261: Invalid `⟨...⟩` notation: The expec | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0399 | `TCSlib.Cryptography.Strategy.pullback_efficient` | TCSlib.Cryptography.Strategy.pullback_efficient l.262: No goals to be solved (#248 inherit | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| C1-0312 | `TCSlib.Cryptography.LevinTransfer.acceptProb_comp_unifProj` | 170 unfold TCSlib.Cryptography.acceptProb | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| C1-0313 | `TCSlib.Cryptography.LevinTransfer.acceptProb_eq_of_unifProj` | 181 unfold TCSlib.Cryptography.acceptProb | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| C1-0314 | `TCSlib.Cryptography.LevinTransfer.distAdv_eq_of_unifProj` | 195 unfold TCSlib.Cryptography.distAdv | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| C1-0321 | `TCSlib.Cryptography.LevinTransfer.distinguisherL_lift` | 405 simp Complexity.NUPPT.distinguisherL | use Complexity.NUPPT.distinguisherL_eq (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| SEAL-0403 | `TCSlib.Cryptography.LevinTransfer.exec_congr` | TCSlib.Cryptography.LevinTransfer.exec_congr l.93: Tactic `rfl` failed: The left-hand side | use TCSlib.Cryptography.exec_succ (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0406 | `TCSlib.Cryptography.LevinTransfer.exists_liftSimulator` | TCSlib.Cryptography.LevinTransfer.exists_liftSimulator l.378: Application type mismatch: T | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0407 | `TCSlib.Cryptography.LevinTransfer.exists_liftSimulator` | TCSlib.Cryptography.LevinTransfer.exists_liftSimulator l.378: Tactic `rewrite` failed: Did | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0405 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient l.297: Tactic `rcases` failed: `h | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| C1-0315 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 323 simp Complexity.NUPPT.inArg | use Complexity.NUPPT.inArg_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| C1-0316 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 323 simp Complexity.NUPPT.inCoins | use Complexity.NUPPT.inCoins_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| C1-0317 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 323 simp Complexity.NUPPT.advInput | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| C1-0318 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 323 simp Complexity.NUPPT.layout | use Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| C1-0319 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 324 simp TCSlib.Cryptography.Strategy.coinLen | use TCSlib.Cryptography.Strategy.coinLen_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| C1-0320 | `TCSlib.Cryptography.LevinTransfer.postView_encode` | 341 simp TCSlib.Cryptography.View.encode | add TCSlib.Cryptography.View.encode_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/Interaction.lean; related: TCSlib.Cryptography.View.encode_mk | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:250 | `TCSlib.Cryptography.colProtocol_sound` | TCSlib.Cryptography.colProtocol_sound (lines 853; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.ColMachines.countTrue_succ (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean) | - |
| SEAL-0415 | `TCSlib.Cryptography.colProtocol_sound` | TCSlib.Cryptography.colProtocol_sound l.857: 'show' tactic failed, pattern (#248 inherited | use TCSlib.Cryptography.ColMachines.countTrue_succ (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines.lean) | - |
| H:245 | `TCSlib.Cryptography.colProverRep_efficient` | TCSlib.Cryptography.colProverRep_efficient (lines 589; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0410 | `TCSlib.Cryptography.colProverRep_efficient` | TCSlib.Cryptography.colProverRep_efficient l.593: Type mismatch (#248 inherited_same_nativ | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| H:243 | `TCSlib.Cryptography.colProver_efficient` | TCSlib.Cryptography.colProver_efficient (lines 567; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0408 | `TCSlib.Cryptography.colProver_efficient` | TCSlib.Cryptography.colProver_efficient l.571: Type mismatch (#248 inherited_same_native_s | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| H:247 | `TCSlib.Cryptography.colProver_length_le` | TCSlib.Cryptography.colProver_length_le (lines 629; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.decGraph_eq (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean) | - |
| SEAL-0412 | `TCSlib.Cryptography.colProver_length_le` | TCSlib.Cryptography.colProver_length_le l.633: Type mismatch (#248 inherited_same_step_aft | use TCSlib.Cryptography.decGraph_eq (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean) | - |
| H:246 | `TCSlib.Cryptography.colVerifierRep_efficient` | TCSlib.Cryptography.colVerifierRep_efficient (lines 597; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0411 | `TCSlib.Cryptography.colVerifierRep_efficient` | TCSlib.Cryptography.colVerifierRep_efficient l.601: Type mismatch (#248 inherited_same_nat | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| H:244 | `TCSlib.Cryptography.colVerifier_efficient` | TCSlib.Cryptography.colVerifier_efficient (lines 582; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0409 | `TCSlib.Cryptography.colVerifier_efficient` | TCSlib.Cryptography.colVerifier_efficient l.586: Type mismatch (#248 inherited_same_native | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| H:249 | `TCSlib.Cryptography.uprob_check_uniform_le` | TCSlib.Cryptography.uprob_check_uniform_le (lines 790; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColProofs.finOneEquiv_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean | - |
| SEAL-0414 | `TCSlib.Cryptography.uprob_check_uniform_le` | TCSlib.Cryptography.uprob_check_uniform_le l.794: Type mismatch (#248 inherited_same_nativ | add TCSlib.Cryptography.ColProofs.finOneEquiv_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean** (11 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:254 | `TCSlib.Cryptography.ColProofs.colProverRep_next_eq` | TCSlib.Cryptography.ColProofs.colProverRep_next_eq (lines 297; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0421 | `TCSlib.Cryptography.ColProofs.colProverRep_next_eq` | TCSlib.Cryptography.ColProofs.colProverRep_next_eq l.298: Tactic `rfl` failed: The left-ha | use Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| H:252 | `TCSlib.Cryptography.ColProofs.colProver_next_eq` | TCSlib.Cryptography.ColProofs.colProver_next_eq (lines 180; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0416 | `TCSlib.Cryptography.ColProofs.colProver_next_eq` | TCSlib.Cryptography.ColProofs.colProver_next_eq l.180: Tactic `rfl` failed: The left-hand  | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| H:255 | `TCSlib.Cryptography.ColProofs.colVerifierRep_next_eq` | TCSlib.Cryptography.ColProofs.colVerifierRep_next_eq (lines 329; #248 OPEN_INCOMPLETE) | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| SEAL-0422 | `TCSlib.Cryptography.ColProofs.colVerifierRep_next_eq` | TCSlib.Cryptography.ColProofs.colVerifierRep_next_eq l.330: Tactic `rfl` failed: The left- | use Complexity.pairFstD_eq (TCSlib/Complexity/ClassNP/PolyTimePairing.lean) | - |
| H:253 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq (lines 224, 231, 233, 243; #248 OPEN_INC | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0417 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq l.224: Tactic `rfl` failed: The left-han | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0418 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq l.231: Tactic `rfl` failed: The left-han | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0419 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq l.233: Tactic `rfl` failed: The left-han | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0420 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq l.243: Tactic `rfl` failed: The left-han | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean** (17 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:263 | `TCSlib.Cryptography.Negligible.comp_sqrt` | TCSlib.Cryptography.Negligible.comp_sqrt (lines 690; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| SEAL-0430 | `TCSlib.Cryptography.Negligible.comp_sqrt` | TCSlib.Cryptography.Negligible.comp_sqrt l.1189: Tactic `introN` failed: There are no addi | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| H:261 | `TCSlib.Cryptography.colSimAttemptPlanted_H` | TCSlib.Cryptography.colSimAttemptPlanted_H (lines 499; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.ColSimLemmas.mergeAt_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean) | - |
| SEAL-0427 | `TCSlib.Cryptography.colSimAttemptPlanted_H` | TCSlib.Cryptography.colSimAttemptPlanted_H l.501: 'show' tactic failed, pattern (#248 inhe | use TCSlib.Cryptography.ColSimLemmas.mergeAt_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean) | - |
| H:260 | `TCSlib.Cryptography.colSimAttemptPlanted_W` | TCSlib.Cryptography.colSimAttemptPlanted_W (lines 448; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.ColSimLemmas.mergeAt_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean) | - |
| SEAL-0426 | `TCSlib.Cryptography.colSimAttemptPlanted_W` | TCSlib.Cryptography.colSimAttemptPlanted_W l.450: 'show' tactic failed, pattern (#248 inhe | use TCSlib.Cryptography.ColSimLemmas.mergeAt_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean) | - |
| H:264 | `TCSlib.Cryptography.col_hvzk` | TCSlib.Cryptography.col_hvzk (lines 789; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.HVZK_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/Defs.lean | - |
| SEAL-0431 | `TCSlib.Cryptography.col_hvzk` | TCSlib.Cryptography.col_hvzk l.1646: Application type mismatch: The argument (#248 inherit | add TCSlib.Cryptography.HVZK_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/Defs.lean | - |
| H:262 | `TCSlib.Cryptography.exists_colSimulator` | TCSlib.Cryptography.exists_colSimulator (lines 676, 676; #248 OPEN_TYPED_COINS) | add TCSlib.Cryptography.ColSimMachine.simCoins_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0428 | `TCSlib.Cryptography.exists_colSimulator` | TCSlib.Cryptography.exists_colSimulator l.718: Application type mismatch: The argument (#2 | add TCSlib.Cryptography.ColSimMachine.simCoins_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0429 | `TCSlib.Cryptography.exists_colSimulator` | TCSlib.Cryptography.exists_colSimulator l.718: Application type mismatch: The argument (#2 | add TCSlib.Cryptography.ColSimMachine.simCoins_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| H:259 | `TCSlib.Cryptography.statClose_colSimTruncH` | TCSlib.Cryptography.statClose_colSimTruncH (lines 356; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0425 | `TCSlib.Cryptography.statClose_colSimTruncH` | TCSlib.Cryptography.statClose_colSimTruncH l.358: Type mismatch (#248 inherited_same_nativ | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| H:257 | `TCSlib.Cryptography.uprob_colSimAttemptH_none` | TCSlib.Cryptography.uprob_colSimAttemptH_none (lines 261; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColSimLemmas.attemptCoinsEquiv_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean | - |
| SEAL-0423 | `TCSlib.Cryptography.uprob_colSimAttemptH_none` | TCSlib.Cryptography.uprob_colSimAttemptH_none l.263: 'show' tactic failed, pattern (#248 i | add TCSlib.Cryptography.ColSimLemmas.attemptCoinsEquiv_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean | - |
| H:258 | `TCSlib.Cryptography.uprob_colSimAttemptH_some` | TCSlib.Cryptography.uprob_colSimAttemptH_some (lines 300; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColSimLemmas.attemptCoinsEquiv_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean | - |
| SEAL-0424 | `TCSlib.Cryptography.uprob_colSimAttemptH_some` | TCSlib.Cryptography.uprob_colSimAttemptH_some l.302: 'show' tactic failed, pattern (#248 i | add TCSlib.Cryptography.ColSimLemmas.attemptCoinsEquiv_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0436 | `TCSlib.Cryptography.ColSimMachine.baseR_poly` | TCSlib.Cryptography.ColSimMachine.baseR_poly l.273: Type mismatch (#248 inherited_same_nat | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0433 | `TCSlib.Cryptography.ColSimMachine.blk_poly` | TCSlib.Cryptography.ColSimMachine.blk_poly l.258: Type mismatch (#248 inherited_same_nativ | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0439 | `TCSlib.Cryptography.ColSimMachine.chunk_poly` | TCSlib.Cryptography.ColSimMachine.chunk_poly l.402: Type mismatch (#248 inherited_same_nat | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0441 | `TCSlib.Cryptography.ColSimMachine.comStr0_poly` | TCSlib.Cryptography.ColSimMachine.comStr0_poly l.428: Type mismatch (#248 inherited_same_n | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0440 | `TCSlib.Cryptography.ColSimMachine.comStr_poly` | TCSlib.Cryptography.ColSimMachine.comStr_poly l.417: Type mismatch (#248 inherited_same_na | reader to be identified (no provider named in the message; see seal-errors.jsonl) | - |
| SEAL-0445 | `TCSlib.Cryptography.ColSimMachine.exists_simulator` | TCSlib.Cryptography.ColSimMachine.exists_simulator l.632: Application type mismatch: The a | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0438 | `TCSlib.Cryptography.ColSimMachine.kPos_poly` | TCSlib.Cryptography.ColSimMachine.kPos_poly l.320: Type mismatch (#248 inherited_same_nati | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0432 | `TCSlib.Cryptography.ColSimMachine.length_simX_le` | TCSlib.Cryptography.ColSimMachine.length_simX_le l.235: Application type mismatch: The arg | use Complexity.NUPPT.inArg_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0435 | `TCSlib.Cryptography.ColSimMachine.mE_poly` | TCSlib.Cryptography.ColSimMachine.mE_poly l.268: Type mismatch (#248 inherited_same_native | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0434 | `TCSlib.Cryptography.ColSimMachine.nV_poly` | TCSlib.Cryptography.ColSimMachine.nV_poly l.263: Type mismatch (#248 inherited_same_native | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0442 | `TCSlib.Cryptography.ColSimMachine.opnStr_poly` | TCSlib.Cryptography.ColSimMachine.opnStr_poly l.476: Type mismatch (#248 inherited_same_na | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0444 | `TCSlib.Cryptography.ColSimMachine.sim_eq` | TCSlib.Cryptography.ColSimMachine.sim_eq l.573: Type mismatch (#248 inherited_same_step_af | use TCSlib.Cryptography.decGraph_eq (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean) | - |
| SEAL-0437 | `TCSlib.Cryptography.ColSimMachine.vIdx_poly` | TCSlib.Cryptography.ColSimMachine.vIdx_poly l.301: Type mismatch (#248 inherited_same_step | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |
| SEAL-0443 | `TCSlib.Cryptography.ColSimMachine.view_poly` | TCSlib.Cryptography.ColSimMachine.view_poly l.484: Type mismatch (#248 inherited_same_nati | use Complexity.polyTimeComputable_iff (TCSlib/Complexity/ClassNP/PolyTime.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean** (20 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0451 | `TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum` | TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum l.652: Type mismatch (#248 inhe | use TCSlib.Cryptography.decGraph_eq (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean) | - |
| SEAL-0452 | `TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum` | TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum l.653: Type mismatch (#248 inhe | use TCSlib.Cryptography.decGraph_eq (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean) | - |
| C1-0342 | `TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum` | 698 unfold TCSlib.Cryptography.colOpen | use TCSlib.Cryptography.colOpen_eq (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean) | - |
| C1-0325 | `TCSlib.Cryptography.ColSimMachine.bitsToNat_getD_eq_blockVal` | 138 simp TCSlib.Cryptography.bitsToNat | use TCSlib.Cryptography.bitsToNat_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0326 | `TCSlib.Cryptography.ColSimMachine.bitsToNat_getD_eq_blockVal` | 141 unfold TCSlib.Cryptography.bitsToNat | use TCSlib.Cryptography.bitsToNat_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0450 | `TCSlib.Cryptography.ColSimMachine.colCommit_eq_comStr` | TCSlib.Cryptography.ColSimMachine.colCommit_eq_comStr l.638: Tactic `rfl` failed: The left | use TCSlib.Cryptography.EnsembleLemmas.padL_eq (TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean) | - |
| C1-0340 | `TCSlib.Cryptography.ColSimMachine.colCommit_eq_comStr` | 634 unfold TCSlib.Cryptography.colCommit | use TCSlib.Cryptography.colCommit_eq (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean) | - |
| C1-0341 | `TCSlib.Cryptography.ColSimMachine.colCommit_eq_comStr` | 634 unfold TCSlib.Cryptography.multiCom | use TCSlib.Cryptography.multiCom_def (TCSlib/Cryptography/ZeroKnowledge/Commitment.lean) | - |
| SEAL-0448 | `TCSlib.Cryptography.ColSimMachine.edgeList_eq_map` | TCSlib.Cryptography.ColSimMachine.edgeList_eq_map l.357: 'show' tactic failed, pattern (#2 | use TCSlib.Cryptography.decGraph_eq (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean) | - |
| C1-0333 | `TCSlib.Cryptography.ColSimMachine.edgeList_eq_map` | 352 unfold TCSlib.Cryptography.edgeList | use TCSlib.Cryptography.edgeList_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean) | - |
| C1-0334 | `TCSlib.Cryptography.ColSimMachine.edgeOf_val_eq` | 480 unfold TCSlib.Cryptography.edgeOf | use TCSlib.Cryptography.edgeOf_eq (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean) | - |
| SEAL-0449 | `TCSlib.Cryptography.ColSimMachine.encodeMsgs_eq_flatMap` | TCSlib.Cryptography.ColSimMachine.encodeMsgs_eq_flatMap l.506: Tactic `rfl` failed: The le | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| C1-0337 | `TCSlib.Cryptography.ColSimMachine.encodeMsgs_eq_flatMap` | 509 simp Turing.pairEncode | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| C1-0327 | `TCSlib.Cryptography.ColSimMachine.findSome?_range_eq` | 161 simp TCSlib.Cryptography.EncodingMachines.firstIdx | add TCSlib.Cryptography.EncodingMachines.firstIdx_eq (or _iff/_apply) in TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean; related: TCSlib.Cryptography.EncodingMachines.firstIdx_le, TCSlib.Cryptography.EncodingMachines.firstIdx_min, TCSlib.Cryptography.EncodingMachines.firstIdx_congr | - |
| C1-0338 | `TCSlib.Cryptography.ColSimMachine.ofFn_getD_eq_padL` | 526 unfold TCSlib.Cryptography.EnsembleLemmas.padL | use TCSlib.Cryptography.EnsembleLemmas.padL_eq (TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean) | - |
| C1-0339 | `TCSlib.Cryptography.ColSimMachine.ofFn_getD_eq_padL` | 529 simp TCSlib.Cryptography.padFin | use TCSlib.Cryptography.padFin_def (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| C1-0330 | `TCSlib.Cryptography.ColSimMachine.sampleEdgeIdx_eq` | 234 unfold TCSlib.Cryptography.sampleEdgeIdx | use TCSlib.Cryptography.sampleEdgeIdx_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean) | - |
| SEAL-0446 | `TCSlib.Cryptography.ColSimMachine.sampleIdx_eq` | TCSlib.Cryptography.ColSimMachine.sampleIdx_eq l.213: 'show' tactic failed, pattern (#248  | use TCSlib.Cryptography.sampleIdx_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean) | - |
| SEAL-0447 | `TCSlib.Cryptography.ColSimMachine.sampleIdx_eq` | TCSlib.Cryptography.ColSimMachine.sampleIdx_eq l.224: 'show' tactic failed, pattern (#248  | use TCSlib.Cryptography.sampleIdx_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean) | - |
| C1-0329 | `TCSlib.Cryptography.ColSimMachine.sampleIdx_eq` | 218 simp TCSlib.Cryptography.uniformFromBits | use TCSlib.Cryptography.uniformFromBits_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/InformationTheory/LeftoverHash.lean** (8 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0458 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.96: Tactic `rewrite` failed: Did not find | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |
| SEAL-0459 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.111: Function expected at (#248 inherited | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |
| SEAL-0460 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.125: Application type mismatch: The argum | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |
| SEAL-0461 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.128: Application type mismatch: The argum | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |
| SEAL-0462 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.132: unsolved goals (#248 inherited_same_ | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |
| SEAL-0463 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.135: Tactic `rewrite` failed: Did not fin | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |
| C1-0343 | `TCSlib.InformationTheory.collision_hashPair_le` | 94 simp TCSlib.InformationTheory.FinDist.collision | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |
| C1-0344 | `TCSlib.InformationTheory.collision_hashPair_le` | 134 simp TCSlib.InformationTheory.FinDist.collision | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |

Totals per file: Complexity/ClassP/BinaryArith/Unary.lean 2; Complexity/Randomized/Build/IterateFind.lean 23; Complexity/Randomized/Build/IterateFindHost.lean 26; Complexity/Randomized/Build/PairSplit.lean 54; Complexity/Randomized/Build/UnaryMul.lean 19; Complexity/Randomized/Primitives.lean 2; Complexity/Randomized/SeedMajority/Enumeration.lean 1; Complexity/Randomized/UnaryPolynomial.lean 1; Complexity/TuringMachine/Build/ModuleHost.lean 20; Complexity/TuringMachine/Build/WordTiming.lean 2; Cryptography/Asymptotic/Collections.lean 2; Cryptography/Asymptotic/Ensembles.lean 20; Cryptography/Asymptotic/EnsemblesLemmas.lean 8; Cryptography/Asymptotic/GoldreichLevinDomain.lean 1; Cryptography/Asymptotic/HardCore/Functions.lean 12; Cryptography/Asymptotic/HardCoreCollection.lean 14; Cryptography/Asymptotic/HardCoreGL.lean 8; Cryptography/Asymptotic/HardCoreLemmas.lean 2; Cryptography/Asymptotic/OneWayYao.lean 14; Cryptography/Asymptotic/SamplingFinDist.lean 2; Cryptography/Asymptotic/Universal.lean 14; Cryptography/Asymptotic/UniversalLemmas.lean 2; Cryptography/Asymptotic/UniversalPadding.lean 5; Cryptography/Candidates/Concrete.lean 1; Cryptography/Candidates/DiscreteLogHardcore.lean 1; Cryptography/Encryption/PublicKey/EnsembleSecurity.lean 10; Cryptography/Encryption/PublicKey/Hybrid.lean 5; Cryptography/Encryption/PublicKey/HybridMachine.lean 2; Cryptography/Encryption/PublicKey/Trapdoor.lean 6; Cryptography/HardcoreBit/InnerProduct.lean 5; Cryptography/NumberTheory/Primality.lean 1; Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean 7; Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean 17; Cryptography/Pseudorandom/Generators/Asymptotic/Defs.lean 7; Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean 3; Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean 6; Cryptography/SecureComputation/SpecialEncryptionMulti.lean 1; Cryptography/SecureComputation/Yao/HybridProof/GarbledRun.lean 1; Cryptography/ZeroKnowledge/Commitment.lean 13; Cryptography/ZeroKnowledge/CommitmentLemmas.lean 4; Cryptography/ZeroKnowledge/Defs.lean 16; Cryptography/ZeroKnowledge/EncodingPermutations.lean 7; Cryptography/ZeroKnowledge/GraphIsomorphism.lean 19; Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete.lean 4; Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean 4; Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean 3; Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean 7; Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean 11; Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean 9; Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean 4; Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean 18; Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean 8; Cryptography/ZeroKnowledge/InteractiveProofs.lean 7; Cryptography/ZeroKnowledge/NP.lean 7; Cryptography/ZeroKnowledge/NPLemmas.lean 14; Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean 14; Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean 11; Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean 17; Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine.lean 14; Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean 20; InformationTheory/LeftoverHash.lean 8 (total 566).

### Provider-reader list (STAGE2-PROVIDER-READER), by provider file

**TCSlib/Complexity/TuringMachine/Configuration.lean**

| reader needed | owner items |
|---|---|
| add Turing.Cfg.inputSymbol_eq (or _iff/_apply) next to Turing.Cfg.inputSymbol | NEW:134, NEW:187 |

### For separate ruling: SEAL-B-ONLY

| file | items | declarations |
|---|---|---|
| Complexity/Randomized/PPT.lean | 1 | `Complexity.NUPPT.runAtL_ofPolyTimeUniform` |
| Complexity/Randomized/Primitives.lean | 1 | `Complexity.polyTimeComputable_unaryPoly` |
| Cryptography/Asymptotic/BlockEncryptor.lean | 2 | `TCSlib.Cryptography.blockEncFun_poly`, `TCSlib.Cryptography.decListFun_poly` |
| Cryptography/Asymptotic/Collections.lean | 5 | `TCSlib.Cryptography.Collection.collInverter_success`, `TCSlib.Cryptography.Collection.fiber_le`, `TCSlib.Cryptography.Collection.invProbAt_owfFamily_le`, `TCSlib.Cryptography.Collection.owfFamily_easy`, `TCSlib.Cryptography.Collection.owfFamily` |
| Cryptography/Asymptotic/Ensembles.lean | 2 | `TCSlib.Cryptography.Ensemble.copies_X`, `TCSlib.Cryptography.Ensemble.copies` |
| Cryptography/Asymptotic/HardCore/Functions.lean | 13 | `TCSlib.Cryptography.FunFamily.glBit`, `TCSlib.Cryptography.FunFamily.glInverter`, `TCSlib.Cryptography.FunFamily.glPad_inEquiv_ofFn`, `TCSlib.Cryptography.FunFamily.glPad_inEquiv_symm_ofFn`, `TCSlib.Cryptography.FunFamily.glPad_inEquiv`, `TCSlib.Cryptography.FunFamily.glPad_inLen_eval`, `TCSlib.Cryptography.FunFamily.glPad_outEquiv_ofFn`, `TCSlib.Cryptography.FunFamily.glPad_outEquiv_symm_ofFn`,  |
| Cryptography/Asymptotic/HardCoreCollection.lean | 1 | `TCSlib.Cryptography.Collection.glPad` |
| Cryptography/Asymptotic/HardCoreGL.lean | 1 | `TCSlib.Cryptography.glMajFun_poly` |
| Cryptography/Asymptotic/HardCoreGLColl.lean | 2 | `TCSlib.Cryptography.glCollMachine_runAt`, `TCSlib.Cryptography.glColl_uprob_le` |
| Cryptography/Asymptotic/HardCoreGLFamily.lean | 2 | `TCSlib.Cryptography.glFamMachine_runAt`, `TCSlib.Cryptography.invProbOpt_glFam_eq` |
| Cryptography/Asymptotic/HardCoreLemmas.lean | 9 | `TCSlib.Cryptography.glPadCollInvMachine_runAt`, `TCSlib.Cryptography.glPadInvMachine_runAt`, `TCSlib.Cryptography.glPad_invProbAt_le`, `TCSlib.Cryptography.invProbOpt_glPad_le`, `TCSlib.Cryptography.owpPredMachine_predProb`, `TCSlib.Cryptography.owpPredMachine_predictor` |
| Cryptography/Asymptotic/HardCorePermutation/GoldreichLevin.lean | 6 | `TCSlib.Cryptography.glHalfOddInv_runAt`, `TCSlib.Cryptography.glHalfOddPred_runAt`, `TCSlib.Cryptography.glHalf_invProbAt_even`, `TCSlib.Cryptography.glHalf_predProb_even`, `TCSlib.Cryptography.oddCoins`, `TCSlib.Cryptography.ofFn_oddCoins` |
| Cryptography/Asymptotic/OneWay.lean | 22 | `TCSlib.Cryptography.FunFamily.Easy.prod`, `TCSlib.Cryptography.FunFamily.invProbAt_prod_eq`, `TCSlib.Cryptography.FunFamily.ofFn_ofString_apply`, `TCSlib.Cryptography.FunFamily.ofFn_ofString_f`, `TCSlib.Cryptography.FunFamily.ofString_id_f`, `TCSlib.Cryptography.FunFamily.ofString_inLen_eval`, `TCSlib.Cryptography.FunFamily.prod_f`, `TCSlib.Cryptography.FunFamily.prod`, `TCSlib.Cryptography.OneWa |
| Cryptography/Asymptotic/OneWayYao.lean | 1 | `TCSlib.Cryptography.OneWay.YaoMachine.ρP_eval` |
| Cryptography/Asymptotic/Universal.lean | 2 | `TCSlib.Cryptography.eval_univOutLen`, `TCSlib.Cryptography.fUniversal_hard` |
| Cryptography/Asymptotic/UniversalPadding.lean | 1 | `TCSlib.Cryptography.PadQuad.strongOneWay` |
| Cryptography/Candidates/RSA.lean | 3 | `TCSlib.Cryptography.Candidates.eval_rsaBlock`, `TCSlib.Cryptography.Candidates.eval_rsaSampleCoins`, `TCSlib.Cryptography.Candidates.eval_rsaTrials` |
| Cryptography/Candidates/Rabin.lean | 2 | `TCSlib.Cryptography.Candidates.rabin_genCore_eq`, `TCSlib.Cryptography.Candidates.rabin_genIndex` |
| Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean | 1 | `TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure.singleMessageSecure` |
| Cryptography/Encryption/PrivateKey/FromPRG.lean | 5 | `TCSlib.Cryptography.prgScheme_encCoinsEquiv_ofFn`, `TCSlib.Cryptography.prgScheme_encCoinsEquiv`, `TCSlib.Cryptography.prgScheme_genCoinsEquiv_ofFn`, `TCSlib.Cryptography.prgScheme_genCoinsEquiv`, `TCSlib.Cryptography.prgScheme` |
| Cryptography/Encryption/PublicKey/EnsembleSecurity.lean | 1 | `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` |
| Cryptography/NumberTheory/Primality.lean | 1 | `TCSlib.Cryptography.NumberTheory.eval_samplePrimeCoins` |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean | 1 | `TCSlib.Cryptography.GGMRed.coinPoly_eval` |
| Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean | 11 | `TCSlib.Cryptography.PermFamily.iterPRG_eq_expand`, `TCSlib.Cryptography.PermFamily.iterPRG`, `TCSlib.Cryptography.cor_81_7`, `TCSlib.Cryptography.owpGenPRG_G_castSucc`, `TCSlib.Cryptography.owpGenPRG_G_last`, `TCSlib.Cryptography.owpGenPRG_G_outEquiv`, `TCSlib.Cryptography.owpGenPRG_outEquiv_ofFn`, `TCSlib.Cryptography.owpGenPRG_outEquiv`, `TCSlib.Cryptography.owpGenPRG`, `TCSlib.Cryptography.owp |
| Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean | 7 | `TCSlib.Cryptography.DoublingPRG.negligible_prgAdv`, `TCSlib.Cryptography.PRG.Secure.doubling`, `TCSlib.Cryptography.PRG.Secure.truncate`, `TCSlib.Cryptography.PRG.oneBit_G`, `TCSlib.Cryptography.PRG.oneBit_secure_iff`, `TCSlib.Cryptography.PRG.oneBit`, `TCSlib.Cryptography.doublingEnsemble` |
| Cryptography/Pseudorandom/Generators/Asymptotic/StretchMachine.lean | 1 | `TCSlib.Cryptography.prgIterFun_poly` |
| Cryptography/SecureComputation/GarblingSecurity.lean | 2 | `TCSlib.Cryptography.SecureComputation.garbling_good_whp`, `TCSlib.Cryptography.SecureComputation.nestedSpecial_wrongKeyBot` |
| Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean | 1 | `TCSlib.Cryptography.SecureComputation.GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds` |
| Cryptography/SecureComputation/SpecialEncryptionSecurity.lean | 5 | `TCSlib.Cryptography.SecureComputation.PRFOut`, `TCSlib.Cryptography.SecureComputation.prfOut_var_iff`, `TCSlib.Cryptography.SecureComputation.spDecStr_wrongKey`, `TCSlib.Cryptography.SecureComputation.specialScheme_multiMessageSecure`, `TCSlib.Cryptography.SecureComputation.specialScheme_wrongKey` |
| Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean | 1 | `TCSlib.Cryptography.SecureComputation.SpecialWrongKey.exists_negligible_prefix_collision` |
| Cryptography/SecureComputation/Yao.lean | 9 | `TCSlib.Cryptography.SecureComputation.yaoCoins_eval`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_answersB_getD`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_callA`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_callB`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_hbcSecure`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime`, `TCSlib.Cryptography.SecureComputation.yaoHyb |
| Cryptography/ZeroKnowledge/Commitment.lean | 3 | `TCSlib.Cryptography.multiAdvBound_eval`, `TCSlib.Cryptography.owpComLen_eval`, `TCSlib.Cryptography.owpComStr_ofFn` |
| Cryptography/ZeroKnowledge/CommitmentLemmas.lean | 2 | `TCSlib.Cryptography.CommitmentLemmas.ComLoop.init_poly`, `TCSlib.Cryptography.CommitmentLemmas.ComLoop.loopOut_poly` |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean | 2 | `TCSlib.Cryptography.GI.iterUnary_poly`, `TCSlib.Cryptography.GI.peelLoop_poly` |
| Cryptography/ZeroKnowledge/NP.lean | 2 | `TCSlib.Cryptography.LevinReduction.refl`, `TCSlib.Cryptography.outV_pullback_cheat` |
| Cryptography/ZeroKnowledge/NPLemmas.lean | 2 | `TCSlib.Cryptography.LevinTransfer.exists_liftDistinguisher`, `TCSlib.Cryptography.LevinTransfer.polyExpr_eval_const_or_strictMono` |
| Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean | 1 | `TCSlib.Cryptography.ColMachines.eRep_poly` |

### For separate ruling: STATEMENT

| file | items | declarations |
|---|---|---|
| Cryptography/Asymptotic/EnsemblesLemmas.lean | 3 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_pushRed`, `TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam_advice`, `TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam` |
| Cryptography/Asymptotic/UniversalLemmas.lean | 3 | `TCSlib.Cryptography.length_signBits` |
| Cryptography/Asymptotic/UniversalPadding.lean | 5 | `TCSlib.Cryptography.PadQuad.family_inLen`, `TCSlib.Cryptography.PadQuad.lengthRegular_gStr` |
| Cryptography/Encryption/PublicKey/TrapdoorPredictor.lean | 4 | `TCSlib.Cryptography.tdpPredictor_runAtL`, `TCSlib.Cryptography.uprob_tdpPredictor` |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean | 2 | `TCSlib.Cryptography.GGMRed.start_rawInput` |
| Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean | 2 | `TCSlib.Cryptography.PRG.expand_G` |
| Cryptography/ZeroKnowledge/CommitmentLemmas.lean | 2 | `TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisherL_of_runAtL`, `TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisher_of_runAtL` |
| Cryptography/ZeroKnowledge/GraphIsomorphism.lean | 14 | `TCSlib.Cryptography.decGraph_snd`, `TCSlib.Cryptography.giProverRep_efficient`, `TCSlib.Cryptography.giProver_efficient`, `TCSlib.Cryptography.giVerifierRep_efficient`, `TCSlib.Cryptography.giVerifier_efficient`, `TCSlib.Cryptography.gniVerifierRep_efficient`, `TCSlib.Cryptography.gniVerifier_efficient` |
| Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean | 2 | `TCSlib.Cryptography.GI.gniProtocolRep_outV` |
| Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean | 2 | `TCSlib.Cryptography.statClose_giHonestView` |
| Cryptography/ZeroKnowledge/NPLemmas.lean | 1 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_coinLen` |
| Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean | 2 | `TCSlib.Cryptography.colProtocol_outV` |

### STRICT-ONLY (notation, no fix): recorded diagnostics only (Q3)

| file | items | strict errors (A+B) |
|---|---|---|
| Cryptography/Foundations/Experiments.lean | 2 | 6 |
| InformationTheory/Extractors.lean | 4 | 12 |
| InformationTheory/LeftoverHash.lean | 1 | 2 |
| InformationTheory/StatisticalDistance.lean | 2 | 8 |

### HANDED-OFF

By source: #248-historical 9, #248-current 437, provider-pair 102, SY-F07 2, C-F02 58 (total 608).

| file | items |
|---|---|
| Complexity/CircuitComplexity/PPoly.lean | 7 |
| Complexity/CircuitComplexity/Uniform.lean | 2 |
| Complexity/ClassNP/PolyTime.lean | 20 |
| Complexity/ClassNP/PolyTimeBlockLoop.lean | 25 |
| Complexity/ClassNP/PolyTimeBlockTests.lean | 2 |
| Complexity/ClassNP/PolyTimePairing.lean | 20 |
| Complexity/ClassNP/PolyTimePrefix.lean | 6 |
| Complexity/ClassNP/Reductions.lean | 39 |
| Complexity/ClassP/BinaryArith/AddSub.lean | 16 |
| Complexity/ClassP/BinaryArith/Words.lean | 12 |
| Complexity/ClassP/P.lean | 4 |
| Complexity/Randomized/Adleman.lean | 2 |
| Complexity/Randomized/PolyTimeModel.lean | 21 |
| Complexity/Randomized/SipserGacs.lean | 13 |
| Complexity/TuringMachine/Build/Convention.lean | 2 |
| Complexity/TuringMachine/Build/Wrappers.lean | 121 |
| Complexity/TuringMachine/CodeSimulator.lean | 58 |
| Complexity/TuringMachine/Deterministic.lean | 10 |
| Complexity/TuringMachine/Encoding.lean | 13 |
| Complexity/TuringMachine/Simulation.lean | 134 |
| Complexity/TuringMachine/UniversalBlock.lean | 81 |

### NEW failures, by file

| file | seal | unfold | eqn | attribution | classes |
|---|---|---|---|---|---|
| Complexity/ClassP/BinaryArith/Unary.lean | 2 | 0 | 0 | Gate 11 | STAGE2 2 |
| Complexity/Randomized/Build/IterateFind.lean | 1 | 0 | 0 | F-01 | STAGE2 1 |
| Complexity/Randomized/Build/IterateFindHost.lean | 0 | 27 | 0 | DW-9 | STAGE2 26, STAGE2-PROVIDER-READER 1 |
| Complexity/Randomized/Build/PairSplit.lean | 10 | 45 | 0 | Gate 11 | STAGE2 54, STAGE2-PROVIDER-READER 1 |
| Complexity/Randomized/Build/UnaryMul.lean | 3 | 16 | 0 | - | STAGE2 19 |
| Complexity/Randomized/PPT.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Complexity/Randomized/Primitives.lean | 3 | 0 | 0 | Gate 11 | STAGE2 2, SEAL-B-ONLY 1 |
| Complexity/Randomized/SeedMajority/Enumeration.lean | 0 | 1 | 0 | - | STAGE2 1 |
| Complexity/Randomized/UnaryPolynomial.lean | 1 | 0 | 0 | Gate 11 | STAGE2 1 |
| Complexity/TuringMachine/Build/WordTiming.lean | 2 | 0 | 0 | Gate 11 | STAGE2 2 |
| Cryptography/Asymptotic/BlockEncryptor.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Asymptotic/Collections.lean | 5 | 0 | 0 | - | SEAL-B-ONLY 5 |
| Cryptography/Asymptotic/Ensembles.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Asymptotic/GoldreichLevinDomain.lean | 0 | 1 | 0 | - | STAGE2 1 |
| Cryptography/Asymptotic/HardCore/Functions.lean | 13 | 0 | 0 | - | SEAL-B-ONLY 13 |
| Cryptography/Asymptotic/HardCoreCollection.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Asymptotic/HardCoreGL.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Asymptotic/HardCoreGLColl.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Asymptotic/HardCoreGLFamily.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Asymptotic/HardCoreLemmas.lean | 3 | 0 | 0 | - | SEAL-B-ONLY 3 |
| Cryptography/Asymptotic/HardCorePermutation/GoldreichLevin.lean | 6 | 0 | 0 | - | SEAL-B-ONLY 6 |
| Cryptography/Asymptotic/OneWay.lean | 20 | 0 | 0 | - | SEAL-B-ONLY 20 |
| Cryptography/Asymptotic/OneWayYao.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Asymptotic/SamplingFinDist.lean | 0 | 1 | 1 | - | STAGE2 2 |
| Cryptography/Asymptotic/Universal.lean | 2 | 0 | 0 | Gate 35; Gate 11 | SEAL-B-ONLY 2 |
| Cryptography/Candidates/RSA.lean | 3 | 0 | 0 | - | SEAL-B-ONLY 3 |
| Cryptography/Candidates/Rabin.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Encryption/PrivateKey/FromPRG.lean | 5 | 0 | 0 | - | SEAL-B-ONLY 5 |
| Cryptography/Encryption/PublicKey/EnsembleSecurity.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Foundations/Experiments.lean | 2 | 0 | 0 | - | STRICT-ONLY (notation, no fix) 2 |
| Cryptography/NumberTheory/Primality.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean | 1 | 0 | 1 | - | SEAL-B-ONLY 1, STAGE2 1 |
| Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean | 9 | 0 | 0 | - | SEAL-B-ONLY 9 |
| Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean | 7 | 0 | 0 | - | SEAL-B-ONLY 7 |
| Cryptography/Pseudorandom/Generators/Asymptotic/StretchMachine.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/SecureComputation/SpecialEncryptionMulti.lean | 0 | 1 | 0 | - | STAGE2 1 |
| Cryptography/SecureComputation/Yao/HybridProof/GarbledRun.lean | 0 | 1 | 0 | - | STAGE2 1 |
| Cryptography/ZeroKnowledge/Commitment.lean | 3 | 0 | 0 | - | SEAL-B-ONLY 3 |
| Cryptography/ZeroKnowledge/CommitmentLemmas.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/ZeroKnowledge/InteractiveProofs.lean | 0 | 7 | 0 | - | STAGE2 7 |
| Cryptography/ZeroKnowledge/NP.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/ZeroKnowledge/NPLemmas.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |



## Questions for Seyoon

Each question records a reading the job had to apply where the brief leaves room; the inventory follows the recommended option
(first), and nothing in it depends on a different answer except where said.

- **DW10-W1. Moved items.** The brief lists "moved" among CHANGED, and FIXED_SINCE as "the recorded failure is gone at the base".
  (a) *Recommended, applied:* a moved item whose failure is gone is FIXED_SINCE (the move noted in `change`); a moved item that
  still fails is CHANGED ("moved"; with the rest of the comparison). (b) Every moved item is CHANGED, failing or not.
- **DW10-W2. An item recorded under seal A that now fails only under seal B.** (a) *Recommended, applied:* CHANGED ("now
  B-only"), classed SEAL-B-ONLY, so it goes to the separate ruling. (b) FIXED_SINCE (canonical coe-A passes), with the B failure
  listed again as a NEW row.
- **DW10-W3. Controls for owners whose readers are not definitional.** 29 owners have published readers, but none holds by
  `intros; rfl` unsealed (propositional readers), and 2 owners (`NumberTheory/Euclid`, `SequentialZK/SimulatorMachine`) define
  only well-founded recursions, so neither a reader nor `eq_def` is `rfl`-checkable. (a) *Recommended, applied:* the first group
  runs the `eq_def` negative only and is recorded `no reader` with the note "readers exist, none rfl-checkable"; the second gets no
  pair, recorded with the reason. (b) Treat these owners as needing a definitional (`rfl`) reader in Stage 2.
- **DW10-W4. `show`/`change` reads.** The brief's suite item 4 names reads by `show`/`change`, but the archived lexer that the
  brief requires unmodified does not inventory them. (a) *Recommended, applied:* accept; such reads are definitional, and the seals
  (all four variants) catch every one of them as a seal failure in its declaration. (b) Extend the lexer in a later job.


## Evidence

`evidence/SHA256SUMS` lists every evidence file; the top-level `SHA256SUMS` every delivered file. Large directories (collector logs,
seal records and probe sources, seal logs, scan inputs, control harnesses and logs) are in `evidence/zip/<name>.partNN.zip` (at most
90 MB each) with `<name>.partNN.entries.txt` (path, bytes, SHA-256 of each uncompressed file).
