# DW-10 seal-debt inventory (`dw10-seal-inventory`): final

Lead: Claude (cloud worker). 
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
| Olean tree | 613 `.olean`, map `build/olean-tree-map.txt`, SHA-256 `99979c3d2053e6b9f7c74c23c397fe426bacff0a8a8f46a49535fb10f7b35a41`; made read-only (uid 0 bypasses the mode bits: `build/readonly-note.txt`); restore check: Restore check 2026-11-17T12:39:20Z: /home/user/dw10/tree rehashed against build/olean-tree-map.txt (613 entries; map SHA-256 99979c3d2053e6b9f7c74c23c397fe426bacff0a8a8f46a49535fb10f7b35a41).
files in tree: 613; extra 0; missing 0; changed 0 (sha256sum -c rc 0).
worktrees: lead, subA, subB all at f472accd5e000a53d0fbe02b5414435429ce4a70; git status --porcelain: lead shows only the untracked probe dir DW10Probe/ and lock files .lean.lock*; subA, subB clean. No tracked file changed. |

## Parallelism (user override and ruling, 2026-11-17)

The brief's "one Lean process at a time on the host, through one lock" was overridden by the user during the run ("I'm overriding
the 'one Lean process at a time on the host' rule ... Be mindful of making sure each Lean process has enough memory"), then by
Seyoon's ruling (`workflow.md` §4.1 *Lean parallelism*, main #353): cloud workers run a pool of at most nproc Lean processes,
keeping about 2 GB (15%) available. Before the override, the bootstrap, the collectors, the scan kinds probes, the locator, the
first 12 seal probes and the first controls pretest ran strictly one at a time. Afterwards the seals ran in a pool of 4 workers
(lock slots w1..w4 as the counting semaphore; claim files against running a probe twice; a probe starts only when MemAvailable is
at least 4.5 GiB): `seals/PARALLEL.txt`. One probe did run twice. When the workers were restarted after a background time limit,
two of them took over the same dead claim at once, because the takeover is not atomic. That probe was
`SealA_Cryptography_Encryption_PrivateKey_FromPRF_Hybrid`. The two runs gave identical records (rc 0, 0 errors, same log SHA-256)
and wrote only that log, not an olean. Later Lean runs used the same slots: the reader-index attempt 4 probe and the controls. Measured (30 s samples, `logs/memsample.log`): at most 4 Lean processes at once, minimum
MemAvailable 9.4 GiB, peak private (anonymous) memory of one Lean process 518 MiB, peak RSS
3.20 GiB (mostly shared olean mappings). The running seal phase was not interrupted to switch over (the ruling's
instruction); the pool is recorded per phase in `seals/PARALLEL.txt`.

## Who did what

**Lead (Claude, cloud).**
- The setup: preflight, toolchain, cache, bootstrap and tree map.
- The collectors and owner check, item location, the scan, seal generation and every Lean run. That is the seal runs (one process,
  then the four-slot pool after the user's override and the ruling), the controls, and the reader index (attempts 1–4).
- The reconciliation, the classification review of the lead's owner set (`review/lead-review-log.md`, `review/overrides-lead.tsv`),
  the merge of the reviews, the tool corrections they prompted, this report and the delivery.
- Only the lead ran Lean or Lake, fetched the cache, wrote under the delivery path outside `subagents/`, or committed.

**Two sub-agents (Claude, in the same session).** They did analysis only: no Lean, no Lake, no git, no network, and they wrote
only under `evidence/subagents/<name>/`. Each worked from its own read-only worktree at the base (`/home/user/dw10/subA` and
`subB`, sparse `TCSlib/`) and a frozen snapshot of the evidence (`snap-r1`: open items, seal errors, scan, reader index; hashes
in `SNAPSHOT.sha256`). Each reviewed the tool's classification of its owner set's open items, item by item, under the
classification brief (`subagents/REVIEW_BRIEF.md`).
- **sub-A** (SecureComputation, ZeroKnowledge): 290 rows (`subagents/sub-A/overrides-A.tsv`, `review-log.md`).
  - 23 STATEMENT→STAGE2, with the error in the proof on the header's last line.
  - The fix changed in 199 rows: a different definition read, a completed partial fix, or a concrete reader statement.
  - The shadow-transfer design question (DW10-W6) and the two lexer false positives (DW10-W7).
- **sub-B** (Encryption, Authentication, Games, Hashing, Randomness, Implications, Pseudorandom): 120 rows
  (`subagents/sub-B/overrides-sub-B.tsv`, `review-log.md`).
  - 8 STATEMENT→STAGE2. sub-B found the line-only statement test, which the lead then corrected in the tool for every set.
  - The fix changed in 50 rows.
  - The duplicate generated-equation row, which the lead traced to the matcher.

Three corrections were sent to the sub-agents while they worked; their logs record them:
- the `agent` values are `sub-A` / `sub-B`;
- the harness rows are DW10-W5;
- use the attempt 4 reader index.

The lead copied their override files into `review/` unchanged. Rows the seals added after the snapshot were reviewed by the lead
(`review/overrides-lead-delta.tsv`).


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
- **Reader index** (`readers/`): every TCSlib theorem whose type mentions a definition P and whose name is `<P>_*` (or the
  lower-camel form). Attempt 3 added the field equations of structure-valued definitions. Attempt 4, after checkpoint 1, added the
  suffix form `<field>_<P>`, for example `Complexity.NUPPT.coins_ofPolyTimeUniform`: the Randomized library names its field
  equations this way, and attempt 3 had missed 1,452 such readers. Attempts 1–3 are kept. The classification uses as published
  readers `_eq`, `_def`, `_apply`, `_iff`, `_eq_def`, field equations, case lemmas and run/contract lemmas.
- **Classification review** (`review/`, `subagents/`): the tool's class and fix for every open item were reviewed item by item. The
  lead reviewed its owner set, and two sub-agents reviewed theirs from a frozen snapshot of the evidence (`review/`, *Who did what*).
  Each override row gives the class, fix and a note (`confirmed`, `changed …`, `needs a check`); `tools/reconcile.py` applies them.
  The fixes name the published reader to use, or the reader to add with its statement.
- **Reconciliation** (`tools/reconcile.py`, matching rules in its header) and the report (`tools/report_tables.py`, this file).

## Deviations and corrections after checkpoint 1

- **Signed checkpoint commit.** The checkpoint 1 commit `82d1966006fec33ec8c5c34e2bdd0b8a07365e56` was created unsigned, but the
  `git pull --rebase` before the push re-created it under the host's global `commit.gpgsign=true`, so the pushed commit carries an SSH
  signature. It was not rewritten, because a force-push is not allowed (`logs/signing-note.txt`). The final commit and its rebase
  both run with `-c commit.gpgsign=false`, and both commits were checked for a `gpgsig` header before the push.
- **File-level seal diagnostics.** At checkpoint 1, SEAL-0306 and SEAL-0307 (no declaration; `SubHybrids` l.68,
  `inherited_source_attribute_interaction`) were reported CHANGED ("declaration removed"). They are now matched by path, line,
  message class and the named definition, and are STILL_OPEN. They and the same diagnostics elsewhere get no class (DW10-W5).
- **Reader index attempt 4** (above). The classification was re-run with it, and the reviews used it.

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



## Totals and lists

### Seals

Owners sealed (all four variants recorded): 434 of 434. Probes: 1736 owner-variants, 1487 run, 249 deduplicated (identical probe bytes, or identical after the SealA_/SealB_ label normalization).

| variant | owners | requests (sum) | requests (max) | failing owners | failing declarations | errors | failing decls by tier | install/EOF incomplete |
|---|---|---|---|---|---|---|---|---|
| strict-A | 434 | 549103 | 3927 | 67 | 287 | 424 | T1 278 / T2 9 | 0 |
| strict-B | 434 | 549456 | 3928 | 99 | 476 | 737 | T1 467 / T2 9 | 0 |
| coe-A | 434 | 548727 | 3926 | 62 | 258 | 385 | T1 253 / T2 5 | 0 |
| coe-B | 434 | 549080 | 3927 | 94 | 447 | 698 | T1 442 / T2 5 | 0 |

### Controls

Owners: 434; pairs 280; negative only (readers exist, none `rfl`-checkable; DW10-W3) 29; defines nothing 123; no passing candidate 2.

### Explicit-unfold scan

Items: 36127; foreign TCSlib definition items 135 (T1 133, T2 2); by kind: THEOREM/theorem 26796, LOCAL_OR_UNRESOLVED/None 6673, OWNED_DEFINITION/semireducible 2449, FOREIGN_TCSLIB_DEFINITION/semireducible 135, SIMPROC/semireducible 42, FOREIGN_CORE_MATHLIB_DEFINITION/semireducible 19, OWNED_DEFINITION/irreducible 10, FOREIGN_CORE_MATHLIB_DEFINITION/reducible 2, OWNED_DEFINITION/abbrev 1

### Status by source

| source | HANDED-OFF | FIXED_SINCE | STILL_OPEN | CHANGED | NEW | NOT_CHECKED | total |
|---|---|---|---|---|---|---|---|
| #248-historical | 9 | 603 | 106 | 46 | 0 | 0 | 764 |
| #248-current | 437 | 36 | 286 | 54 | 0 | 0 | 813 |
| provider-pair | 102 | 0 | 21 | 1 | 0 | 0 | 124 |
| SG-F07 | 0 | 0 | 9 | 0 | 0 | 0 | 9 |
| SY-F07 | 2 | 0 | 9 | 0 | 0 | 0 | 11 |
| C-F02 | 58 | 0 | 0 | 0 | 0 | 0 | 58 |
| new | 0 | 0 | 0 | 0 | 331 | 0 | 331 |
| total | 608 | 639 | 431 | 101 | 331 | 0 | 2110 |

### Class by tier (open items)

| tier | STAGE2 | STAGE2-PROVIDER-READER | SEAL-B-ONLY | STRICT-ONLY (notation, no fix) | STATEMENT |
|---|---|---|---|---|---|
| T1 | 584 | 17 | 194 | 26 | 3 |
| T2 | 13 | 0 | 0 | 5 | 0 |

### Named findings against their records

| finding | rows | statuses |
|---|---|---|
| SG-F07 | 9 | STILL_OPEN 9 |
| SY-F07 | 11 | HANDED-OFF 2, STILL_OPEN 9 |
| C-F02 | 58 | HANDED-OFF 58 |

### Stage 2 fix list, by file

**TCSlib/Complexity/Randomized/Build/IterateFind.lean** (23 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:3 | `Complexity.IterateFind.computesFunInTime_find` | first error l.602: Unknown constant X | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0051 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.359: Unknown constant `Turing.FinTM.State | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0052 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.359: Invalid dotted identifier notation:  | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0053 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.377: Application type mismatch: The argum | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0054 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.379: Type mismatch (#248 inherited_reache | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0055 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.386: Application type mismatch: The argum | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0056 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.387: Type mismatch (#248 inherited_reache | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0057 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.430: Application type mismatch: The argum | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0058 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.431: Type mismatch (#248 inherited_reache | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0059 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.536: Tactic `introN` failed: There are no | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0060 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.552: Invalid `⟨...⟩` notation: The expect | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| SEAL-0061 | `Complexity.IterateFind.polyTimeComputable_find` | Complexity.IterateFind.polyTimeComputable_find l.553: No goals to be solved (#248 inherite | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0051 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0051 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0052 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0052 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0053 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0053 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0054 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0054 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0055 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0055 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0056 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0056 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0057 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0057 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0058 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0058 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0059 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0059 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0060 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0060 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |
| EFF72:SEAL-0061 | `Complexity.IterateFind.polyTimeComputable_find` | efficiency-72 pair SEAL-0061 Complexity.IterateFind.polyTimeComputable_find (home at rulin | F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it | #347 |

**TCSlib/Complexity/Randomized/Build/IterateFindHost.lean** (32 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:4 | `Complexity.IterateFind.copy_clean` | first error l.217: Application type mismatch: The argument; providers Turing.Cfg.ofWords,T | use Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| NEW:234 | `Complexity.IterateFind.copy_clean` | 219 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:235 | `Complexity.IterateFind.copy_clean` | 219 simp Turing.stateWord | use Turing.stateWord_eq (TCSlib/Complexity/TuringMachine/Build/Loop.lean) | - |
| NEW:236 | `Complexity.IterateFind.copy_clean` | 246 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:237 | `Complexity.IterateFind.copy_clean` | 248 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:238 | `Complexity.IterateFind.copy_clean` | 248 simp Turing.stateWord | use Turing.stateWord_eq (TCSlib/Complexity/TuringMachine/Build/Loop.lean) | - |
| NEW:239 | `Complexity.IterateFind.copy_clean` | 250 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:5 | `Complexity.IterateFind.copy_finish` | first error l.194: Application type mismatch: The argument; providers Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:240 | `Complexity.IterateFind.copy_finish` | 187 simp Turing.Cfg.inputSymbol | use Turing.Cfg.inputSymbol_of_zero (Configuration.lean; the configuration is at input position 0) | - |
| NEW:241 | `Complexity.IterateFind.copy_finish` | 189 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:242 | `Complexity.IterateFind.copy_finish` | 196 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:243 | `Complexity.IterateFind.copy_finish` | 199 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:244 | `Complexity.IterateFind.copy_finish` | 201 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:6 | `Complexity.IterateFind.copy_rewind` | first error l.167: Application type mismatch: The argument; providers Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:245 | `Complexity.IterateFind.copy_rewind` | 162 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:246 | `Complexity.IterateFind.copy_rewind` | 169 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:247 | `Complexity.IterateFind.copy_rewind` | 173 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:248 | `Complexity.IterateFind.copy_rewind` | 175 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:7 | `Complexity.IterateFind.copy_step` | first error l.106: Application type mismatch: The argument; providers Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:249 | `Complexity.IterateFind.copy_step` | 100 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:250 | `Complexity.IterateFind.copy_step` | 108 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:251 | `Complexity.IterateFind.copy_step` | 111 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:252 | `Complexity.IterateFind.copy_step` | 115 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:8 | `Complexity.IterateFind.copy_turn` | first error l.134: Application type mismatch: The argument; providers Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:253 | `Complexity.IterateFind.copy_turn` | 129 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:254 | `Complexity.IterateFind.copy_turn` | 136 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:255 | `Complexity.IterateFind.copy_turn` | 140 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:256 | `Complexity.IterateFind.copy_turn` | 142 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:257 | `Complexity.IterateFind.host_branch` | 342 simp Turing.Cfg.ofWords | use Turing.Cfg.ofWords_def (TCSlib/Complexity/TuringMachine/Build/Convention.lean) | - |
| NEW:258 | `Complexity.IterateFind.host_branch` | 342 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:259 | `Complexity.IterateFind.host_branch` | 342 simp Turing.stateWord | use Turing.stateWord_eq (TCSlib/Complexity/TuringMachine/Build/Loop.lean) | - |
| NEW:260 | `Complexity.IterateFind.host_branch` | 342 simp Turing.FinTM.bufferTape | use Turing.FinTM.bufferTape_eq (TCSlib/Complexity/TuringMachine/Simulation.lean) | - |

**TCSlib/Complexity/Randomized/Build/PairSplit.lean** (49 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:261 | `Turing.FinTM.split_computes` | 643 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:262 | `Turing.FinTM.split_computes` | 643 simp Turing.Cfg.init | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:12 | `Turing.FinTM.split_copy` | first error l.401: Application type mismatch: The argument; providers Turing.Action.apply, | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:263 | `Turing.FinTM.split_copy` | 396 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:264 | `Turing.FinTM.split_copy` | 399 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:265 | `Turing.FinTM.split_copy` | 402 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:266 | `Turing.FinTM.split_copy` | 408 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:267 | `Turing.FinTM.split_copy` | 415 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:268 | `Turing.FinTM.split_dbl_append` | 341 simp Turing.dbl | use Turing.dbl_nil and Turing.dbl_cons | - |
| NEW:13 | `Turing.FinTM.split_run` | first error l.585: 'change' tactic failed, pattern; providers Turing.Action.apply,Turing.A | use Turing.MultiTapeTM.runFrom_succ_eq_step and runFrom_zero to rewrite the runFrom goal to two steps (the `change` reads runFrom), then Turing.MultiTapeTM.step_of_some | - |
| NEW:269 | `Turing.FinTM.split_run` | 578 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:270 | `Turing.FinTM.split_run` | 581 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:272 | `Turing.FinTM.split_run` | 588 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:273 | `Turing.FinTM.split_run` | 591 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:14 | `Turing.FinTM.split_sep` | first error l.440: Application type mismatch: The argument; providers Turing.Action.apply, | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:279 | `Turing.FinTM.split_sep` | 434 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:280 | `Turing.FinTM.split_sep` | 441 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:281 | `Turing.FinTM.split_sep` | 443 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:282 | `Turing.FinTM.split_sep` | 446 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:283 | `Turing.FinTM.split_sep` | 449 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:284 | `Turing.FinTM.split_sep` | 452 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:285 | `Turing.FinTM.split_sep` | 455 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:286 | `Turing.FinTM.split_sep` | 456 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:15 | `Turing.FinTM.split_tail` | first error l.476: Application type mismatch: The argument; providers Turing.Action.apply, | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:287 | `Turing.FinTM.split_tail` | 471 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:288 | `Turing.FinTM.split_tail` | 477 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:289 | `Turing.FinTM.split_tail` | 478 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:290 | `Turing.FinTM.split_tail` | 479 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:291 | `Turing.FinTM.split_tail` | 485 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:292 | `Turing.FinTM.split_tail` | 493 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:16 | `Turing.PairParse.apply_cfg_advance` | first error l.148: Application type mismatch: The argument; providers Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:17 | `Turing.PairParse.apply_cfg_stay` | first error l.137: Application type mismatch: The argument; providers Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:293 | `Turing.PairParse.cfg_inputSymbol` | 110 simp Turing.Cfg.inputSymbol | use Turing.Cfg.inputSymbol_of_end (Configuration.lean; the read is at the end position i = x.length) | - |
| NEW:18 | `Turing.PairParse.cfg_workTapeSymbols` | first error l.126: Type mismatch; providers Turing.Cfg.workTapeSymbols,Turing.FinTM.buffer | use Turing.Cfg.workTapeSymbols_eq and Turing.FinTM.bufferTape_eq | - |
| NEW:19 | `Turing.PairParse.parse_block` | first error l.195: 'change' tactic failed, pattern; providers Turing.MultiTapeTM.runFrom,T | use Turing.MultiTapeTM.runFrom_succ_eq_step and runFrom_zero to rewrite the runFrom goal to two steps (the `change` reads runFrom), then Turing.MultiTapeTM.step_of_some | - |
| NEW:294 | `Turing.PairParse.parse_block` | 197 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:295 | `Turing.PairParse.parse_block` | 210 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:20 | `Turing.PairParse.parse_first` | first error l.165: Application type mismatch: The argument; providers Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:296 | `Turing.PairParse.parse_first` | 160 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:297 | `Turing.PairParse.parse_first` | 167 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:21 | `Turing.PairParse.rewind_run` | first error l.235: Application type mismatch: The argument; providers Turing.Action.apply, | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:298 | `Turing.PairParse.rewind_run` | 233 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:299 | `Turing.PairParse.rewind_run` | 234 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:300 | `Turing.PairParse.rewind_run` | 236 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:301 | `Turing.PairParse.rewind_run` | 237 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:302 | `Turing.PairParse.rewind_run` | 244 unfold Turing.MultiTapeTM.step | use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place of unfolding MultiTapeTM.step, then the Action.apply field equations | - |
| NEW:303 | `Turing.PairParse.rewind_run` | 245 simp Turing.Cfg.workTapeSymbols | use Turing.Cfg.workTapeSymbols_eq (TCSlib/Complexity/TuringMachine/Configuration.lean) | - |
| NEW:304 | `Turing.PairParse.rewind_run` | 248 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| NEW:305 | `Turing.PairParse.rewind_run` | 249 simp Turing.Action.apply | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |

**TCSlib/Complexity/Randomized/Build/UnaryMul.lean** (13 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:22 | `Turing.FinTM.exists_unaryMulTM` | first error l.409: Application type mismatch: The argument; providers Turing.FinTM.Compute | use Turing.FinTM.computesFunInTime_iff | - |
| NEW:23 | `Turing.FinTM.mul_back` | first error l.159: Application type mismatch: The argument | give the private unaryMulTM field equations (unaryMulTM.k = 1, unaryMulTM.State = MulControl) or state mul_tr_back for a MultiTapeTM 1 Bool MulControl that unaryMulTM wraps, in UnaryMul.lean: the read is the k/State field (Fin 1 against Fin unaryMulTM.k) | - |
| NEW:306 | `Turing.FinTM.mul_computes` | 369 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:307 | `Turing.FinTM.mul_computes` | 369 simp Turing.Cfg.init | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:308 | `Turing.FinTM.mul_computes` | 370 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:309 | `Turing.FinTM.mul_computes` | 370 simp Turing.Cfg.init | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:310 | `Turing.FinTM.mul_computes` | 371 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:311 | `Turing.FinTM.mul_computes` | 371 simp Turing.Cfg.init | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:312 | `Turing.FinTM.mul_computes` | 372 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:313 | `Turing.FinTM.mul_computes` | 372 simp Turing.Cfg.init | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:314 | `Turing.FinTM.mul_computes` | 373 simp Turing.MultiTapeTM.initCfg | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:315 | `Turing.FinTM.mul_computes` | 373 simp Turing.Cfg.init | use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, init_workTapes, init_workTapePos; Configuration.lean) | - |
| NEW:24 | `Turing.FinTM.mul_run` | first error l.304: 'change' tactic failed, pattern; providers Turing.MultiTapeTM.runFrom,T | use Turing.MultiTapeTM.runFrom_succ_eq_step and runFrom_zero to rewrite the runFrom goal to two steps (the `change` reads runFrom), then Turing.MultiTapeTM.step_of_some | - |

**TCSlib/Complexity/Randomized/Primitives.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:26 | `Complexity.polyTimeComputable_unaryMulFun` | first error l.138: Invalid X notation: The expected type; providers Complexity.PolyTimeCom | use Complexity.polyTimeComputable_iff | - |
| NEW:28 | `Turing.FinTM.computesFunInTime_unaryMul` | first error l.120: Application type mismatch: The argument; providers Turing.pairDecode | use Turing.FinTM.computesFunInTime_iff and state both sides through one function (two different `match pairDecode z` terms meet; reading pairDecode is not needed) | - |

**TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean** (20 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0090 | `Turing.ModuleHost.clean_emit` | Turing.ModuleHost.clean_emit l.345: Tactic `rcases` failed: `hf : PolyTimeComputable f` is | use Complexity.polyTimeComputable_iff | - |
| EFF72:SEAL-0090 | `Turing.ModuleHost.clean_emit` | efficiency-72 pair SEAL-0090 Turing.ModuleHost.clean_emit (home at ruling TCSlib.Complexit | use Complexity.polyTimeComputable_iff | - |
| SEAL-0089 | `Turing.ModuleHost.clean_install` | Turing.ModuleHost.clean_install l.321: Tactic `rcases` failed: `hf : PolyTimeComputable f` | use Complexity.polyTimeComputable_iff | - |
| EFF72:SEAL-0089 | `Turing.ModuleHost.clean_install` | efficiency-72 pair SEAL-0089 Turing.ModuleHost.clean_install (home at ruling TCSlib.Comple | use Complexity.polyTimeComputable_iff | - |
| SEAL-0095 | `Turing.ModuleHost.host_call` | Turing.ModuleHost.host_call l.537: Type mismatch: After simplification, term (#248 inherit | use Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| EFF72:SEAL-0095 | `Turing.ModuleHost.host_call` | efficiency-72 pair SEAL-0095 Turing.ModuleHost.host_call (home at ruling TCSlib.Complexity | use Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| SEAL-0094 | `Turing.ModuleHost.host_seam` | Turing.ModuleHost.host_seam l.499: Application type mismatch: The argument (#248 inherited | use Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| EFF72:SEAL-0094 | `Turing.ModuleHost.host_seam` | efficiency-72 pair SEAL-0094 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| SEAL-0091 | `Turing.ModuleHost.pad_apply` | Turing.ModuleHost.pad_apply l.393: Application type mismatch: The argument (#248 inherited | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| EFF72:SEAL-0091 | `Turing.ModuleHost.pad_apply` | efficiency-72 pair SEAL-0091 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| SEAL-0092 | `Turing.ModuleHost.pad_run` | Turing.ModuleHost.pad_run l.417: 'change' tactic failed, pattern (#248 inherited_same_step | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| EFF72:SEAL-0092 | `Turing.ModuleHost.pad_run` | efficiency-72 pair SEAL-0092 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| SEAL-0093 | `Turing.ModuleHost.pad_seam` | Turing.ModuleHost.pad_seam l.426: Application type mismatch: The argument (#248 inherited_ | use Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| EFF72:SEAL-0093 | `Turing.ModuleHost.pad_seam` | efficiency-72 pair SEAL-0093 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| SEAL-0087 | `Turing.ModuleHost.stop_clean` | Turing.ModuleHost.stop_clean l.184: Tactic `rfl` failed: The left-hand side (#248 inherite | use Turing.MultiTapeTM.runFrom_zero (zero case), then Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| SEAL-0088 | `Turing.ModuleHost.stop_clean` | Turing.ModuleHost.stop_clean l.193: Type mismatch (#248 inherited_same_step_after_other_re | use Turing.MultiTapeTM.runFrom_zero (zero case), then Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| EFF72:SEAL-0087 | `Turing.ModuleHost.stop_clean` | efficiency-72 pair SEAL-0087 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.MultiTapeTM.runFrom_zero (zero case), then Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| EFF72:SEAL-0088 | `Turing.ModuleHost.stop_clean` | efficiency-72 pair SEAL-0088 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use Turing.MultiTapeTM.runFrom_zero (zero case), then Turing.Cfg.ofWords_def and Turing.stateWord_eq | - |
| SEAL-0086 | `Turing.ModuleHost.stop_step` | Turing.ModuleHost.stop_step l.161: Tactic `rfl` failed: The left-hand side (#248 inherited | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |
| EFF72:SEAL-0086 | `Turing.ModuleHost.stop_step` | efficiency-72 pair SEAL-0086 _private.TCSlib.Complexity.TuringMachine.Build.ModuleHost.0.T | use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean) | - |

**TCSlib/Cryptography/Asymptotic/Collections.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:33 | `TCSlib.Cryptography.FunFamily.toCollection_sampleClose` | TCSlib.Cryptography.FunFamily.toCollection_sampleClose (lines 563; #248 OPEN_TYPED_COINS) | restate hX through TCSlib.Cryptography.FunFamily.toCollection_decD and toCollection_domEquiv_apply, with toCollection_sample_eq and Complexity.NUPPT.coins_ofPolyTimeUniform for the Coins type (the step reads the D and sample fields of toCollection at the type level) | - |
| SEAL-0183 | `TCSlib.Cryptography.FunFamily.toCollection_sampleClose` | TCSlib.Cryptography.FunFamily.toCollection_sampleClose l.564: Type mismatch (#248 inherite | restate hX through TCSlib.Cryptography.FunFamily.toCollection_decD and toCollection_domEquiv_apply, with toCollection_sample_eq and Complexity.NUPPT.coins_ofPolyTimeUniform for the Coins type (the step reads the D and sample fields of toCollection at the type level) | - |

**TCSlib/Cryptography/Asymptotic/Ensembles.lean** (20 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:49 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies (lines 516, 551, 582, 585; #248 OPEN_TYPED_COIN | use TCSlib.Cryptography.acceptProb_def (rewrite both sides before OneWay.uprob_congr) | - |
| SEAL-0189 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies l.524: typeclass instance problem is stuck, it  | use TCSlib.Cryptography.acceptProb_def (rewrite both sides before OneWay.uprob_congr) | - |
| SEAL-0190 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies l.559: unsolved goals (#248 inherited_same_step | use TCSlib.Cryptography.acceptProb_def (rewrite both sides before OneWay.uprob_congr) | - |
| SEAL-0191 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies l.591: Application type mismatch: The argument  | use TCSlib.Cryptography.acceptProb_def (rewrite both sides before OneWay.uprob_congr) | - |
| SEAL-0192 | `TCSlib.Cryptography.Ensemble.Indist.copies` | TCSlib.Cryptography.Ensemble.Indist.copies l.594: Type mismatch (#248 inherited_same_step_ | use TCSlib.Cryptography.acceptProb_def (rewrite both sides before OneWay.uprob_congr) | - |
| H:45 | `TCSlib.Cryptography.Ensemble.Indist.symm` | TCSlib.Cryptography.Ensemble.Indist.symm (lines 334; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_def | - |
| SEAL-0185 | `TCSlib.Cryptography.Ensemble.Indist.symm` | TCSlib.Cryptography.Ensemble.Indist.symm l.342: Type mismatch (#248 inherited_same_native_ | use TCSlib.Cryptography.distAdv_def | - |
| H:48 | `TCSlib.Cryptography.Ensemble.Indist.trans` | TCSlib.Cryptography.Ensemble.Indist.trans (lines 459; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_def | - |
| SEAL-0188 | `TCSlib.Cryptography.Ensemble.Indist.trans` | TCSlib.Cryptography.Ensemble.Indist.trans l.467: Application type mismatch: The argument ( | use TCSlib.Cryptography.distAdv_def | - |
| H:46 | `TCSlib.Cryptography.Ensemble.IndistLit.toIndist` | TCSlib.Cryptography.Ensemble.IndistLit.toIndist (lines 403; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coinLen_eq (rewrite D.coinLen to D.coins.eval before eval_mono) | - |
| SEAL-0186 | `TCSlib.Cryptography.Ensemble.IndistLit.toIndist` | TCSlib.Cryptography.Ensemble.IndistLit.toIndist l.411: Type mismatch (#248 inherited_same_ | use Complexity.NUPPT.coinLen_eq (rewrite D.coinLen to D.coins.eval before eval_mono) | - |
| H:44 | `TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible` | TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible (lines 273; #248 OPEN_INCOMPLETE | use TCSlib.Cryptography.distAdv_def | - |
| SEAL-0184 | `TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible` | TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible l.281: Type mismatch (#248 inher | use TCSlib.Cryptography.distAdv_def | - |
| H:47 | `TCSlib.Cryptography.hybrid_lemma` | TCSlib.Cryptography.hybrid_lemma (lines 447; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_def | - |
| SEAL-0187 | `TCSlib.Cryptography.hybrid_lemma` | TCSlib.Cryptography.hybrid_lemma l.455: Application type mismatch: The argument (#248 inhe | use TCSlib.Cryptography.distAdv_def | - |
| H:50 | `TCSlib.Cryptography.predict_eq` | TCSlib.Cryptography.predict_eq (lines 629; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.acceptProb_def | - |
| SEAL-0193 | `TCSlib.Cryptography.predict_eq` | TCSlib.Cryptography.predict_eq l.638: Tactic `rfl` failed: The left-hand side (#248 inheri | use TCSlib.Cryptography.acceptProb_def | - |
| H:51 | `TCSlib.Cryptography.prediction_lemma` | TCSlib.Cryptography.prediction_lemma (lines 662, 668; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_def | - |
| SEAL-0194 | `TCSlib.Cryptography.prediction_lemma` | TCSlib.Cryptography.prediction_lemma l.671: typeclass instance problem is stuck, it is oft | use TCSlib.Cryptography.distAdv_def | - |
| SEAL-0195 | `TCSlib.Cryptography.prediction_lemma` | TCSlib.Cryptography.prediction_lemma l.677: Type mismatch (#248 inherited_same_native_step | use TCSlib.Cryptography.distAdv_def | - |

**TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean** (11 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0196 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_equiv` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_equiv l.82: Type mismatch (#248 inheri | use TCSlib.Cryptography.acceptProb_def | - |
| SEAL-0197 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_fst` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_coins_fst l.89: Type mismatch (#248 inherite | use TCSlib.Cryptography.acceptProb_def | - |
| SEAL-0204 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_multicopyRed_congr` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_multicopyRed_congr l.501: Type mismatch (#24 | use TCSlib.Cryptography.acceptProb_def | - |
| SEAL-0205 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_multicopyRed_congr` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_multicopyRed_congr l.506: Type mismatch (#24 | use TCSlib.Cryptography.acceptProb_def | - |
| SEAL-0203 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_pushRed` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_pushRed l.325: unsolved goals (#248 inherite | use Complexity.NUPPT.distinguisher_eq and distinguisherL_eq (Adversary.lean) with hB; padFin is not the read | - |
| SEAL-0200 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam l.242: unsolved goals (#248 inherite | use Complexity.NUPPT.distinguisher_eq and distinguisherL_eq (Adversary.lean) with hB to close the pointwise distinguisher goal | - |
| SEAL-0201 | `TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam_advice` | TCSlib.Cryptography.EnsembleLemmas.acceptProb_reparam_advice l.259: unsolved goals (#248 i | use Complexity.NUPPT.distinguisher_eq and distinguisherL_eq (Adversary.lean) with hA to close the pointwise distinguisher goal | - |
| SEAL-0199 | `TCSlib.Cryptography.EnsembleLemmas.distAdv_eq_zero_of_subsingleton` | TCSlib.Cryptography.EnsembleLemmas.distAdv_eq_zero_of_subsingleton l.128: Application type | use TCSlib.Cryptography.distAdv_def | - |
| SEAL-0206 | `TCSlib.Cryptography.EnsembleLemmas.exists_copiesRed` | TCSlib.Cryptography.EnsembleLemmas.exists_copiesRed l.806: Tactic `rfl` failed: The left-h | use Complexity.NUPPT.coins_ofPolyTimeUniform (PPT.lean) | - |
| SEAL-0202 | `TCSlib.Cryptography.EnsembleLemmas.exists_pushRed` | TCSlib.Cryptography.EnsembleLemmas.exists_pushRed l.309: Application type mismatch: The ar | use Complexity.NUPPT.coins_ofPolyTime (PPT.lean) | - |
| SEAL-0198 | `TCSlib.Cryptography.EnsembleLemmas.statClose_of_subsingleton` | TCSlib.Cryptography.EnsembleLemmas.statClose_of_subsingleton l.118: Tactic `introN` failed | use TCSlib.Cryptography.statClose_iff | - |

**TCSlib/Cryptography/Asymptotic/GoldreichLevinDomain.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:41 | `TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc` | first error l.101: Tactic X failed: The left-hand side; providers TCSlib.Cryptography.Hard | use TCSlib.Cryptography.HardcoreBit.secProb_def and TCSlib.Cryptography.uexp_def | - |
| NEW:322 | `TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc` | 105 simp TCSlib.Cryptography.uexp | use TCSlib.Cryptography.uexp_def (TCSlib/Cryptography/Foundations/Probability.lean) | - |

**TCSlib/Cryptography/Asymptotic/HardCore/Functions.lean** (12 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:71 | `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad` | TCSlib.Cryptography.FunFamily.StrongOneWay.glPad (lines 815; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.FunFamily.glPad_f / glPad_inLen_eval / glPad_outLen_eval with TCSlib.Cryptography.glPadInvMachine_runAt to bridge invProbAt of the padded family | - |
| SEAL-0232 | `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad` | TCSlib.Cryptography.FunFamily.StrongOneWay.glPad l.827: Type mismatch (#248 inherited_reac | use TCSlib.Cryptography.FunFamily.glPad_f / glPad_inLen_eval / glPad_outLen_eval with TCSlib.Cryptography.glPadInvMachine_runAt to bridge invProbAt of the padded family | - |
| H:72 | `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore` | TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore (lines 874, 874; #248 OPEN_INCOM | use TCSlib.Cryptography.FunFamily.glPad_f / glPad_inLen_eval / glPad_outLen_eval and invProbAt_eq_uprob to bridge invProbOpt_glFam_eq | - |
| SEAL-0233 | `TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore` | TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore l.897: Type mismatch (#248 inher | use TCSlib.Cryptography.FunFamily.glPad_f / glPad_inLen_eval / glPad_outLen_eval and invProbAt_eq_uprob to bridge invProbOpt_glFam_eq | - |
| H:69 | `TCSlib.Cryptography.FunFamily.glBit_append` | TCSlib.Cryptography.FunFamily.glBit_append (lines 742; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.HardcoreBit.glBit_eq (glBit (x, r) = ip x r) next to HardcoreBit.glBit | - |
| SEAL-0230 | `TCSlib.Cryptography.FunFamily.glBit_append` | TCSlib.Cryptography.FunFamily.glBit_append l.744: Tactic `rfl` failed: The left-hand side  | add TCSlib.Cryptography.HardcoreBit.glBit_eq (glBit (x, r) = ip x r) next to HardcoreBit.glBit | - |
| H:68 | `TCSlib.Cryptography.FunFamily.glPad_f` | TCSlib.Cryptography.FunFamily.glPad_f (lines 735; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.HardcoreBit.glPad_apply | - |
| SEAL-0229 | `TCSlib.Cryptography.FunFamily.glPad_f` | TCSlib.Cryptography.FunFamily.glPad_f l.737: Tactic `rfl` failed: The left-hand side (#248 | use TCSlib.Cryptography.HardcoreBit.glPad_apply | - |
| H:70 | `TCSlib.Cryptography.FunFamily.glPad_f_bijective` | TCSlib.Cryptography.FunFamily.glPad_f_bijective (lines 792; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.HardcoreBit.glPad_apply | - |
| SEAL-0231 | `TCSlib.Cryptography.FunFamily.glPad_f_bijective` | TCSlib.Cryptography.FunFamily.glPad_f_bijective l.795: Tactic `rfl` failed: The left-hand  | use TCSlib.Cryptography.HardcoreBit.glPad_apply | - |
| H:62 | `TCSlib.Cryptography.not_hardCore_const` | TCSlib.Cryptography.not_hardCore_const (lines 263, 267, 267; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.predProb_def (expose the sample space before HardcoreBit.uprob_eq_one_of_forall) | - |
| SEAL-0220 | `TCSlib.Cryptography.not_hardCore_const` | TCSlib.Cryptography.not_hardCore_const l.264: typeclass instance problem is stuck, it is o | use TCSlib.Cryptography.predProb_def (expose the sample space before HardcoreBit.uprob_eq_one_of_forall) | - |

**TCSlib/Cryptography/Asymptotic/HardCoreCollection.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:74 | `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` | TCSlib.Cryptography.Collection.OneWay.glPad_hardCore (lines 355, 356; #248 OPEN_INCOMPLETE | use TCSlib.Cryptography.Collection.hardCore_iff (PermCollection/TrapdoorCollection forms: also oneWay_iff) | - |
| SEAL-0236 | `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` | TCSlib.Cryptography.Collection.OneWay.glPad_hardCore l.356: Invalid `⟨...⟩` notation: The  | use TCSlib.Cryptography.Collection.hardCore_iff (PermCollection/TrapdoorCollection forms: also oneWay_iff) | - |
| SEAL-0237 | `TCSlib.Cryptography.Collection.OneWay.glPad_hardCore` | TCSlib.Cryptography.Collection.OneWay.glPad_hardCore l.357: No goals to be solved (#248 in | use TCSlib.Cryptography.Collection.hardCore_iff (PermCollection/TrapdoorCollection forms: also oneWay_iff) | - |
| H:73 | `TCSlib.Cryptography.Collection.glPad_sample_runAtL` | TCSlib.Cryptography.Collection.glPad_sample_runAtL (lines 178, 175; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.uniform_iff (F.sample_uniform is applied to n; the l.175 error is its consequence) | - |
| SEAL-0234 | `TCSlib.Cryptography.Collection.glPad_sample_runAtL` | TCSlib.Cryptography.Collection.glPad_sample_runAtL l.178: Function expected at (#248 inher | use Complexity.NUPPT.uniform_iff (F.sample_uniform is applied to n; the l.175 error is its consequence) | - |
| SEAL-0235 | `TCSlib.Cryptography.Collection.glPad_sample_runAtL` | TCSlib.Cryptography.Collection.glPad_sample_runAtL l.175: unsolved goals (#248 inherited_s | use Complexity.NUPPT.uniform_iff (F.sample_uniform is applied to n; the l.175 error is its consequence) | - |
| H:75 | `TCSlib.Cryptography.PermCollection.OneWay.glPad` | TCSlib.Cryptography.PermCollection.OneWay.glPad (lines 419; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.PermCollection.oneWay_iff (h : P.OneWay is passed where Collection.OneWay of P.toCollection is expected) | - |
| SEAL-0238 | `TCSlib.Cryptography.PermCollection.OneWay.glPad` | TCSlib.Cryptography.PermCollection.OneWay.glPad l.420: Application type mismatch: The argu | use TCSlib.Cryptography.PermCollection.oneWay_iff (h : P.OneWay is passed where Collection.OneWay of P.toCollection is expected) | - |
| H:76 | `TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore` | TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore (lines 425; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.PermCollection.oneWay_iff (h : P.OneWay is passed where Collection.OneWay of P.toCollection is expected) | - |
| SEAL-0239 | `TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore` | TCSlib.Cryptography.PermCollection.OneWay.glPad_hardCore l.426: Application type mismatch: | use TCSlib.Cryptography.PermCollection.oneWay_iff (h : P.OneWay is passed where Collection.OneWay of P.toCollection is expected) | - |
| H:77 | `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad` | TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad (lines 483; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.TrapdoorCollection.oneWay_iff (h : T.OneWay is passed where Collection.OneWay of the underlying collection is expected) | - |
| SEAL-0240 | `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad` | TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad l.484: Application type mismatch: The  | use TCSlib.Cryptography.TrapdoorCollection.oneWay_iff (h : T.OneWay is passed where Collection.OneWay of the underlying collection is expected) | - |
| H:78 | `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore` | TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore (lines 492; #248 OPEN_INCOMPL | use TCSlib.Cryptography.TrapdoorCollection.oneWay_iff (h : T.OneWay is passed where Collection.OneWay of the underlying collection is expected) | - |
| SEAL-0241 | `TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore` | TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore l.493: Application type misma | use TCSlib.Cryptography.TrapdoorCollection.oneWay_iff (h : T.OneWay is passed where Collection.OneWay of the underlying collection is expected) | - |

**TCSlib/Cryptography/Asymptotic/HardCoreGL.lean** (8 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:79 | `TCSlib.Cryptography.GLLoop.orbit_eq` | TCSlib.Cryptography.GLLoop.orbit_eq (lines 368; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.SelXor.input_eq (SelXor.input m β s = pairEncode (pairEncode (List.replicate m true) (List.ofFn β)) (blocksStr s)) next to SelXor.input | - |
| SEAL-0242 | `TCSlib.Cryptography.GLLoop.orbit_eq` | TCSlib.Cryptography.GLLoop.orbit_eq l.370: Type mismatch (#248 inherited_same_step_after_o | add TCSlib.Cryptography.SelXor.input_eq (SelXor.input m β s = pairEncode (pairEncode (List.replicate m true) (List.ofFn β)) (blocksStr s)) next to SelXor.input | - |
| H:81 | `TCSlib.Cryptography.glMachine_runAt` | TCSlib.Cryptography.glMachine_runAt (lines 752; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.blocksStr_def / take_drop_blocksStr and TCSlib.Cryptography.glMajFun_blocksStr (the rewrite fails on the sealed blocksStr inside glMajFun) | - |
| SEAL-0244 | `TCSlib.Cryptography.glMachine_runAt` | TCSlib.Cryptography.glMachine_runAt l.755: Tactic `rewrite` failed: Did not find an occurr | use TCSlib.Cryptography.blocksStr_def / take_drop_blocksStr and TCSlib.Cryptography.glMajFun_blocksStr (the rewrite fails on the sealed blocksStr inside glMajFun) | - |
| H:82 | `TCSlib.Cryptography.ofFn_glCoinsEquiv` | TCSlib.Cryptography.ofFn_glCoinsEquiv (lines 848; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.blocksStr_def and TCSlib.Cryptography.glBlocks_apply (with NUPPT.coinLen_eq for A.Coins) | - |
| SEAL-0245 | `TCSlib.Cryptography.ofFn_glCoinsEquiv` | TCSlib.Cryptography.ofFn_glCoinsEquiv l.842: Tactic `rfl` failed: The left-hand side (#248 | use TCSlib.Cryptography.blocksStr_def and TCSlib.Cryptography.glBlocks_apply (with NUPPT.coinLen_eq for A.Coins) | - |
| H:80 | `TCSlib.Cryptography.unaryMulFun_poly` | TCSlib.Cryptography.unaryMulFun_poly (lines 488; #248 OPEN_INCOMPLETE) | use Complexity.polyTimeComputable_iff | - |
| SEAL-0243 | `TCSlib.Cryptography.unaryMulFun_poly` | TCSlib.Cryptography.unaryMulFun_poly l.490: Invalid `⟨...⟩` notation: The expected type `P | use Complexity.polyTimeComputable_iff | - |

**TCSlib/Cryptography/Asymptotic/HardCoreLemmas.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:87 | `TCSlib.Cryptography.statClose_glPadSampler` | TCSlib.Cryptography.statClose_glPadSampler (lines 772, 777, 770; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coinLen_eq | - |
| SEAL-0248 | `TCSlib.Cryptography.statClose_glPadSampler` | TCSlib.Cryptography.statClose_glPadSampler l.809: 'show' tactic failed, pattern (#248 inhe | use Complexity.NUPPT.coinLen_eq | - |

**TCSlib/Cryptography/Asymptotic/OneWayYao.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:104 | `TCSlib.Cryptography.OneWay.YaoMachine.ans_layout` | TCSlib.Cryptography.OneWay.YaoMachine.ans_layout (lines 677, 690; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.runAt_eq | - |
| SEAL-0253 | `TCSlib.Cryptography.OneWay.YaoMachine.ans_layout` | TCSlib.Cryptography.OneWay.YaoMachine.ans_layout l.704: Tactic `rfl` failed: The left-hand | use Complexity.NUPPT.runAt_eq | - |
| H:103 | `TCSlib.Cryptography.OneWay.YaoMachine.length_g_iterate_le` | TCSlib.Cryptography.OneWay.YaoMachine.length_g_iterate_le (lines 442; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.inCoins_eq | - |
| SEAL-0250 | `TCSlib.Cryptography.OneWay.YaoMachine.length_g_iterate_le` | TCSlib.Cryptography.OneWay.YaoMachine.length_g_iterate_le l.449: Type mismatch (#248 inher | use Complexity.NUPPT.inCoins_eq | - |
| H:105 | `TCSlib.Cryptography.OneWay.YaoMachine.statClose_sampleAll` | TCSlib.Cryptography.OneWay.YaoMachine.statClose_sampleAll (lines 750; #248 OPEN_TYPED_COIN | add TCSlib.Cryptography.OneWay.YaoMachine.sampleAll_eq (sampleAll T n hM as the equivalence-pushed product of the round samplers; proved by unfold) next to sampleAll in OneWayYao.lean; coinLen_eq does not reach the read | - |
| SEAL-0254 | `TCSlib.Cryptography.OneWay.YaoMachine.statClose_sampleAll` | TCSlib.Cryptography.OneWay.YaoMachine.statClose_sampleAll l.764: Type mismatch (#248 inher | add TCSlib.Cryptography.OneWay.YaoMachine.sampleAll_eq (sampleAll T n hM as the equivalence-pushed product of the round samplers; proved by unfold) next to sampleAll in OneWayYao.lean; coinLen_eq does not reach the read | - |
| SEAL-0251 | `TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_poly` | TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_poly l.456: Type mismatch (#248 inherited_sam | add TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_eq (yaoRaw D T = fun x => match the iterateFind search; proved by unfold) next to yaoRaw and rewrite with it before polyTimeComputable_iterateFind | - |
| SEAL-0252 | `TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_poly` | TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_poly l.457: unsolved goals (#248 inherited_sa | add TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_eq (yaoRaw D T = fun x => match the iterateFind search; proved by unfold) next to yaoRaw and rewrite with it before polyTimeComputable_iterateFind | - |
| H:106 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction (lines 907, 912, 916, 927, 935; #248 OPEN_T | use Complexity.NUPPT.coinLen_eq with TCSlib.Cryptography.OneWay.YaoMachine.ρP_eval to identify A.Coins n with the sampler coins | - |
| SEAL-0255 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.923: Application type mismatch: The argum | use Complexity.NUPPT.coinLen_eq with TCSlib.Cryptography.OneWay.YaoMachine.ρP_eval to identify A.Coins n with the sampler coins | - |
| SEAL-0256 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.928: Application type mismatch: The argum | use Complexity.NUPPT.coinLen_eq with TCSlib.Cryptography.OneWay.YaoMachine.ρP_eval to identify A.Coins n with the sampler coins | - |
| SEAL-0257 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.932: Application type mismatch: The argum | use Complexity.NUPPT.coinLen_eq with TCSlib.Cryptography.OneWay.YaoMachine.ρP_eval to identify A.Coins n with the sampler coins | - |
| SEAL-0258 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.943: Application type mismatch: The argum | use Complexity.NUPPT.coinLen_eq with TCSlib.Cryptography.OneWay.YaoMachine.ρP_eval to identify A.Coins n with the sampler coins | - |
| SEAL-0259 | `TCSlib.Cryptography.OneWay.exists_yaoReduction` | TCSlib.Cryptography.OneWay.exists_yaoReduction l.951: Application type mismatch: The argum | use Complexity.NUPPT.coinLen_eq with TCSlib.Cryptography.OneWay.YaoMachine.ρP_eval to identify A.Coins n with the sampler coins | - |

**TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean** (3 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:91 | `TCSlib.Cryptography.statClose_iff_epsClose_map` | first error l.65: Tactic X failed: There are no additional binders or X bindings in the go | use TCSlib.Cryptography.statClose_iff | - |
| NEW:323 | `TCSlib.Cryptography.uprob_comp_eq_probTrue_map` | 52 rw TCSlib.InformationTheory.FinDist.probTrue | use TCSlib.InformationTheory.FinDist.probTrue_eq (TCSlib/InformationTheory/FinDist.lean) | - |
| NEW:331 | `TCSlib.Cryptography.uprob_comp_eq_probTrue_map` | TCSlib.InformationTheory.FinDist.probTrue.eq_1 | use TCSlib.InformationTheory.FinDist.probTrue_eq (TCSlib/InformationTheory/FinDist.lean) | - |

**TCSlib/Cryptography/Asymptotic/Universal.lean** (9 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:125 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge (lines 748, 749, 754, 756, 784, 786; #248 OPEN_ | use TCSlib.Cryptography.fUniversal_inLen_eval (cast e (w.1, w.2.1) along it) | - |
| SEAL-0285 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.744: Application type mismatch: The argument  | use TCSlib.Cryptography.fUniversal_inLen_eval (cast e (w.1, w.2.1) along it) | - |
| SEAL-0286 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.745: Application type mismatch: The argument  | use TCSlib.Cryptography.fUniversal_inLen_eval (cast e (w.1, w.2.1) along it) | - |
| SEAL-0287 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.750: Application type mismatch: The argument  | use TCSlib.Cryptography.fUniversal_inLen_eval (cast e (w.1, w.2.1) along it) | - |
| SEAL-0288 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.752: Type mismatch (#248 inherited_same_nativ | use TCSlib.Cryptography.fUniversal_inLen_eval (cast e (w.1, w.2.1) along it) | - |
| SEAL-0289 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.780: Application type mismatch: The argument  | use TCSlib.Cryptography.fUniversal_inLen_eval (cast e (w.1, w.2.1) along it) | - |
| SEAL-0290 | `TCSlib.Cryptography.invProbAt_reduction_ge` | TCSlib.Cryptography.invProbAt_reduction_ge l.782: Application type mismatch: The argument  | use TCSlib.Cryptography.fUniversal_inLen_eval (cast e (w.1, w.2.1) along it) | - |
| H:122 | `TCSlib.Cryptography.ofFn_getD_eq_take` | TCSlib.Cryptography.ofFn_getD_eq_take (lines 259; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.padFin_def | - |
| SEAL-0284 | `TCSlib.Cryptography.ofFn_getD_eq_take` | TCSlib.Cryptography.ofFn_getD_eq_take l.259: Type mismatch (#248 inherited_same_native_ste | use TCSlib.Cryptography.padFin_def | - |

**TCSlib/Cryptography/Asymptotic/UniversalLemmas.lean** (5 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0291 | `Complexity.NUPPT.exists_reparam_pre_post` | Complexity.NUPPT.exists_reparam_pre_post l.112: Application type mismatch: The argument (# | use Complexity.NUPPT.coins_ofPolyTime (PPT.lean) | - |
| SEAL-0292 | `Complexity.NUPPT.exists_reparam_pre_post_adv` | Complexity.NUPPT.exists_reparam_pre_post_adv l.160: Application type mismatch: The argumen | use Complexity.NUPPT.coins_ofPolyTime (PPT.lean) | - |
| SEAL-0293 | `TCSlib.Cryptography.length_signBits` | TCSlib.Cryptography.length_signBits l.208: Tactic `rfl` failed: The left-hand side (#248 i | use Turing.signBits_neg, signBits_zero and signBits_pos (Encoding.lean; one per case) | - |
| SEAL-0294 | `TCSlib.Cryptography.length_signBits` | TCSlib.Cryptography.length_signBits l.208: Tactic `rfl` failed: The left-hand side (#248 i | use Turing.signBits_neg, signBits_zero and signBits_pos (Encoding.lean; one per case) | - |
| SEAL-0295 | `TCSlib.Cryptography.length_signBits` | TCSlib.Cryptography.length_signBits l.208: Tactic `rfl` failed: The left-hand side (#248 i | use Turing.signBits_neg, signBits_zero and signBits_pos (Encoding.lean; one per case) | - |

**TCSlib/Cryptography/Asymptotic/UniversalPadding.lean** (10 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:131 | `TCSlib.Cryptography.PadQuad.exists_family` | TCSlib.Cryptography.PadQuad.exists_family (lines 527; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.PadQuad.family_inLen (the step reads the inLen field of family) | - |
| SEAL-0301 | `TCSlib.Cryptography.PadQuad.exists_family` | TCSlib.Cryptography.PadQuad.exists_family l.548: Application type mismatch: The argument ( | use TCSlib.Cryptography.PadQuad.family_inLen (the step reads the inLen field of family) | - |
| H:127 | `TCSlib.Cryptography.PadQuad.family_inLen` | TCSlib.Cryptography.PadQuad.family_inLen (lines 134; #248 OPEN_INCOMPLETE) | prove the reader without rfl through the definition: `unfold family` / family.eq_def (family is sealed after its definition in the whole-file seal) | - |
| SEAL-0298 | `TCSlib.Cryptography.PadQuad.family_inLen` | TCSlib.Cryptography.PadQuad.family_inLen l.134: Type mismatch (#248 inherited_same_native_ | prove the reader without rfl through the definition: `unfold family` / family.eq_def (family is sealed after its definition in the whole-file seal) | - |
| H:129 | `TCSlib.Cryptography.PadQuad.invProbAt_family_le` | TCSlib.Cryptography.PadQuad.invProbAt_family_le (lines 313, 346; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coinLen_eq | - |
| SEAL-0299 | `TCSlib.Cryptography.PadQuad.invProbAt_family_le` | TCSlib.Cryptography.PadQuad.invProbAt_family_le l.314: Type mismatch (#248 inherited_same_ | use Complexity.NUPPT.coinLen_eq | - |
| SEAL-0300 | `TCSlib.Cryptography.PadQuad.invProbAt_family_le` | TCSlib.Cryptography.PadQuad.invProbAt_family_le l.347: Tactic `rewrite` failed: Did not fi | use Complexity.NUPPT.coinLen_eq | - |
| H:126 | `TCSlib.Cryptography.PadQuad.lengthRegular_gStr` | TCSlib.Cryptography.PadQuad.lengthRegular_gStr (lines 124, 125; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.FunFamily.lengthRegular_iff (the unfolded LengthRegular condition) in TCSlib/Cryptography/Asymptotic/OneWay.lean (an owner) | - |
| SEAL-0296 | `TCSlib.Cryptography.PadQuad.lengthRegular_gStr` | TCSlib.Cryptography.PadQuad.lengthRegular_gStr l.124: Type mismatch (#248 inherited_same_n | add TCSlib.Cryptography.FunFamily.lengthRegular_iff (the unfolded LengthRegular condition) in TCSlib/Cryptography/Asymptotic/OneWay.lean (an owner) | - |
| SEAL-0297 | `TCSlib.Cryptography.PadQuad.lengthRegular_gStr` | TCSlib.Cryptography.PadQuad.lengthRegular_gStr l.125: `simp` made no progress (#248 inheri | add TCSlib.Cryptography.FunFamily.lengthRegular_iff (the unfolded LengthRegular condition) in TCSlib/Cryptography/Asymptotic/OneWay.lean (an owner) | - |

**TCSlib/Cryptography/Candidates/Concrete.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| C3-0004 | `TCSlib.Cryptography.Candidates.rbl_loop_poly` | _private.TCSlib.Cryptography.Candidates.Concrete.0.Complexity.polyTimeComputable_iterateFi | add Complexity.polyTimeComputable_iterateFind.match_1_eq (or _iff/_apply) in TCSlib/Complexity/Randomized/Repetition.lean | - |

**TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean** (10 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:108 | `TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly` | TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly (lines 289; #248 OPEN_TYPED_COIN | use TCSlib.Cryptography.blockState_eq (TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean) | - |
| SEAL-0268 | `TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly` | TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly l.289: Application type mismatch | use TCSlib.Cryptography.blockState_eq (TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean) | - |
| H:109 | `TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL` | TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL (lines 333; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.layout_eq, Complexity.NUPPT.advInput_eq and Complexity.NUPPT.coinLen_eq (Randomized/Closure.lean, Randomized/PPT.lean) | - |
| SEAL-0269 | `TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL` | TCSlib.Cryptography.BitPublicKeyScheme.bitwise_enc_runAtL l.333: Tactic `rfl` failed: The  | use Complexity.NUPPT.layout_eq, Complexity.NUPPT.advInput_eq and Complexity.NUPPT.coinLen_eq (Randomized/Closure.lean, Randomized/PPT.lean) | - |
| H:107 | `TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff` | TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff (lines 268, 276; #248 OPEN_INCO | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0266 | `TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff` | TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff l.268: Type mismatch (#248 inhe | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0267 | `TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff` | TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff l.276: Type mismatch (#248 inhe | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:110 | `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` | TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure (lines 554, 530; #248 OPEN_I | use TCSlib.Cryptography.distAdv_def (l.479) and TCSlib.Cryptography.singleDist_def, TCSlib.Cryptography.multiDist_eq (Encryption/PublicKey/Hybrid.lean) (l.455) | - |
| SEAL-0270 | `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` | TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure l.554: Application type mism | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0271 | `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` | TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure l.530: unsolved goals (#248  | use TCSlib.Cryptography.singleDist_def and TCSlib.Cryptography.multiDist_eq (TCSlib/Cryptography/Encryption/PublicKey/Hybrid.lean) | - |

**TCSlib/Cryptography/Encryption/PublicKey/Hybrid.lean** (5 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:115 | `TCSlib.Cryptography.distAdv_tuple_le_mul` | TCSlib.Cryptography.distAdv_tuple_le_mul (lines 620; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_comp (TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean) with P := fun w => pairEncode w.1 (encodeList (List.ofFn w.2)) | - |
| SEAL-0276 | `TCSlib.Cryptography.distAdv_tuple_le_mul` | TCSlib.Cryptography.distAdv_tuple_le_mul l.631: Type mismatch (#248 inherited_same_step_af | use TCSlib.Cryptography.distAdv_comp (TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean) with P := fun w => pairEncode w.1 (encodeList (List.ofFn w.2)) | - |
| H:116 | `TCSlib.Cryptography.exists_hybridBound` | TCSlib.Cryptography.exists_hybridBound (lines 695, 703; #248 OPEN_TYPED_COINS) | l.322: proof-only fix to be identified in the infoview (set_option pp.explicit true): the residual goal prints as X = X, so the sides differ only in hidden arguments; l.330: use TCSlib.Cryptography.distAdv_def on hsingle | - |
| SEAL-0277 | `TCSlib.Cryptography.exists_hybridBound` | TCSlib.Cryptography.exists_hybridBound l.707: unsolved goals (#248 inherited_same_step_aft | proof-only fix to be identified in the infoview (set_option pp.explicit true): the residual goal prints as X = X, so the sides differ only in hidden arguments (likely a stale Decidable instance or an implicit coin length, Enc.coinLen n vs Enc.coins.eval n) | - |
| SEAL-0278 | `TCSlib.Cryptography.exists_hybridBound` | TCSlib.Cryptography.exists_hybridBound l.715: Type mismatch (#248 inherited_same_step_afte | use TCSlib.Cryptography.distAdv_def on hsingle (simpa only [distAdv_def] using hsingle _ _) | - |

**TCSlib/Cryptography/Encryption/PublicKey/HybridMachine.lean** (2 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:114 | `TCSlib.Cryptography.blockEncFun_flatten` | TCSlib.Cryptography.blockEncFun_flatten (lines 217; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.layout_eq, Complexity.NUPPT.advInput_eq and Complexity.NUPPT.coinLen_eq (Randomized/Closure.lean, Randomized/PPT.lean) | - |
| SEAL-0275 | `TCSlib.Cryptography.blockEncFun_flatten` | TCSlib.Cryptography.blockEncFun_flatten l.218: Tactic `rfl` failed: The left-hand side (#2 | use Complexity.NUPPT.layout_eq, Complexity.NUPPT.advInput_eq and Complexity.NUPPT.coinLen_eq (Randomized/Closure.lean, Randomized/PPT.lean) | - |

**TCSlib/Cryptography/Encryption/PublicKey/Trapdoor.lean** (6 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:113 | `TCSlib.Cryptography.acceptProb_owpGenNot_unit` | TCSlib.Cryptography.acceptProb_owpGenNot_unit (lines 808; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.owpGenNot_apply (owpGenNot f B w = (f w.1, w.2, !B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0274 | `TCSlib.Cryptography.acceptProb_owpGenNot_unit` | TCSlib.Cryptography.acceptProb_owpGenNot_unit l.808: Type mismatch (#248 inherited_reviewe | add TCSlib.Cryptography.owpGenNot_apply (owpGenNot f B w = (f w.1, w.2, !B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| H:112 | `TCSlib.Cryptography.acceptProb_owpGen_unit` | TCSlib.Cryptography.acceptProb_owpGen_unit (lines 800; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0273 | `TCSlib.Cryptography.acceptProb_owpGen_unit` | TCSlib.Cryptography.acceptProb_owpGen_unit l.800: Type mismatch (#248 inherited_reviewed_c | add TCSlib.Cryptography.owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| H:111 | `TCSlib.Cryptography.predProb_pkPredictor_eq` | TCSlib.Cryptography.predProb_pkPredictor_eq (lines 792; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean; use owpPredictor_apply | - |
| SEAL-0272 | `TCSlib.Cryptography.predProb_pkPredictor_eq` | TCSlib.Cryptography.predProb_pkPredictor_eq l.792: Type mismatch (#248 inherited_reviewed_ | add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean; use owpPredictor_apply | - |

**TCSlib/Cryptography/Encryption/PublicKey/TrapdoorPredictor.lean** (4 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:117 | `TCSlib.Cryptography.tdpPredictor_runAtL` | TCSlib.Cryptography.tdpPredictor_runAtL (lines 767; #248 OPEN_INCOMPLETE) | proof-only fix to be identified in the infoview (set_option pp.explicit true): the residual goal prints as X = X, so the sides differ only in hidden arguments; candidate: close with decide_eq_decide / Bool.decide_congr | - |
| SEAL-0279 | `TCSlib.Cryptography.tdpPredictor_runAtL` | TCSlib.Cryptography.tdpPredictor_runAtL l.790: unsolved goals (#248 inherited_same_step_af | proof-only fix to be identified in the infoview (set_option pp.explicit true): the residual goal prints as X = X, so the sides differ only in hidden arguments; candidate: close with decide_eq_decide / Bool.decide_congr | - |
| H:118 | `TCSlib.Cryptography.uprob_tdpPredictor` | TCSlib.Cryptography.uprob_tdpPredictor (lines 809; #248 OPEN_TYPED_COINS) | proof-only: rewrite the right-hand ite with the local ite_eq_xor_not before unfolding NUPPT.distinguisherL (or state ite_eq_xor_not for an arbitrary Decidable instance); readers NUPPT.distinguisherL_eq and NUPPT.runAt_eq are already used | - |
| SEAL-0280 | `TCSlib.Cryptography.uprob_tdpPredictor` | TCSlib.Cryptography.uprob_tdpPredictor l.833: unsolved goals (#248 inherited_same_step_aft | proof-only: rewrite the right-hand ite with the local ite_eq_xor_not before unfolding NUPPT.distinguisherL (or state ite_eq_xor_not for an arbitrary Decidable instance); readers NUPPT.distinguisherL_eq and NUPPT.runAt_eq are already used | - |

**TCSlib/Cryptography/HardcoreBit/InnerProduct.lean** (5 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:140 | `TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter` | TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter (lines 229, 228; #248 OPEN_INCOMPL | use TCSlib.Cryptography.predProb_def and TCSlib.Cryptography.invProb_def | - |
| SEAL-0303 | `TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter` | TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter l.242: Application type mismatch:  | use TCSlib.Cryptography.predProb_def and TCSlib.Cryptography.invProb_def | - |
| SEAL-0304 | `TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter` | TCSlib.Cryptography.HardcoreBit.invProb_perfectInverter l.241: unsolved goals (#248 inheri | use TCSlib.Cryptography.predProb_def and TCSlib.Cryptography.invProb_def | - |
| H:139 | `TCSlib.Cryptography.HardcoreBit.uprob_recover_le_invProb` | TCSlib.Cryptography.HardcoreBit.uprob_recover_le_invProb (lines 165; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.invProb_def (expose the sample space before uprob_mono) | - |
| SEAL-0302 | `TCSlib.Cryptography.HardcoreBit.uprob_recover_le_invProb` | TCSlib.Cryptography.HardcoreBit.uprob_recover_le_invProb l.178: typeclass instance problem | use TCSlib.Cryptography.invProb_def (expose the sample space before uprob_mono) | - |

**TCSlib/Cryptography/NumberTheory/Chebyshev.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:156 | `TCSlib.Cryptography.NumberTheory.uprob_prime_bits` | first error l.280: Type mismatch; providers TCSlib.Cryptography.bitsEquiv,TCSlib.Cryptogra | use TCSlib.Cryptography.bitsEquiv_val (published; the first index missed it) | - |

**TCSlib/Cryptography/NumberTheory/Primality.lean** (1 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0305 | `TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt` | TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt l.928: Type mismatch (#248 inher | use Complexity.NUPPT.runAtL_ofPolyTimeUniform / output_ofPolyTimeUniform (PPT.lean) to compute the sampler run | - |

**TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:52 | `TCSlib.Cryptography.GGMRed.length_lookStep_iterate_le` | TCSlib.Cryptography.GGMRed.length_lookStep_iterate_le (lines 400; #248 OPEN_INCOMPLETE) | use Complexity.pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil (ClassNP/PolyTimePairing.lean, TuringMachine/Encoding.lean) | - |
| SEAL-0208 | `TCSlib.Cryptography.GGMRed.length_lookStep_iterate_le` | TCSlib.Cryptography.GGMRed.length_lookStep_iterate_le l.401: Type mismatch (#248 inherited | use Complexity.pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil (ClassNP/PolyTimePairing.lean, TuringMachine/Encoding.lean) | - |
| H:53 | `TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc` | TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc (lines 439; #248 OPEN_INCOMPLETE) | use Complexity.pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil (ClassNP/PolyTimePairing.lean, TuringMachine/Encoding.lean); with GGMRed.tblEnc_nil | - |
| SEAL-0210 | `TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc` | TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc l.440: Tactic `rfl` failed: The left-ha | use Complexity.pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil (ClassNP/PolyTimePairing.lean, TuringMachine/Encoding.lean); with GGMRed.tblEnc_nil | - |
| SEAL-0209 | `TCSlib.Cryptography.GGMRed.lookup_poly` | TCSlib.Cryptography.GGMRed.lookup_poly l.423: Type mismatch (#248 inherited_same_native_st | add Complexity.polyTimeComputable_iterateFind_elim (hypotheses of polyTimeComputable_iterateFind; conclusion PolyTimeComputable fun x => ((List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x))).elim [] (fun i => out (g^[i] x))) in TCSlib/Complexity/Randomized/Repetition.lean; then PolyTimeComputable.congr and a case split on the local match | - |
| SEAL-0207 | `TCSlib.Cryptography.GGMRed.stateLoopFun_poly` | TCSlib.Cryptography.GGMRed.stateLoopFun_poly l.300: Type mismatch (#248 inherited_same_nat | add Complexity.polyTimeComputable_iterateFind_elim (hypotheses of polyTimeComputable_iterateFind; conclusion PolyTimeComputable fun x => ((List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x))).elim [] (fun i => out (g^[i] x))) in TCSlib/Complexity/Randomized/Repetition.lean; then PolyTimeComputable.congr and a case split on the local match | - |
| EFF72:SEAL-0207 | `TCSlib.Cryptography.GGMRed.stateLoopFun_poly` | efficiency-72 pair SEAL-0207 TCSlib.Cryptography.GGMRed.stateLoopFun_poly (home at ruling  | add Complexity.polyTimeComputable_iterateFind_elim (hypotheses of polyTimeComputable_iterateFind; conclusion PolyTimeComputable fun x => ((List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x))).elim [] (fun i => out (g^[i] x))) in TCSlib/Complexity/Randomized/Repetition.lean; then PolyTimeComputable.congr and a case split on the local match | - |

**TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean** (18 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:56 | `TCSlib.Cryptography.GGMRed.concrete_succ` | TCSlib.Cryptography.GGMRed.concrete_succ (lines 112, 113; #248 OPEN_INCOMPLETE) | add GGMRed.buildTreeQ_of_queryOf_none and GGMRed.buildTreeQ_succ_of_queryOf_some (queryOf l1 (next hist) = some x -> buildTreeQ next (b+1) hist = .query x (fun o => buildTreeQ next b (hist ++ [(x, o)]))) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean; use QueryTree.simulate_query, QueryTree.evalLazy_query, simulate_ret, evalLazy_ret | - |
| SEAL-0213 | `TCSlib.Cryptography.GGMRed.concrete_succ` | TCSlib.Cryptography.GGMRed.concrete_succ l.112: Tactic `rfl` failed: The left-hand side (# | add GGMRed.buildTreeQ_of_queryOf_none and GGMRed.buildTreeQ_succ_of_queryOf_some (queryOf l1 (next hist) = some x -> buildTreeQ next (b+1) hist = .query x (fun o => buildTreeQ next b (hist ++ [(x, o)]))) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean; use QueryTree.simulate_query, QueryTree.evalLazy_query, simulate_ret, evalLazy_ret | - |
| SEAL-0214 | `TCSlib.Cryptography.GGMRed.concrete_succ` | TCSlib.Cryptography.GGMRed.concrete_succ l.113: Tactic `rfl` failed: The left-hand side (# | add GGMRed.buildTreeQ_of_queryOf_none and GGMRed.buildTreeQ_succ_of_queryOf_some (queryOf l1 (next hist) = some x -> buildTreeQ next (b+1) hist = .query x (fun o => buildTreeQ next b (hist ++ [(x, o)]))) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean; use QueryTree.simulate_query, QueryTree.evalLazy_query, simulate_ret, evalLazy_ret | - |
| H:55 | `TCSlib.Cryptography.GGMRed.concrete_zero` | TCSlib.Cryptography.GGMRed.concrete_zero (lines 101, 101; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.GGMRed.buildTreeQ_of_queryOf_none (queryOf l1 (next hist) = none -> buildTreeQ next b hist = .ret (verdictOf (next hist))) and GGMRed.buildTreeQ_zero_of_queryOf_some (queryOf l1 (next hist) = some x -> buildTreeQ next 0 hist = .ret false) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean; use QueryTree.simulate_ret, QueryTree.evalLazy_ret | - |
| SEAL-0211 | `TCSlib.Cryptography.GGMRed.concrete_zero` | TCSlib.Cryptography.GGMRed.concrete_zero l.101: Tactic `rfl` failed: The left-hand side (# | add TCSlib.Cryptography.GGMRed.buildTreeQ_of_queryOf_none (queryOf l1 (next hist) = none -> buildTreeQ next b hist = .ret (verdictOf (next hist))) and GGMRed.buildTreeQ_zero_of_queryOf_some (queryOf l1 (next hist) = some x -> buildTreeQ next 0 hist = .ret false) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean; use QueryTree.simulate_ret, QueryTree.evalLazy_ret | - |
| SEAL-0212 | `TCSlib.Cryptography.GGMRed.concrete_zero` | TCSlib.Cryptography.GGMRed.concrete_zero l.101: Tactic `rfl` failed: The left-hand side (# | add TCSlib.Cryptography.GGMRed.buildTreeQ_of_queryOf_none (queryOf l1 (next hist) = none -> buildTreeQ next b hist = .ret (verdictOf (next hist))) and GGMRed.buildTreeQ_zero_of_queryOf_some (queryOf l1 (next hist) = some x -> buildTreeQ next 0 hist = .ret false) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean; use QueryTree.simulate_ret, QueryTree.evalLazy_ret | - |
| H:61 | `TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher` | TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher (lines 784; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ggmBitsDist_apply (ggmBitsDist G A q i j z c = ggmDist (splitHalves o G) A q i j (splitHalves z) c), ggmDist_eq (ggmDist G A q i j = tableDist G (levelAdv G i A) q j) and levelAdv_apply (levelAdv G i A r = (A r).simulate (fun x => prefixAt x i) (fun x v => ggmFrom G x (i + 1) (pairSel (x i) v))) in TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean; add tableDist_apply (tableDist G A q j z c = (A c.2).evalLazy (challengeStream G j z c.1) []) in TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean; use challengeStream_def | - |
| SEAL-0219 | `TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher` | TCSlib.Cryptography.GGMRed.ggmRedMachine_distinguisher l.775: Type mismatch (#248 inherite | add TCSlib.Cryptography.ggmBitsDist_apply (ggmBitsDist G A q i j z c = ggmDist (splitHalves o G) A q i j (splitHalves z) c), ggmDist_eq (ggmDist G A q i j = tableDist G (levelAdv G i A) q j) and levelAdv_apply (levelAdv G i A r = (A r).simulate (fun x => prefixAt x i) (fun x v => ggmFrom G x (i + 1) (pairSel (x i) v))) in TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean; add tableDist_apply (tableDist G A q j z c = (A c.2).evalLazy (challengeStream G j z c.1) []) in TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean; use challengeStream_def | - |
| H:58 | `TCSlib.Cryptography.GGMRed.move_eq` | TCSlib.Cryptography.GGMRed.move_eq (lines 381; #248 OPEN_INCOMPLETE) | use Complexity.NUPPT.runAt_eq and Complexity.NUPPT.runAtL_eq_output_layout (Randomized/PPT.lean, Randomized/Closure.lean) after unfolding the local nextQ | - |
| SEAL-0216 | `TCSlib.Cryptography.GGMRed.move_eq` | TCSlib.Cryptography.GGMRed.move_eq l.368: Tactic `rfl` failed: The left-hand side (#248 in | use Complexity.NUPPT.runAt_eq and Complexity.NUPPT.runAtL_eq_output_layout (Randomized/PPT.lean, Randomized/Closure.lean) after unfolding the local nextQ | - |
| H:59 | `TCSlib.Cryptography.GGMRed.orbit_eq_encState` | TCSlib.Cryptography.GGMRed.orbit_eq_encState (lines 541; #248 OPEN_INCOMPLETE) | use Complexity.StateLoop.orbit_zero (TCSlib/Complexity/Randomized/Build/StateLoop.lean) | - |
| SEAL-0217 | `TCSlib.Cryptography.GGMRed.orbit_eq_encState` | TCSlib.Cryptography.GGMRed.orbit_eq_encState l.530: Type mismatch (#248 inherited_same_nat | use Complexity.StateLoop.orbit_zero (TCSlib/Complexity/Randomized/Build/StateLoop.lean) | - |
| C3-0002 | `TCSlib.Cryptography.GGMRed.queryOf_eq_some_iff` | _private.TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run.0.TCSlib.Cryptograp | add TCSlib.Cryptography.GGMRed.queryOf_eq_some_iff_decode (queryOf l w = some x <-> exists y, pairDecode w = some ([false], y) and decodeFin l y = some x) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean (or move queryOf_eq_some_iff itself next to queryOf); the `split at h` on the foreign matcher queryOf.match_1 (via queryOf_eq) is then not needed | - |
| C3-0003 | `TCSlib.Cryptography.GGMRed.queryOf_eq_some_iff` | _private.TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run.0.TCSlib.Cryptograp | add TCSlib.Cryptography.GGMRed.queryOf_eq_some_iff_decode (queryOf l w = some x <-> exists y, pairDecode w = some ([false], y) and decodeFin l y = some x) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean (or move queryOf_eq_some_iff itself next to queryOf); the `split at h` on the foreign matcher queryOf.match_1 (via queryOf_eq) is then not needed | - |
| H:60 | `TCSlib.Cryptography.GGMRed.runAt_ggmRedMachine` | TCSlib.Cryptography.GGMRed.runAt_ggmRedMachine (lines 752; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.layout_eq and Complexity.NUPPT.advInput_eq (Randomized/Closure.lean, Randomized/PPT.lean) | - |
| SEAL-0218 | `TCSlib.Cryptography.GGMRed.runAt_ggmRedMachine` | TCSlib.Cryptography.GGMRed.runAt_ggmRedMachine l.742: Tactic `rfl` failed: The left-hand s | use Complexity.NUPPT.layout_eq and Complexity.NUPPT.advInput_eq (Randomized/Closure.lean, Randomized/PPT.lean) | - |
| H:57 | `TCSlib.Cryptography.GGMRed.start_rawInput` | TCSlib.Cryptography.GGMRed.start_rawInput (lines 291; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.GGMRed.start_eq (start X = pairEncode [] (pairEncode [] (pairEncode [] []))) and GGMRed.tblOf_nil (tblOf val [] k = []) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean; use GGMRed.histEnc_eq, GGMRed.tblEnc_nil | - |
| SEAL-0215 | `TCSlib.Cryptography.GGMRed.start_rawInput` | TCSlib.Cryptography.GGMRed.start_rawInput l.278: Type mismatch (#248 inherited_same_native | add TCSlib.Cryptography.GGMRed.start_eq (start X = pairEncode [] (pairEncode [] (pairEncode [] []))) and GGMRed.tblOf_nil (tblOf val [] k = []) in TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean; use GGMRed.histEnc_eq, GGMRed.tblEnc_nil | - |

**TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Defs.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0262 | `TCSlib.Cryptography.Ensemble.Indist.pseudorandom` | TCSlib.Cryptography.Ensemble.Indist.pseudorandom l.105: Application type mismatch: The arg | use TCSlib.Cryptography.Ensemble.pseudorandom_iff (TCSlib/Cryptography/Asymptotic/Ensembles.lean) on hY and on the goal | - |
| SEAL-0260 | `TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv` | TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv l.94: Type mismatch (#248 inherited_s | use TCSlib.Cryptography.Ensemble.pseudorandom_iff and TCSlib.Cryptography.prgAdv_eq; add Ensemble.indist_iff (X.Indist Y <-> forall D, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (l.eval n))) and Ensemble.distAdv_uniform (distAdv X ((uniform l).X n) D = distAdv X id D) in TCSlib/Cryptography/Asymptotic/Ensembles.lean | - |
| SEAL-0261 | `TCSlib.Cryptography.Ensemble.uniform_pseudorandom` | TCSlib.Cryptography.Ensemble.uniform_pseudorandom l.99: Type mismatch (#248 inherited_same | use TCSlib.Cryptography.Ensemble.pseudorandom_iff (TCSlib/Cryptography/Asymptotic/Ensembles.lean) | - |
| SEAL-0264 | `TCSlib.Cryptography.PRG.Easy.samplable` | TCSlib.Cryptography.PRG.Easy.samplable l.198: Invalid `⟨...⟩` notation: The expected type  | add TCSlib.Cryptography.Ensemble.samplable_iff (X.Samplable <-> exists s S, PolyTimeComputable S and forall n, StatClose (fun r : Fin (s.eval n) -> Bool => padFin (l.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0) in TCSlib/Cryptography/Asymptotic/Ensembles.lean | - |
| SEAL-0265 | `TCSlib.Cryptography.PRG.Easy.samplable` | TCSlib.Cryptography.PRG.Easy.samplable l.199: No goals to be solved (#248 inherited_same_n | add TCSlib.Cryptography.Ensemble.samplable_iff (X.Samplable <-> exists s S, PolyTimeComputable S and forall n, StatClose (fun r : Fin (s.eval n) -> Bool => padFin (l.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0) in TCSlib/Cryptography/Asymptotic/Ensembles.lean | - |
| C1-0277 | `TCSlib.Cryptography.PRG.Easy.samplable` | 203 simp Complexity.NUPPT.advInput | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0263 | `TCSlib.Cryptography.PRG.secure_iff` | TCSlib.Cryptography.PRG.secure_iff l.189: Type mismatch (#248 inherited_same_native_step) | use TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv (this file, repaired per SEAL-0260) with the local PRG.ensemble_X; PRG.Secure is local | - |

**TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean** (3 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:63 | `TCSlib.Cryptography.exists_owpPredictorSnoc` | TCSlib.Cryptography.exists_owpPredictorSnoc (lines 389, 395; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean; also add owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) there; use owpPredictor_apply and the local owpPredictorSnoc_eq | - |
| SEAL-0221 | `TCSlib.Cryptography.exists_owpPredictorSnoc` | TCSlib.Cryptography.exists_owpPredictorSnoc l.390: Type mismatch (#248 inherited_reviewed_ | add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean; use owpPredictor_apply and the local owpPredictorSnoc_eq | - |
| SEAL-0222 | `TCSlib.Cryptography.exists_owpPredictorSnoc` | TCSlib.Cryptography.exists_owpPredictorSnoc l.396: Tactic `rfl` failed: The left-hand side | add TCSlib.Cryptography.owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |

**TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean** (8 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:64 | `TCSlib.Cryptography.PRG.expand_G` | TCSlib.Cryptography.PRG.expand_G (lines 493; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.prgExt_def (TCSlib/Cryptography/Pseudorandom/Generators.lean); add TCSlib.Cryptography.prgStep_eq (prgStep G s = (G s).2) in TCSlib/Cryptography/Pseudorandom/Generators.lean; with the local oneBitStep_eq | - |
| SEAL-0223 | `TCSlib.Cryptography.PRG.expand_G` | TCSlib.Cryptography.PRG.expand_G l.494: Type mismatch (#248 inherited_same_native_step) | use TCSlib.Cryptography.prgExt_def (TCSlib/Cryptography/Pseudorandom/Generators.lean); add TCSlib.Cryptography.prgStep_eq (prgStep G s = (G s).2) in TCSlib/Cryptography/Pseudorandom/Generators.lean; with the local oneBitStep_eq | - |
| H:65 | `TCSlib.Cryptography.prgAdv_fst` | TCSlib.Cryptography.prgAdv_fst (lines 529; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0224 | `TCSlib.Cryptography.prgAdv_fst` | TCSlib.Cryptography.prgAdv_fst l.530: Tactic `rfl` failed: The left-hand side (#248 inheri | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:66 | `TCSlib.Cryptography.prg_expand` | TCSlib.Cryptography.prg_expand (lines 589; #248 OPEN_TYPED_COINS) | l.217: use the local PRG.expand_G (after SEAL-0223); l.230: add TCSlib.Cryptography.expandRedMachine_coinsEquiv in Pseudorandom/Generators/Asymptotic/StretchMachine.lean; l.241: use prgAdv_eq and distAdv_def | - |
| SEAL-0225 | `TCSlib.Cryptography.prg_expand` | TCSlib.Cryptography.prg_expand l.595: Tactic `rfl` failed: The left-hand side (#248 inheri | use TCSlib.Cryptography.PRG.expand_G (this file; repaired per SEAL-0223) | - |
| SEAL-0226 | `TCSlib.Cryptography.prg_expand` | TCSlib.Cryptography.prg_expand l.608: Application type mismatch: The argument (#248 inheri | add TCSlib.Cryptography.expandRedMachine_coinsEquiv ((expandRedMachine D hF l k hk).Coins n ~= (Fin (l.eval n) -> Bool) x D.Coins n, with List.ofFn (e.symm (a, c)) = List.ofFn a ++ List.ofFn c) in TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/StretchMachine.lean (built from Complexity.NUPPT.wrapCoinsEquiv and Fin.appendEquiv) | - |
| SEAL-0227 | `TCSlib.Cryptography.prg_expand` | TCSlib.Cryptography.prg_expand l.619: Type mismatch (#248 inherited_reached_in_baseline_pr | use TCSlib.Cryptography.prgAdv_eq (Pseudorandom/Generators.lean) and TCSlib.Cryptography.distAdv_def (Foundations/Experiments.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/Commitment.lean** (13 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:146 | `TCSlib.Cryptography.exists_bitComPredictor` | TCSlib.Cryptography.exists_bitComPredictor (lines 596, 600, 604; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.owpPredictorSnoc_eq (Pseudorandom/Generators/Asymptotic/FromPermutation.lean) and TCSlib.Cryptography.acceptProb_def (Foundations/Experiments.lean); add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)), owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) and owpGenNot_apply (owpGenNot f B w = (f w.1, w.2, !B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0309 | `TCSlib.Cryptography.exists_bitComPredictor` | TCSlib.Cryptography.exists_bitComPredictor l.603: Type mismatch (#248 inherited_reviewed_c | use TCSlib.Cryptography.owpPredictorSnoc_eq (Pseudorandom/Generators/Asymptotic/FromPermutation.lean) and TCSlib.Cryptography.acceptProb_def (Foundations/Experiments.lean); add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)), owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) and owpGenNot_apply (owpGenNot f B w = (f w.1, w.2, !B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0310 | `TCSlib.Cryptography.exists_bitComPredictor` | TCSlib.Cryptography.exists_bitComPredictor l.607: Tactic `rfl` failed: The left-hand side  | use TCSlib.Cryptography.owpPredictorSnoc_eq (Pseudorandom/Generators/Asymptotic/FromPermutation.lean) and TCSlib.Cryptography.acceptProb_def (Foundations/Experiments.lean); add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)), owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) and owpGenNot_apply (owpGenNot f B w = (f w.1, w.2, !B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| SEAL-0311 | `TCSlib.Cryptography.exists_bitComPredictor` | TCSlib.Cryptography.exists_bitComPredictor l.611: Tactic `rfl` failed: The left-hand side  | use TCSlib.Cryptography.owpPredictorSnoc_eq (Pseudorandom/Generators/Asymptotic/FromPermutation.lean) and TCSlib.Cryptography.acceptProb_def (Foundations/Experiments.lean); add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)), owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) and owpGenNot_apply (owpGenNot f B w = (f w.1, w.2, !B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean | - |
| H:147 | `TCSlib.Cryptography.exists_bitRed_bound` | TCSlib.Cryptography.exists_bitRed_bound (lines 712; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0312 | `TCSlib.Cryptography.exists_bitRed_bound` | TCSlib.Cryptography.exists_bitRed_bound l.719: Tactic `rfl` failed: The left-hand side (#2 | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| H:145 | `TCSlib.Cryptography.exists_multiRed_bound` | TCSlib.Cryptography.exists_multiRed_bound (lines 308; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.distAdv_def and TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) [or TCSlib.Cryptography.distAdv_comp, Pseudorandom/Indistinguishability.lean] | - |
| SEAL-0308 | `TCSlib.Cryptography.exists_multiRed_bound` | TCSlib.Cryptography.exists_multiRed_bound l.315: Type mismatch (#248 inherited_same_step_a | use TCSlib.Cryptography.distAdv_def and TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) [or TCSlib.Cryptography.distAdv_comp, Pseudorandom/Indistinguishability.lean] | - |
| H:148 | `TCSlib.Cryptography.owpComStr_eq_loopOut` | TCSlib.Cryptography.owpComStr_eq_loopOut (lines 843, 844; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.EnsembleLemmas.blocks_eq (TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean) and TCSlib.Cryptography.padFin_apply (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| SEAL-0313 | `TCSlib.Cryptography.owpComStr_eq_loopOut` | TCSlib.Cryptography.owpComStr_eq_loopOut l.850: Tactic `rfl` failed: The left-hand side (# | use TCSlib.Cryptography.EnsembleLemmas.blocks_eq (TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean) and TCSlib.Cryptography.padFin_apply (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| SEAL-0314 | `TCSlib.Cryptography.owpComStr_eq_loopOut` | TCSlib.Cryptography.owpComStr_eq_loopOut l.851: Type mismatch (#248 inherited_same_native_ | use TCSlib.Cryptography.EnsembleLemmas.blocks_eq (TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean) and TCSlib.Cryptography.padFin_apply (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| H:149 | `TCSlib.Cryptography.owpComStr_polyTimeComputable` | TCSlib.Cryptography.owpComStr_polyTimeComputable (lines 870; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv_symm_ofFn, PermFamily.toFunFamily_codEquiv_ofFn and PermFamily.toFunFamily_f_domEquiv (TCSlib/Cryptography/Asymptotic/OneWay.lean) to restate hFx over Fin n (as OneWayPermutation.evaluator does) | - |
| SEAL-0315 | `TCSlib.Cryptography.owpComStr_polyTimeComputable` | TCSlib.Cryptography.owpComStr_polyTimeComputable l.882: Application type mismatch: The arg | use TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv_symm_ofFn, PermFamily.toFunFamily_codEquiv_ofFn and PermFamily.toFunFamily_f_domEquiv (TCSlib/Cryptography/Asymptotic/OneWay.lean) to restate hFx over Fin n (as OneWayPermutation.evaluator does) | - |

**TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas.lean** (6 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0321 | `TCSlib.Cryptography.CommitmentLemmas.ComLoop.emit_init_of_lt` | TCSlib.Cryptography.CommitmentLemmas.ComLoop.emit_init_of_lt l.499: Type mismatch (#248 in | use TCSlib.Cryptography.EnsembleLemmas.ofFn_padFin_eq_padL (TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean:198) | - |
| SEAL-0319 | `TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisherL_of_runAtL` | TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisherL_of_runAtL l.146: unsolved g | reader to be confirmed by a Lean check: residual goal decide (D.runAtL n (g z) (ofFn c) = [true]) = decide (same printed term) after simp only [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hofn, hrun]; hidden implicit most likely the coin-length index (NUPPT.coinLen, Complexity/Randomized/PPT.lean, reader NUPPT.coinLen_eq published) | - |
| SEAL-0318 | `TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisher_of_runAtL` | TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisher_of_runAtL l.133: unsolved go | reader to be confirmed by a Lean check: the published readers already used (NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq in Complexity/Randomized/PPT.lean and Asymptotic/Adversary.lean) leave a goal whose two printed sides are identical; the hidden difference is most likely the coin-length index of List.ofFn (NUPPT.coinLen / Coins), i.e. add NUPPT.coinLen_eq to the simp set or close with congrArg | - |
| SEAL-0316 | `TCSlib.Cryptography.CommitmentLemmas.acceptProb_eq_uexp_fst` | TCSlib.Cryptography.CommitmentLemmas.acceptProb_eq_uexp_fst l.97: Tactic `rfl` failed: The | add TCSlib.Cryptography.EnsembleLemmas.swapAux_apply (swapAux ζ S ρ (a, b) = (b.1, (a, b.2))) in TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean | - |
| SEAL-0317 | `TCSlib.Cryptography.CommitmentLemmas.distAdv_comm` | TCSlib.Cryptography.CommitmentLemmas.distAdv_comm l.122: Type mismatch (#248 inherited_sam | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| SEAL-0320 | `TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append` | TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append l.234: Tactic `rfl` failed: The lef | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/Defs.lean** (16 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:152 | `TCSlib.Cryptography.AbortRetry.attempt_poly` | TCSlib.Cryptography.AbortRetry.attempt_poly (lines 394; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0324 | `TCSlib.Cryptography.AbortRetry.attempt_poly` | TCSlib.Cryptography.AbortRetry.attempt_poly l.394: Type mismatch (#248 inherited_same_nati | use Complexity.NUPPT.coinLen_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| H:153 | `TCSlib.Cryptography.AbortRetry.exists_retrySimulator` | TCSlib.Cryptography.AbortRetry.exists_retrySimulator (lines 440, 438; #248 OPEN_TYPED_COIN | use Complexity.NUPPT.coins_ofPolyTimeUniform (TCSlib/Complexity/Randomized/PPT.lean:412) for the coins rfl at l.449, and Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) with Complexity.NUPPT.advInput_eq (PPT.lean) for the rfl at l.451 | - |
| SEAL-0325 | `TCSlib.Cryptography.AbortRetry.exists_retrySimulator` | TCSlib.Cryptography.AbortRetry.exists_retrySimulator l.440: Tactic `rfl` failed: The left- | use Complexity.NUPPT.coins_ofPolyTimeUniform (TCSlib/Complexity/Randomized/PPT.lean:412) for the coins rfl at l.449, and Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) with Complexity.NUPPT.advInput_eq (PPT.lean) for the rfl at l.451 | - |
| SEAL-0326 | `TCSlib.Cryptography.AbortRetry.exists_retrySimulator` | TCSlib.Cryptography.AbortRetry.exists_retrySimulator l.438: Application type mismatch: The | use Complexity.NUPPT.coins_ofPolyTimeUniform (TCSlib/Complexity/Randomized/PPT.lean:412) for the coins rfl at l.449, and Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) with Complexity.NUPPT.advInput_eq (PPT.lean) for the rfl at l.451 | - |
| H:154 | `TCSlib.Cryptography.AbortRetry.statClose_retry` | TCSlib.Cryptography.AbortRetry.statClose_retry (lines 513; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0327 | `TCSlib.Cryptography.AbortRetry.statClose_retry` | TCSlib.Cryptography.AbortRetry.statClose_retry l.513: Tactic `introN` failed: There are no | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| H:155 | `TCSlib.Cryptography.PerfectZKAbort.statZK` | TCSlib.Cryptography.PerfectZKAbort.statZK (lines 629, 641, 643; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.Uniform.advice_eq (or NUPPT.uniform_iff) (TCSlib/Complexity/Randomized/PPT.lean) for rw [hSu] at l.640; TCSlib.Cryptography.Protocol.withV_P (ZeroKnowledge/Interaction.lean) at l.652 (state the binder as (π.withV V').ExecCoins (π.withV V').P x); TCSlib.Cryptography.statClose_iff (Asymptotic/Sampling.lean) for intro T at l.654 | - |
| SEAL-0328 | `TCSlib.Cryptography.PerfectZKAbort.statZK` | TCSlib.Cryptography.PerfectZKAbort.statZK l.629: Invalid rewrite argument: Expected an equ | use Complexity.NUPPT.Uniform.advice_eq (or NUPPT.uniform_iff) (TCSlib/Complexity/Randomized/PPT.lean) for rw [hSu] at l.640; TCSlib.Cryptography.Protocol.withV_P (ZeroKnowledge/Interaction.lean) at l.652 (state the binder as (π.withV V').ExecCoins (π.withV V').P x); TCSlib.Cryptography.statClose_iff (Asymptotic/Sampling.lean) for intro T at l.654 | - |
| SEAL-0329 | `TCSlib.Cryptography.PerfectZKAbort.statZK` | TCSlib.Cryptography.PerfectZKAbort.statZK l.641: Application type mismatch: The argument ( | use Complexity.NUPPT.Uniform.advice_eq (or NUPPT.uniform_iff) (TCSlib/Complexity/Randomized/PPT.lean) for rw [hSu] at l.640; TCSlib.Cryptography.Protocol.withV_P (ZeroKnowledge/Interaction.lean) at l.652 (state the binder as (π.withV V').ExecCoins (π.withV V').P x); TCSlib.Cryptography.statClose_iff (Asymptotic/Sampling.lean) for intro T at l.654 | - |
| SEAL-0330 | `TCSlib.Cryptography.PerfectZKAbort.statZK` | TCSlib.Cryptography.PerfectZKAbort.statZK l.643: Tactic `introN` failed: There are no addi | use Complexity.NUPPT.Uniform.advice_eq (or NUPPT.uniform_iff) (TCSlib/Complexity/Randomized/PPT.lean) for rw [hSu] at l.640; TCSlib.Cryptography.Protocol.withV_P (ZeroKnowledge/Interaction.lean) at l.652 (state the binder as (π.withV V').ExecCoins (π.withV V').P x); TCSlib.Cryptography.statClose_iff (Asymptotic/Sampling.lean) for intro T at l.654 | - |
| H:156 | `TCSlib.Cryptography.negligible_inv_pow_sqrt_div` | TCSlib.Cryptography.negligible_inv_pow_sqrt_div (lines 673; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| SEAL-0331 | `TCSlib.Cryptography.negligible_inv_pow_sqrt_div` | TCSlib.Cryptography.negligible_inv_pow_sqrt_div l.673: Tactic `introN` failed: There are n | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| H:151 | `TCSlib.Cryptography.perfectZK_zeroRounds` | TCSlib.Cryptography.perfectZK_zeroRounds (lines 291, 292; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0322 | `TCSlib.Cryptography.perfectZK_zeroRounds` | TCSlib.Cryptography.perfectZK_zeroRounds l.291: Application type mismatch: The argument (# | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0323 | `TCSlib.Cryptography.perfectZK_zeroRounds` | TCSlib.Cryptography.perfectZK_zeroRounds l.292: No goals to be solved (#248 inherited_same | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| C1-0300 | `TCSlib.Cryptography.EncodingMachines.bitsToNat_eq_blockVal` | 225 simp TCSlib.Cryptography.bitsToNat | use TCSlib.Cryptography.bitsToNat_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0301 | `TCSlib.Cryptography.EncodingMachines.bitsToNat_eq_blockVal` | 228 unfold TCSlib.Cryptography.bitsToNat | use TCSlib.Cryptography.bitsToNat_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0306 | `TCSlib.Cryptography.EncodingMachines.fisherYates_val_eq` | 684 unfold TCSlib.Cryptography.fisherYates | add TCSlib.Cryptography.fisherYates_def (fisherYates n c = (List.finRange n).foldr (fun i σ => Equiv.swap i ⟨(i + c i % (n - i)) % n, _⟩ * σ) 1) in TCSlib/Cryptography/Asymptotic/Permutations.lean | - |
| C1-0307 | `TCSlib.Cryptography.EncodingMachines.permFromCoins_getD_val` | 721 unfold TCSlib.Cryptography.permFromCoins | add TCSlib.Cryptography.permFromCoins_def (permFromCoins n k T b = if h : ∀ i, (rejectionSample (n - i) k T (b i)).isSome then some (fisherYates n fun i => ((rejectionSample (n - i) k T (b i)).get (h i)).val) else none) in TCSlib/Cryptography/Asymptotic/Permutations.lean | - |
| C1-0303 | `TCSlib.Cryptography.EncodingMachines.rejectionSample_eq_dite` | 618 unfold TCSlib.Cryptography.rejectionSample | use TCSlib.Cryptography.rejectionSample_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0304 | `TCSlib.Cryptography.EncodingMachines.rejectionSample_eq_dite` | 625 unfold TCSlib.Cryptography.uniformFromBits | use TCSlib.Cryptography.uniformFromBits_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0305 | `TCSlib.Cryptography.EncodingMachines.rejectionSample_eq_dite` | 631 unfold TCSlib.Cryptography.uniformFromBits | use TCSlib.Cryptography.uniformFromBits_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean** (33 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:162 | `TCSlib.Cryptography.Riso_witnessRelation` | TCSlib.Cryptography.Riso_witnessRelation (lines 340; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.riso_iff (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:185) to convert GI.Riso_decidable to the local Riso (simp only [GI.riso_iff] and unfold the local Riso) | - |
| SEAL-0333 | `TCSlib.Cryptography.Riso_witnessRelation` | TCSlib.Cryptography.Riso_witnessRelation l.346: Type mismatch (#248 inherited_same_native_ | use TCSlib.Cryptography.GI.riso_iff (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:185) to convert GI.Riso_decidable to the local Riso (simp only [GI.riso_iff] and unfold the local Riso) | - |
| H:161 | `TCSlib.Cryptography.decGraph_snd` | TCSlib.Cryptography.decGraph_snd (lines 216; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.decGraph_snd_apply (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:151) (funext u v; rw [decGraph_snd_apply]; rfl) | - |
| SEAL-0332 | `TCSlib.Cryptography.decGraph_snd` | TCSlib.Cryptography.decGraph_snd l.216: Type mismatch (#248 inherited_same_native_step) | use TCSlib.Cryptography.decGraph_snd_apply (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:151) (funext u v; rw [decGraph_snd_apply]; rfl) | - |
| H:173 | `TCSlib.Cryptography.giProtocolRep_proverBounded` | TCSlib.Cryptography.giProtocolRep_proverBounded (lines 943; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.giProverRep_next (GraphIsomorphism/Proofs.lean) to rewrite GI.giProverRep.next in GI.giProverRep_length_le to the local giProverRep body | - |
| SEAL-0344 | `TCSlib.Cryptography.giProtocolRep_proverBounded` | TCSlib.Cryptography.giProtocolRep_proverBounded l.954: Type mismatch (#248 inherited_same_ | use TCSlib.Cryptography.GI.giProverRep_next (GraphIsomorphism/Proofs.lean) to rewrite GI.giProverRep.next in GI.giProverRep_length_le to the local giProverRep body | - |
| H:172 | `TCSlib.Cryptography.giProtocol_proverBounded` | TCSlib.Cryptography.giProtocol_proverBounded (lines 938; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.giProver_next_nil' and GI.giProver_next_cons' (GraphIsomorphism/Proofs.lean): rewrite (cases hist) GI.giProver.next in GI.giProver_length_le x y r hist to the local giProver body | - |
| SEAL-0343 | `TCSlib.Cryptography.giProtocol_proverBounded` | TCSlib.Cryptography.giProtocol_proverBounded l.949: Type mismatch (#248 inherited_same_nat | use TCSlib.Cryptography.GI.giProver_next_nil' and GI.giProver_next_cons' (GraphIsomorphism/Proofs.lean): rewrite (cases hist) GI.giProver.next in GI.giProver_length_le x y r hist to the local giProver body | - |
| H:168 | `TCSlib.Cryptography.giProverRep_efficient` | TCSlib.Cryptography.giProverRep_efficient (lines 879; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.giProverRep_coins and GI.giProverRep_next (GraphIsomorphism/Proofs.lean) to prove giProverRep = GI.giProverRep, then transport GI.giProverRep_efficient | - |
| SEAL-0339 | `TCSlib.Cryptography.giProverRep_efficient` | TCSlib.Cryptography.giProverRep_efficient l.890: Type mismatch (#248 inherited_same_native | use TCSlib.Cryptography.GI.giProverRep_coins and GI.giProverRep_next (GraphIsomorphism/Proofs.lean) to prove giProverRep = GI.giProverRep, then transport GI.giProverRep_efficient | - |
| H:164 | `TCSlib.Cryptography.giProver_efficient` | TCSlib.Cryptography.giProver_efficient (lines 852; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.GI.giProver_coins (GI.giProver.coins = .normal 1 2) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean; with the published GI.giProver_next_nil' and GI.giProver_next_cons' (Proofs.lean) prove giProver = GI.giProver in GraphIsomorphism.lean (structure eta, funext, cases hist) and transport GI.giProver_efficient | - |
| SEAL-0335 | `TCSlib.Cryptography.giProver_efficient` | TCSlib.Cryptography.giProver_efficient l.863: Type mismatch (#248 inherited_same_native_st | add TCSlib.Cryptography.GI.giProver_coins (GI.giProver.coins = .normal 1 2) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean; with the published GI.giProver_next_nil' and GI.giProver_next_cons' (Proofs.lean) prove giProver = GI.giProver in GraphIsomorphism.lean (structure eta, funext, cases hist) and transport GI.giProver_efficient | - |
| H:169 | `TCSlib.Cryptography.giVerifierRep_efficient` | TCSlib.Cryptography.giVerifierRep_efficient (lines 885; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.GI.giVerifierRep_coins (GI.giVerifierRep.coins = <its coin polynomial>) in GraphIsomorphism/Proofs.lean; with the published GI.giVerifierRep_next prove giVerifierRep = GI.giVerifierRep and transport GI.giVerifierRep_efficient | - |
| SEAL-0340 | `TCSlib.Cryptography.giVerifierRep_efficient` | TCSlib.Cryptography.giVerifierRep_efficient l.896: Type mismatch (#248 inherited_same_nati | add TCSlib.Cryptography.GI.giVerifierRep_coins (GI.giVerifierRep.coins = <its coin polynomial>) in GraphIsomorphism/Proofs.lean; with the published GI.giVerifierRep_next prove giVerifierRep = GI.giVerifierRep and transport GI.giVerifierRep_efficient | - |
| H:165 | `TCSlib.Cryptography.giVerifier_efficient` | TCSlib.Cryptography.giVerifier_efficient (lines 862; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.GI.giVerifier_coins (GI.giVerifier.coins = <its coin polynomial>) in GraphIsomorphism/Proofs.lean; with the published next readers GI.giVerifier_next_nil', giVerifier_next_one, giVerifier_next_two', giVerifier_next_long' (cover every history) prove giVerifier = GI.giVerifier and transport GI.giVerifier_efficient | - |
| SEAL-0336 | `TCSlib.Cryptography.giVerifier_efficient` | TCSlib.Cryptography.giVerifier_efficient l.873: Type mismatch (#248 inherited_same_native_ | add TCSlib.Cryptography.GI.giVerifier_coins (GI.giVerifier.coins = <its coin polynomial>) in GraphIsomorphism/Proofs.lean; with the published next readers GI.giVerifier_next_nil', giVerifier_next_one, giVerifier_next_two', giVerifier_next_long' (cover every history) prove giVerifier = GI.giVerifier and transport GI.giVerifier_efficient | - |
| H:175 | `TCSlib.Cryptography.gi_efficientProverProofErr` | TCSlib.Cryptography.gi_efficientProverProofErr (lines 969; #248 OPEN_INCOMPLETE) | bridge the shadows of GI.gi_efficientProverProofErr: giProver and giVerifier (as for giProver_efficient/giVerifier_efficient: add GI.giProver_coins, GI.giVerifier_coins), giProtocol (add GI.giProtocol_rounds, GI.giProtocol_verifierFirst; _P/_V published), in GraphIsomorphism/Proofs.lean; Riso via the published GI.riso_iff and Liso via the published GI.mem_Liso_iff (Proofs.lean:165) | - |
| SEAL-0347 | `TCSlib.Cryptography.gi_efficientProverProofErr` | TCSlib.Cryptography.gi_efficientProverProofErr l.980: Application type mismatch: The argum | bridge the shadows of GI.gi_efficientProverProofErr: giProver and giVerifier (as for giProver_efficient/giVerifier_efficient: add GI.giProver_coins, GI.giVerifier_coins), giProtocol (add GI.giProtocol_rounds, GI.giProtocol_verifierFirst; _P/_V published), in GraphIsomorphism/Proofs.lean; Riso via the published GI.riso_iff and Liso via the published GI.mem_Liso_iff (Proofs.lean:165) | - |
| H:176 | `TCSlib.Cryptography.gi_rep_efficientProverProof` | TCSlib.Cryptography.gi_rep_efficientProverProof (lines 986; #248 OPEN_INCOMPLETE) | bridge the shadows of GI.gi_rep_efficientProverProof: giProverRep (published GI.giProverRep_coins/_next), giVerifierRep (add GI.giVerifierRep_coins; _next published), giProtocolRep (published GI.giProtocolRep_P/_V/_rounds/_verifierFirst), Riso (published GI.riso_iff) and Liso (published GI.mem_Liso_iff, Proofs.lean:165) | - |
| SEAL-0348 | `TCSlib.Cryptography.gi_rep_efficientProverProof` | TCSlib.Cryptography.gi_rep_efficientProverProof l.997: Application type mismatch: The argu | bridge the shadows of GI.gi_rep_efficientProverProof: giProverRep (published GI.giProverRep_coins/_next), giVerifierRep (add GI.giVerifierRep_coins; _next published), giProtocolRep (published GI.giProtocolRep_P/_V/_rounds/_verifierFirst), Riso (published GI.riso_iff) and Liso (published GI.mem_Liso_iff, Proofs.lean:165) | - |
| H:174 | `TCSlib.Cryptography.gniProtocol_proverBounded` | TCSlib.Cryptography.gniProtocol_proverBounded (lines 949, 950; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.gniProver_next (GraphIsomorphism/Proofs.lean:214) to rewrite GI.gniProver.next in GI.gniProver_length_le to the local gniProver body (both conjuncts, l.960/961) | - |
| SEAL-0345 | `TCSlib.Cryptography.gniProtocol_proverBounded` | TCSlib.Cryptography.gniProtocol_proverBounded l.960: Type mismatch (#248 inherited_same_na | use TCSlib.Cryptography.GI.gniProver_next (GraphIsomorphism/Proofs.lean:214) to rewrite GI.gniProver.next in GI.gniProver_length_le to the local gniProver body (both conjuncts, l.960/961) | - |
| SEAL-0346 | `TCSlib.Cryptography.gniProtocol_proverBounded` | TCSlib.Cryptography.gniProtocol_proverBounded l.961: Type mismatch (#248 inherited_same_na | use TCSlib.Cryptography.GI.gniProver_next (GraphIsomorphism/Proofs.lean:214) to rewrite GI.gniProver.next in GI.gniProver_length_le to the local gniProver body (both conjuncts, l.960/961) | - |
| H:167 | `TCSlib.Cryptography.gniVerifierRep_efficient` | TCSlib.Cryptography.gniVerifierRep_efficient (lines 874; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.gniVerifierRep_coins and GI.gniVerifierRep_next (GraphIsomorphism/Proofs.lean) to prove gniVerifierRep = GI.gniVerifierRep, then transport GI.gniVerifierRep_efficient | - |
| SEAL-0338 | `TCSlib.Cryptography.gniVerifierRep_efficient` | TCSlib.Cryptography.gniVerifierRep_efficient l.885: Type mismatch (#248 inherited_same_nat | use TCSlib.Cryptography.GI.gniVerifierRep_coins and GI.gniVerifierRep_next (GraphIsomorphism/Proofs.lean) to prove gniVerifierRep = GI.gniVerifierRep, then transport GI.gniVerifierRep_efficient | - |
| H:166 | `TCSlib.Cryptography.gniVerifier_efficient` | TCSlib.Cryptography.gniVerifier_efficient (lines 868; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.GI.gniVerifier_coins (GI.gniVerifier.coins = <its coin polynomial>) in GraphIsomorphism/Proofs.lean; with the published GI.gniVerifier_next_nil', gniVerifier_next_one, gniVerifier_next_long' prove gniVerifier = GI.gniVerifier and transport GI.gniVerifier_efficient | - |
| SEAL-0337 | `TCSlib.Cryptography.gniVerifier_efficient` | TCSlib.Cryptography.gniVerifier_efficient l.879: Type mismatch (#248 inherited_same_native | add TCSlib.Cryptography.GI.gniVerifier_coins (GI.gniVerifier.coins = <its coin polynomial>) in GraphIsomorphism/Proofs.lean; with the published GI.gniVerifier_next_nil', gniVerifier_next_one, gniVerifier_next_long' prove gniVerifier = GI.gniVerifier and transport GI.gniVerifier_efficient | - |
| H:171 | `TCSlib.Cryptography.gni_interactiveProof` | TCSlib.Cryptography.gni_interactiveProof (lines 931; #248 OPEN_INCOMPLETE) | bridge the shadows of GI.gni_interactiveProof: gniVerifierRep (published GI.gniVerifierRep_coins, GI.gniVerifierRep_next), gniProtocolRep (add GI.gniProtocolRep_P, _rounds, _verifierFirst; _V published) in GraphIsomorphism/Proofs.lean, and Lniso via the published GI.mem_Lniso_iff | - |
| SEAL-0342 | `TCSlib.Cryptography.gni_interactiveProof` | TCSlib.Cryptography.gni_interactiveProof l.942: Application type mismatch: The argument (# | bridge the shadows of GI.gni_interactiveProof: gniVerifierRep (published GI.gniVerifierRep_coins, GI.gniVerifierRep_next), gniProtocolRep (add GI.gniProtocolRep_P, _rounds, _verifierFirst; _V published) in GraphIsomorphism/Proofs.lean, and Lniso via the published GI.mem_Lniso_iff | - |
| H:170 | `TCSlib.Cryptography.gni_interactiveProofErr` | TCSlib.Cryptography.gni_interactiveProofErr (lines 912; #248 OPEN_INCOMPLETE) | bridge every shadow in GI.gni_interactiveProofErr's type: gniVerifier (as for gniVerifier_efficient: add GI.gniVerifier_coins), gniProtocol (add GI.gniProtocol_rounds and GI.gniProtocol_verifierFirst; GI.gniProtocol_P/_V published; GI.gniProver needs add GI.gniProver_coins, next via GI.gniProver_next), use the published GI.mem_Lniso_iff (Proofs.lean:174) for Lniso, and add GI.permFailBound_def and GI.instanceVertices_def (defining equations) in GraphIsomorphism/Proofs.lean | - |
| SEAL-0341 | `TCSlib.Cryptography.gni_interactiveProofErr` | TCSlib.Cryptography.gni_interactiveProofErr l.923: Application type mismatch: The argument | bridge every shadow in GI.gni_interactiveProofErr's type: gniVerifier (as for gniVerifier_efficient: add GI.gniVerifier_coins), gniProtocol (add GI.gniProtocol_rounds and GI.gniProtocol_verifierFirst; GI.gniProtocol_P/_V published; GI.gniProver needs add GI.gniProver_coins, next via GI.gniProver_next), use the published GI.mem_Lniso_iff (Proofs.lean:174) for Lniso, and add GI.permFailBound_def and GI.instanceVertices_def (defining equations) in GraphIsomorphism/Proofs.lean | - |
| H:163 | `TCSlib.Cryptography.permCoinLen_le` | TCSlib.Cryptography.permCoinLen_le (lines 375; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.permTrials_eq (TCSlib/Cryptography/Asymptotic/Permutations.lean:445) | - |
| SEAL-0334 | `TCSlib.Cryptography.permCoinLen_le` | TCSlib.Cryptography.permCoinLen_le l.390: Type mismatch (#248 inherited_same_native_step) | use TCSlib.Cryptography.permTrials_eq (TCSlib/Cryptography/Asymptotic/Permutations.lean:445) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete.lean** (4 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0349 | `TCSlib.Cryptography.GI.negligible_mul_permFailBound` | TCSlib.Cryptography.GI.negligible_mul_permFailBound l.62: Type mismatch (#248 inherited_sa | add TCSlib.Cryptography.GI.instanceVertices_def (instanceVertices N = Nat.sqrt ((N - 2) / 3)) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | - |
| C1-0308 | `TCSlib.Cryptography.GI.negligible_mul_permFailBound` | 67 unfold TCSlib.Cryptography.GI.permFailBound | add TCSlib.Cryptography.GI.permFailBound_def (permFailBound n = n * (2 : ℝ)⁻¹ ^ n) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | - |
| SEAL-0350 | `TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le` | TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le l.208: Invalid `⟨...⟩` notation: The expected | use TCSlib.Cryptography.GI.isomorphic_iff (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |
| SEAL-0351 | `TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le` | TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le l.211: Invalid `⟨...⟩` notation: The expected | use TCSlib.Cryptography.GI.isomorphic_iff (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean** (4 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0355 | `TCSlib.Cryptography.GI.dec_sndD_last` | TCSlib.Cryptography.GI.dec_sndD_last l.315: Application type mismatch: The argument (#248  | use Complexity.pairSndD_of_pairDecode_eq_none (ClassNP/PolyTimePairing.lean) with Turing.pairDecode_nil (TuringMachine/Encoding.lean) in place of rfl at l.316 | - |
| SEAL-0353 | `TCSlib.Cryptography.GI.iterate_pairSndD_nil` | TCSlib.Cryptography.GI.iterate_pairSndD_nil l.89: Type mismatch (#248 inherited_same_nativ | use Complexity.pairSndD_of_pairDecode_eq_none (ClassNP/PolyTimePairing.lean) with Turing.pairDecode_nil (TuringMachine/Encoding.lean) to rewrite pairSndD [] = [] before the recursive call | - |
| SEAL-0352 | `TCSlib.Cryptography.GI.length_pairSndD_le` | TCSlib.Cryptography.GI.length_pairSndD_le l.75: Tactic `rfl` failed: The left-hand side (# | use Complexity.pairSndD_of_pairDecode_eq_none (TCSlib/Complexity/ClassNP/PolyTimePairing.lean:227) with Turing.pairDecode_nil (TCSlib/Complexity/TuringMachine/Encoding.lean:153); or replace the whole proof by the published Complexity.length_pairSndD_le (ClassNP/PolyTimeBlockLoop.lean:187) | - |
| SEAL-0354 | `TCSlib.Cryptography.GI.pairSndD_encodeMsgs` | TCSlib.Cryptography.GI.pairSndD_encodeMsgs l.95: Tactic `rfl` failed: The left-hand side ( | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (ZeroKnowledge/Interaction.lean) and Complexity.pairSndD_of_pairDecode_eq_none with Turing.pairDecode_nil | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean** (3 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0358 | `TCSlib.Cryptography.GI.giVerifierRep_efficient` | TCSlib.Cryptography.GI.giVerifierRep_efficient l.321: 'show' tactic failed, pattern (#248  | use TCSlib.Cryptography.GI.giVerifierRep_next (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:369): rw [giVerifierRep_next] in place of the `show` at l.322 | - |
| SEAL-0356 | `TCSlib.Cryptography.GI.gi_verdict_iff` | TCSlib.Cryptography.GI.gi_verdict_iff l.305: Type mismatch (#248 inherited_same_native_ste | use TCSlib.Cryptography.GI.instanceG₀_def, GI.instanceG₁_def and GI.instanceVertexCount_def (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:124-141) before Iff.rfl | - |
| SEAL-0357 | `TCSlib.Cryptography.GI.gi_verdict_iff` | TCSlib.Cryptography.GI.gi_verdict_iff l.305: Type mismatch (#248 inherited_same_native_ste | use TCSlib.Cryptography.GI.instanceG₀_def, GI.instanceG₁_def and GI.instanceVertexCount_def (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:124-141) before Iff.rfl | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:183 | `TCSlib.Cryptography.GI.gi_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_efficientProverProofErr (lines 305, 330, 332, 308, 334; #248 OPE | use TCSlib.Cryptography.GI.giProtocol_P and TCSlib.Cryptography.GI.encInstance_eq (GraphIsomorphism/Proofs.lean:327, :115): rw [giProtocol_P, ← encInstance_eq] on the goals at l.316 and l.346 | - |
| SEAL-0361 | `TCSlib.Cryptography.GI.gi_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_efficientProverProofErr l.316: Application type mismatch: The ar | use TCSlib.Cryptography.GI.giProtocol_P and TCSlib.Cryptography.GI.encInstance_eq (GraphIsomorphism/Proofs.lean:327, :115): rw [giProtocol_P, ← encInstance_eq] on the goals at l.316 and l.346 | - |
| SEAL-0362 | `TCSlib.Cryptography.GI.gi_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_efficientProverProofErr l.316: Type mismatch (#248 inherited_rea | use TCSlib.Cryptography.GI.giProtocol_P and TCSlib.Cryptography.GI.encInstance_eq (GraphIsomorphism/Proofs.lean:327, :115): rw [giProtocol_P, ← encInstance_eq] on the goals at l.316 and l.346 | - |
| SEAL-0363 | `TCSlib.Cryptography.GI.gi_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_efficientProverProofErr l.346: Type mismatch (#248 inherited_rea | use TCSlib.Cryptography.GI.giProtocol_P and TCSlib.Cryptography.GI.encInstance_eq (GraphIsomorphism/Proofs.lean:327, :115): rw [giProtocol_P, ← encInstance_eq] on the goals at l.316 and l.346 | - |
| H:182 | `TCSlib.Cryptography.GI.gni_interactiveProofErr` | TCSlib.Cryptography.GI.gni_interactiveProofErr (lines 178, 181, 187; #248 OPEN_TYPED_COINS | use TCSlib.Cryptography.GI.gniProtocol_P and TCSlib.Cryptography.GI.encInstance_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:238, :115): rw [gniProtocol_P, ← encInstance_eq] on the completeness goal before the anonymous constructor at l.186 | - |
| SEAL-0359 | `TCSlib.Cryptography.GI.gni_interactiveProofErr` | TCSlib.Cryptography.GI.gni_interactiveProofErr l.186: Application type mismatch: The argum | use TCSlib.Cryptography.GI.gniProtocol_P and TCSlib.Cryptography.GI.encInstance_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:238, :115): rw [gniProtocol_P, ← encInstance_eq] on the completeness goal before the anonymous constructor at l.186 | - |
| SEAL-0360 | `TCSlib.Cryptography.GI.gni_interactiveProofErr` | TCSlib.Cryptography.GI.gni_interactiveProofErr l.186: Type mismatch (#248 inherited_reache | use TCSlib.Cryptography.GI.gniProtocol_P and TCSlib.Cryptography.GI.encInstance_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:238, :115): rw [gniProtocol_P, ← encInstance_eq] on the completeness goal before the anonymous constructor at l.186 | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean** (13 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:187 | `TCSlib.Cryptography.GI.gniProtocolRep_outV` | TCSlib.Cryptography.GI.gniProtocolRep_outV (lines 181; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Protocol.outV_eq and Protocol.transcriptWith_eq (ZeroKnowledge/Interaction.lean) with GI.gniProtocolRep_V (GraphIsomorphism/Proofs.lean); add GI.gniProtocolRep_P (= gniProver), GI.gniProtocolRep_rounds (= .mul (.const 2) .var) and GI.gniProtocolRep_verifierFirst (= true) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | - |
| SEAL-0365 | `TCSlib.Cryptography.GI.gniProtocolRep_outV` | TCSlib.Cryptography.GI.gniProtocolRep_outV l.167: Type mismatch (#248 inherited_same_nativ | use TCSlib.Cryptography.Protocol.outV_eq and Protocol.transcriptWith_eq (ZeroKnowledge/Interaction.lean) with GI.gniProtocolRep_V (GraphIsomorphism/Proofs.lean); add GI.gniProtocolRep_P (= gniProver), GI.gniProtocolRep_rounds (= .mul (.const 2) .var) and GI.gniProtocolRep_verifierFirst (= true) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | - |
| H:184 | `TCSlib.Cryptography.GI.gniProver_next_enc` | TCSlib.Cryptography.GI.gniProver_next_enc (lines 130; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.gniProver_next and GI.instanceG₀_def (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:214, :133): rw [gniProver_next, instanceG₀_def] in place of the `show` at l.120 | - |
| SEAL-0364 | `TCSlib.Cryptography.GI.gniProver_next_enc` | TCSlib.Cryptography.GI.gniProver_next_enc l.130: 'show' tactic failed, pattern (#248 inher | use TCSlib.Cryptography.GI.gniProver_next and GI.instanceG₀_def (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:214, :133): rw [gniProver_next, instanceG₀_def] in place of the `show` at l.120 | - |
| H:189 | `TCSlib.Cryptography.GI.gniRep_accept_le` | TCSlib.Cryptography.GI.gniRep_accept_le (lines 386; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.GI.prefixLE_apply (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete.lean:88) before the rfl at l.367 | - |
| SEAL-0368 | `TCSlib.Cryptography.GI.gniRep_accept_le` | TCSlib.Cryptography.GI.gniRep_accept_le l.377: Tactic `rfl` failed: The left-hand side (#2 | use TCSlib.Cryptography.GI.prefixLE_apply (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete.lean:88) before the rfl at l.367 | - |
| H:190 | `TCSlib.Cryptography.GI.gni_interactiveProofErrRep` | TCSlib.Cryptography.GI.gni_interactiveProofErrRep (lines 420, 423, 429; #248 OPEN_INCOMPLE | use TCSlib.Cryptography.GI.gniProtocolRep_V (l.401), GI.mem_Lniso_iff (l.404 rintro) and GI.isomorphic_iff (l.410 obtain), all in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | - |
| SEAL-0369 | `TCSlib.Cryptography.GI.gni_interactiveProofErrRep` | TCSlib.Cryptography.GI.gni_interactiveProofErrRep l.411: Type mismatch (#248 inherited_sam | use TCSlib.Cryptography.GI.gniProtocolRep_V (l.401), GI.mem_Lniso_iff (l.404 rintro) and GI.isomorphic_iff (l.410 obtain), all in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | - |
| SEAL-0370 | `TCSlib.Cryptography.GI.gni_interactiveProofErrRep` | TCSlib.Cryptography.GI.gni_interactiveProofErrRep l.414: Tactic `rcases` failed: `a✝ : Lni | use TCSlib.Cryptography.GI.gniProtocolRep_V (l.401), GI.mem_Lniso_iff (l.404 rintro) and GI.isomorphic_iff (l.410 obtain), all in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | - |
| SEAL-0371 | `TCSlib.Cryptography.GI.gni_interactiveProofErrRep` | TCSlib.Cryptography.GI.gni_interactiveProofErrRep l.420: Tactic `rcases` failed: `x✝ : Iso | use TCSlib.Cryptography.GI.gniProtocolRep_V (l.401), GI.mem_Lniso_iff (l.404 rintro) and GI.isomorphic_iff (l.410 obtain), all in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean | - |
| H:188 | `TCSlib.Cryptography.GI.statClose_pi` | TCSlib.Cryptography.GI.statClose_pi (lines 302, 323; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0366 | `TCSlib.Cryptography.GI.statClose_pi` | TCSlib.Cryptography.GI.statClose_pi l.293: Tactic `introN` failed: There are no additional | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0367 | `TCSlib.Cryptography.GI.statClose_pi` | TCSlib.Cryptography.GI.statClose_pi l.314: Tactic `introN` failed: There are no additional | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean** (9 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:202 | `TCSlib.Cryptography.GI.giRep_accept_le` | TCSlib.Cryptography.GI.giRep_accept_le (lines 433; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.GI.giProtocolRep_V_coinLen (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:795) with List.ofFn_congr to rewrite List.ofFn ((giRepCoins P' x) (b, r1)).2 to List.ofFn b (a local helper next to giRepCoins), then rw [getD_ofFn_lt' ..] instead of the `show` at l.425 | - |
| SEAL-0374 | `TCSlib.Cryptography.GI.giRep_accept_le` | TCSlib.Cryptography.GI.giRep_accept_le l.425: 'show' tactic failed, pattern (#248 inherite | use TCSlib.Cryptography.GI.giProtocolRep_V_coinLen (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:795) with List.ofFn_congr to rewrite List.ofFn ((giRepCoins P' x) (b, r1)).2 to List.ofFn b (a local helper next to giRepCoins), then rw [getD_ofFn_lt' ..] instead of the `show` at l.425 | - |
| H:198 | `TCSlib.Cryptography.GI.giVerifierRep_next_end_enc` | TCSlib.Cryptography.GI.giVerifierRep_next_end_enc (lines 197; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.GI.encInstance_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:115): rw [encInstance_eq, pairSndD_pairEncode] for the two `show .. from pairSndD_pairEncode/pairFstD_pairEncode` at l.198-199 | - |
| SEAL-0372 | `TCSlib.Cryptography.GI.giVerifierRep_next_end_enc` | TCSlib.Cryptography.GI.giVerifierRep_next_end_enc l.198: Type mismatch (#248 inherited_rea | use TCSlib.Cryptography.GI.encInstance_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:115): rw [encInstance_eq, pairSndD_pairEncode] for the two `show .. from pairSndD_pairEncode/pairFstD_pairEncode` at l.198-199 | - |
| SEAL-0373 | `TCSlib.Cryptography.GI.giVerifierRep_next_end_enc` | TCSlib.Cryptography.GI.giVerifierRep_next_end_enc l.195: unsolved goals (#248 inherited_re | use TCSlib.Cryptography.GI.encInstance_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs.lean:115): rw [encInstance_eq, pairSndD_pairEncode] for the two `show .. from pairSndD_pairEncode/pairFstD_pairEncode` at l.198-199 | - |
| H:203 | `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr (lines 448, 477, 479, 451, 481; #248 | use TCSlib.Cryptography.GI.giProtocolRep_P and TCSlib.Cryptography.GI.encInstance_eq (GraphIsomorphism/Proofs.lean:386, :115): rw [giProtocolRep_P, ← encInstance_eq] on the goals at l.445 and l.480 | - |
| SEAL-0375 | `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr l.445: Application type mismatch: Th | use TCSlib.Cryptography.GI.giProtocolRep_P and TCSlib.Cryptography.GI.encInstance_eq (GraphIsomorphism/Proofs.lean:386, :115): rw [giProtocolRep_P, ← encInstance_eq] on the goals at l.445 and l.480 | - |
| SEAL-0376 | `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr l.445: Type mismatch (#248 inherited | use TCSlib.Cryptography.GI.giProtocolRep_P and TCSlib.Cryptography.GI.encInstance_eq (GraphIsomorphism/Proofs.lean:386, :115): rw [giProtocolRep_P, ← encInstance_eq] on the goals at l.445 and l.480 | - |
| SEAL-0377 | `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr` | TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr l.480: Type mismatch (#248 inherited | use TCSlib.Cryptography.GI.giProtocolRep_P and TCSlib.Cryptography.GI.encInstance_eq (GraphIsomorphism/Proofs.lean:386, :115): rw [giProtocolRep_P, ← encInstance_eq] on the goals at l.445 and l.480 | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean** (6 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0381 | `TCSlib.Cryptography.exists_giSimulator` | TCSlib.Cryptography.exists_giSimulator l.533: Type mismatch (#248 inherited_same_native_st | use TCSlib.Cryptography.GIZK.sim_eq, GIZK.attemptStr_def and GIZK.blockLen_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean) to prove giSim = GIZK.sim; add TCSlib.Cryptography.GIZK.simCoins_def (simCoins V' = .mul .var (.add (.add (.const 1) (.normal 1 2)) V'.coins)) in GraphIsomorphismZK/Simulator.lean (only simCoins_eval is published); then transport GIZK.exists_simulator | - |
| SEAL-0383 | `TCSlib.Cryptography.gi_hvzk` | TCSlib.Cryptography.gi_hvzk l.594: Application type mismatch: The argument (#248 inherited | use TCSlib.Cryptography.giProtocol_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean:543) to turn giVerifier_efficient into giProtocol.V.Efficient at l.594 | - |
| SEAL-0382 | `TCSlib.Cryptography.gi_statZK` | TCSlib.Cryptography.gi_statZK l.566: Tactic `introN` failed: There are no additional binde | use TCSlib.Cryptography.StatZK_iff (TCSlib/Cryptography/ZeroKnowledge/Defs.lean) before `intro V' hV'` at l.566 | - |
| SEAL-0378 | `TCSlib.Cryptography.statClose_giHonestView` | TCSlib.Cryptography.statClose_giHonestView l.143: Type mismatch (#248 inherited_same_nativ | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean): := (statClose_iff _ _ _).2 fun T => by .. | - |
| SEAL-0379 | `TCSlib.Cryptography.statClose_giHonestView` | TCSlib.Cryptography.statClose_giHonestView l.144: Tactic `rewrite` failed: Did not find an | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean): := (statClose_iff _ _ _).2 fun T => by .. | - |
| SEAL-0380 | `TCSlib.Cryptography.statClose_giSimTrunc` | TCSlib.Cryptography.statClose_giSimTrunc l.472: Type mismatch (#248 inherited_same_native_ | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean** (18 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:207 | `TCSlib.Cryptography.GIZK.attemptStr_ofFn` | TCSlib.Cryptography.GIZK.attemptStr_ofFn (lines 351, 348; #248 OPEN_TYPED_COINS) | add TCSlib.Cryptography.encInstance_eq (encInstance G0 G1 = pairEncode (encGraph G0) (encGraph G1)) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| SEAL-0387 | `TCSlib.Cryptography.GIZK.attemptStr_ofFn` | TCSlib.Cryptography.GIZK.attemptStr_ofFn l.340: Type mismatch (#248 inherited_same_step_af | add TCSlib.Cryptography.encInstance_eq (encInstance G0 G1 = pairEncode (encGraph G0) (encGraph G1)) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| SEAL-0388 | `TCSlib.Cryptography.GIZK.attemptStr_ofFn` | TCSlib.Cryptography.GIZK.attemptStr_ofFn l.336: unsolved goals (#248 inherited_same_step_a | add TCSlib.Cryptography.encInstance_eq (encInstance G0 G1 = pairEncode (encGraph G0) (encGraph G1)) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| H:209 | `TCSlib.Cryptography.GIZK.giProver_next_cons` | TCSlib.Cryptography.GIZK.giProver_next_cons (lines 407; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.giProver_next (as for GIZK.giProver_next_nil) and encInstance_eq in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| SEAL-0390 | `TCSlib.Cryptography.GIZK.giProver_next_cons` | TCSlib.Cryptography.GIZK.giProver_next_cons l.396: 'show' tactic failed, pattern (#248 inh | add TCSlib.Cryptography.giProver_next (as for GIZK.giProver_next_nil) and encInstance_eq in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| H:208 | `TCSlib.Cryptography.GIZK.giProver_next_nil` | TCSlib.Cryptography.GIZK.giProver_next_nil (lines 398; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.giProver_next (giProver.next x y r hist = <its let/match body>, or the two cases next_nil/next_cons) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean, plus encInstance_eq there (see attemptStr_ofFn); decGraph_eq (Encoding.lean) is published | - |
| SEAL-0389 | `TCSlib.Cryptography.GIZK.giProver_next_nil` | TCSlib.Cryptography.GIZK.giProver_next_nil l.387: 'show' tactic failed, pattern (#248 inhe | add TCSlib.Cryptography.giProver_next (giProver.next x y r hist = <its let/match body>, or the two cases next_nil/next_cons) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean, plus encInstance_eq there (see attemptStr_ofFn); decGraph_eq (Encoding.lean) is published | - |
| H:211 | `TCSlib.Cryptography.GIZK.negligible_delta` | TCSlib.Cryptography.GIZK.negligible_delta (lines 562, 568; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.instanceVertices_def (instanceVertices N = Nat.sqrt ((N - 2) / 3)) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| SEAL-0392 | `TCSlib.Cryptography.GIZK.negligible_delta` | TCSlib.Cryptography.GIZK.negligible_delta l.551: Type mismatch (#248 inherited_same_step_a | add TCSlib.Cryptography.instanceVertices_def (instanceVertices N = Nat.sqrt ((N - 2) / 3)) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| SEAL-0393 | `TCSlib.Cryptography.GIZK.negligible_delta` | TCSlib.Cryptography.GIZK.negligible_delta l.557: Type mismatch (#248 inherited_same_step_a | add TCSlib.Cryptography.instanceVertices_def (instanceVertices N = Nat.sqrt ((N - 2) / 3)) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| H:204 | `TCSlib.Cryptography.GIZK.samplePerm_ofFn_castLE` | TCSlib.Cryptography.GIZK.samplePerm_ofFn_castLE (lines 155; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.permCoinLen_eq (permCoinLen n = n * permTrials n * permBits n) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| SEAL-0384 | `TCSlib.Cryptography.GIZK.samplePerm_ofFn_castLE` | TCSlib.Cryptography.GIZK.samplePerm_ofFn_castLE l.143: Application type mismatch: The argu | add TCSlib.Cryptography.permCoinLen_eq (permCoinLen n = n * permTrials n * permBits n) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| H:206 | `TCSlib.Cryptography.GIZK.statClose_pi` | TCSlib.Cryptography.GIZK.statClose_pi (lines 183; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0386 | `TCSlib.Cryptography.GIZK.statClose_pi` | TCSlib.Cryptography.GIZK.statClose_pi l.171: Tactic `introN` failed: There are no addition | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| H:205 | `TCSlib.Cryptography.GIZK.statClose_samplePerm_long` | TCSlib.Cryptography.GIZK.statClose_samplePerm_long (lines 164; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0385 | `TCSlib.Cryptography.GIZK.statClose_samplePerm_long` | TCSlib.Cryptography.GIZK.statClose_samplePerm_long l.152: Tactic `introN` failed: There ar | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| H:210 | `TCSlib.Cryptography.GIZK.statClose_typed_string` | TCSlib.Cryptography.GIZK.statClose_typed_string (lines 511; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) before `intro T` at l.500 | - |
| SEAL-0391 | `TCSlib.Cryptography.GIZK.statClose_typed_string` | TCSlib.Cryptography.GIZK.statClose_typed_string l.500: Tactic `introN` failed: There are n | use TCSlib.Cryptography.statClose_iff (TCSlib/Cryptography/Asymptotic/Sampling.lean) before `intro T` at l.500 | - |

**TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean** (8 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:212 | `TCSlib.Cryptography.GIZK.decGraphAt_padSq` | TCSlib.Cryptography.GIZK.decGraphAt_padSq (lines 167; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.decGraphAt_apply (decGraphAt n w u v = w.getD (finProdFinEquiv (u, v)) false) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| SEAL-0394 | `TCSlib.Cryptography.GIZK.decGraphAt_padSq` | TCSlib.Cryptography.GIZK.decGraphAt_padSq l.181: Type mismatch (#248 inherited_same_native | add TCSlib.Cryptography.decGraphAt_apply (decGraphAt n w u v = w.getD (finProdFinEquiv (u, v)) false) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| H:213 | `TCSlib.Cryptography.GIZK.decGraph_eq_of_sqrt` | TCSlib.Cryptography.GIZK.decGraph_eq_of_sqrt (lines 186; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.decGraph_eq (ZeroKnowledge/Encoding.lean:142) and add TCSlib.Cryptography.decGraphAt_apply (as for decGraphAt_padSq) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| SEAL-0395 | `TCSlib.Cryptography.GIZK.decGraph_eq_of_sqrt` | TCSlib.Cryptography.GIZK.decGraph_eq_of_sqrt l.200: Tactic `rfl` failed: The left-hand sid | use TCSlib.Cryptography.decGraph_eq (ZeroKnowledge/Encoding.lean:142) and add TCSlib.Cryptography.decGraphAt_apply (as for decGraphAt_padSq) in TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean | - |
| H:216 | `TCSlib.Cryptography.GIZK.exists_simulator` | TCSlib.Cryptography.GIZK.exists_simulator (lines 459; #248 OPEN_TYPED_COINS) | use Complexity.NUPPT.coins_ofPolyTimeUniform (TCSlib/Complexity/Randomized/PPT.lean:412) for the `rfl` at l.493 | - |
| SEAL-0397 | `TCSlib.Cryptography.GIZK.exists_simulator` | TCSlib.Cryptography.GIZK.exists_simulator l.493: Application type mismatch: The argument ( | use Complexity.NUPPT.coins_ofPolyTimeUniform (TCSlib/Complexity/Randomized/PPT.lean:412) for the `rfl` at l.493 | - |
| H:215 | `TCSlib.Cryptography.GIZK.sim_poly` | TCSlib.Cryptography.GIZK.sim_poly (lines 440; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.instanceVertexCount_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean:231) | - |
| SEAL-0396 | `TCSlib.Cryptography.GIZK.sim_poly` | TCSlib.Cryptography.GIZK.sim_poly l.474: Type mismatch (#248 inherited_same_native_step) | use TCSlib.Cryptography.instanceVertexCount_eq (TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean:231) | - |

**TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean** (10 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:324 | `TCSlib.Cryptography.exists_witnessRelation_of_mem_NP` | 333 simp Turing.MultiTapeTM.indicator | use Turing.MultiTapeTM.indicator_def (TCSlib/Complexity/TuringMachine/Deterministic.lean) | - |
| NEW:218 | `TCSlib.Cryptography.npProtocol_efficientP` | first error l.466: Invalid X notation: The expected type X is not an inductive type | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:183) for the anonymous constructor at l.466 and Complexity.NUPPT.coins_ofPolyTimeUniform (Complexity/Randomized/PPT.lean:412) for its `rfl` coins component | - |
| NEW:325 | `TCSlib.Cryptography.npProtocol_efficientP` | 468 simp Complexity.NUPPT.advInput | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| NEW:219 | `TCSlib.Cryptography.npProtocol_efficientV` | first error l.453: Invalid X notation: The expected type X is not an inductive type | use TCSlib.Cryptography.Strategy.efficient_iff (Interaction.lean:183) for the anonymous constructor at l.453 and Complexity.NUPPT.coins_ofPolyTimeUniform (PPT.lean:412) for the coins rfl | - |
| NEW:326 | `TCSlib.Cryptography.npProtocol_efficientV` | 455 simp Complexity.NUPPT.advInput | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| NEW:327 | `TCSlib.Cryptography.npProtocol_outV` | 413 simp TCSlib.Cryptography.Protocol.outV | use TCSlib.Cryptography.Protocol.outV_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| NEW:328 | `TCSlib.Cryptography.npProtocol_outV` | 413 simp TCSlib.Cryptography.Protocol.transcriptWith | use TCSlib.Cryptography.Protocol.transcriptWith_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| NEW:329 | `TCSlib.Cryptography.npProtocol_outV` | 413 simp TCSlib.Cryptography.exec | use TCSlib.Cryptography.exec_succ (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| NEW:330 | `TCSlib.Cryptography.npProtocol_outV` | 413 simp TCSlib.Cryptography.moverIsV | use TCSlib.Cryptography.moverIsV_def (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| NEW:220 | `TCSlib.Cryptography.npProtocol_readsPrefix` | first error l.419: Tactic X failed: There are no additional binders or X bindings in the g | add TCSlib.Cryptography.Strategy.readsPrefix_iff (S.ReadsPrefix m ↔ ∀ x z r hist, S.next x z r hist = S.next x z r (hist.map (List.take (m.eval x.length)))) in TCSlib/Cryptography/ZeroKnowledge/Interaction.lean | - |

**TCSlib/Cryptography/ZeroKnowledge/NP.lean** (7 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:221 | `TCSlib.Cryptography.LevinReduction.efficientProverProofErr` | TCSlib.Cryptography.LevinReduction.efficientProverProofErr (lines 436; #248 OPEN_TYPED_COI | use TCSlib.Cryptography.Strategy.coinLen_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:126): (Strategy.coinLen_eq _ _).le in place of le_rfl at l.421 (as outV_pullback_cheat does at l.348) | - |
| SEAL-0401 | `TCSlib.Cryptography.LevinReduction.efficientProverProofErr` | TCSlib.Cryptography.LevinReduction.efficientProverProofErr l.437: Application type mismatc | use TCSlib.Cryptography.Strategy.coinLen_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:126): (Strategy.coinLen_eq _ _).le in place of le_rfl at l.421 (as outV_pullback_cheat does at l.348) | - |
| H:222 | `TCSlib.Cryptography.LevinReduction.zk` | TCSlib.Cryptography.LevinReduction.zk (lines 499; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.ZK_iff (TCSlib/Cryptography/ZeroKnowledge/Defs.lean:168) before `intro V' hV'` at l.484 | - |
| SEAL-0402 | `TCSlib.Cryptography.LevinReduction.zk` | TCSlib.Cryptography.LevinReduction.zk l.500: Tactic `introN` failed: There are no addition | use TCSlib.Cryptography.ZK_iff (TCSlib/Cryptography/ZeroKnowledge/Defs.lean:168) before `intro V' hV'` at l.484 | - |
| H:219 | `TCSlib.Cryptography.Strategy.pullback_efficient` | TCSlib.Cryptography.Strategy.pullback_efficient (lines 253; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0398 | `TCSlib.Cryptography.Strategy.pullback_efficient` | TCSlib.Cryptography.Strategy.pullback_efficient l.261: Invalid `⟨...⟩` notation: The expec | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0399 | `TCSlib.Cryptography.Strategy.pullback_efficient` | TCSlib.Cryptography.Strategy.pullback_efficient l.262: No goals to be solved (#248 inherit | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/NPLemmas.lean** (15 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| C1-0312 | `TCSlib.Cryptography.LevinTransfer.acceptProb_comp_unifProj` | 170 unfold TCSlib.Cryptography.acceptProb | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| C1-0313 | `TCSlib.Cryptography.LevinTransfer.acceptProb_eq_of_unifProj` | 181 unfold TCSlib.Cryptography.acceptProb | use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| C1-0314 | `TCSlib.Cryptography.LevinTransfer.distAdv_eq_of_unifProj` | 195 unfold TCSlib.Cryptography.distAdv | use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean) | - |
| C1-0321 | `TCSlib.Cryptography.LevinTransfer.distinguisherL_lift` | 405 simp Complexity.NUPPT.distinguisherL | use Complexity.NUPPT.distinguisherL_eq (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| SEAL-0403 | `TCSlib.Cryptography.LevinTransfer.exec_congr` | TCSlib.Cryptography.LevinTransfer.exec_congr l.93: Tactic `rfl` failed: The left-hand side | use TCSlib.Cryptography.exec_zero (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:262) in the zero case (l.93) | - |
| SEAL-0406 | `TCSlib.Cryptography.LevinTransfer.exists_liftSimulator` | TCSlib.Cryptography.LevinTransfer.exists_liftSimulator l.378: Application type mismatch: T | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0407 | `TCSlib.Cryptography.LevinTransfer.exists_liftSimulator` | TCSlib.Cryptography.LevinTransfer.exists_liftSimulator l.378: Tactic `rewrite` failed: Did | use Complexity.NUPPT.uniform_iff (TCSlib/Complexity/Randomized/PPT.lean) | - |
| SEAL-0404 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_coinLen` | TCSlib.Cryptography.LevinTransfer.liftVerifier_coinLen l.281: Type mismatch (#248 inherite | use TCSlib.Cryptography.Strategy.coinLen_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:126): rw [Strategy.coinLen_eq, Strategy.coinLen_eq]; rfl (liftVerifier is local) | - |
| SEAL-0405 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient l.297: Tactic `rcases` failed: `h | use TCSlib.Cryptography.Strategy.efficient_iff (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| C1-0315 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 323 simp Complexity.NUPPT.inArg | use Complexity.NUPPT.inArg_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| C1-0316 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 323 simp Complexity.NUPPT.inCoins | use Complexity.NUPPT.inCoins_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| C1-0317 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 323 simp Complexity.NUPPT.advInput | use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean) | - |
| C1-0318 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 323 simp Complexity.NUPPT.layout | use Complexity.NUPPT.layout_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| C1-0319 | `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient` | 324 simp TCSlib.Cryptography.Strategy.coinLen | use TCSlib.Cryptography.Strategy.coinLen_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| C1-0320 | `TCSlib.Cryptography.LevinTransfer.postView_encode` | 341 simp TCSlib.Cryptography.View.encode | use TCSlib.Cryptography.View.encode_mk (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:302) | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean** (16 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:248 | `TCSlib.Cryptography.colProtocol_outV` | TCSlib.Cryptography.colProtocol_outV (lines 746; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Protocol.outV_eq, Protocol.transcriptWith_eq, exec_succ/exec_zero and moverIsV_false (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean), with the local colProtocol_V/_rounds/_verifierFirst | - |
| SEAL-0413 | `TCSlib.Cryptography.colProtocol_outV` | TCSlib.Cryptography.colProtocol_outV l.750: Type mismatch (#248 inherited_same_native_step | use TCSlib.Cryptography.Protocol.outV_eq, Protocol.transcriptWith_eq, exec_succ/exec_zero and moverIsV_false (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean), with the local colProtocol_V/_rounds/_verifierFirst | - |
| H:250 | `TCSlib.Cryptography.colProtocol_sound` | TCSlib.Cryptography.colProtocol_sound (lines 853; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.Strategy.coinLen_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:126) (with the local colVerifier coins .normal 1 2) in place of the `show` at l.857 | - |
| SEAL-0415 | `TCSlib.Cryptography.colProtocol_sound` | TCSlib.Cryptography.colProtocol_sound l.857: 'show' tactic failed, pattern (#248 inherited | use TCSlib.Cryptography.Strategy.coinLen_eq (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:126) (with the local colVerifier coins .normal 1 2) in place of the `show` at l.857 | - |
| H:245 | `TCSlib.Cryptography.colProverRep_efficient` | TCSlib.Cryptography.colProverRep_efficient (lines 589; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColProofs.colProverRep_coins and a body-form ColProofs.colProverRep_next in ThreeColoring/ProtocolProofs.lean; prove colProverRep Com ℓ = ColProofs.colProverRep Com ℓ and transport | - |
| SEAL-0410 | `TCSlib.Cryptography.colProverRep_efficient` | TCSlib.Cryptography.colProverRep_efficient l.593: Type mismatch (#248 inherited_same_nativ | add TCSlib.Cryptography.ColProofs.colProverRep_coins and a body-form ColProofs.colProverRep_next in ThreeColoring/ProtocolProofs.lean; prove colProverRep Com ℓ = ColProofs.colProverRep Com ℓ and transport | - |
| H:243 | `TCSlib.Cryptography.colProver_efficient` | TCSlib.Cryptography.colProver_efficient (lines 567; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColProofs.colProver_coins and a body-form next reader TCSlib.Cryptography.ColProofs.colProver_next (the verbatim let/match body of the shadow) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean; prove colProver Com ℓ = ColProofs.colProver Com ℓ in Protocol.lean and transport ColProofs.colProver_efficient | - |
| SEAL-0408 | `TCSlib.Cryptography.colProver_efficient` | TCSlib.Cryptography.colProver_efficient l.571: Type mismatch (#248 inherited_same_native_s | add TCSlib.Cryptography.ColProofs.colProver_coins and a body-form next reader TCSlib.Cryptography.ColProofs.colProver_next (the verbatim let/match body of the shadow) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean; prove colProver Com ℓ = ColProofs.colProver Com ℓ in Protocol.lean and transport ColProofs.colProver_efficient | - |
| H:247 | `TCSlib.Cryptography.colProver_length_le` | TCSlib.Cryptography.colProver_length_le (lines 629; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.decGraph_fst (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:146): (decGraph x).1 = Nat.sqrt x.length | - |
| SEAL-0412 | `TCSlib.Cryptography.colProver_length_le` | TCSlib.Cryptography.colProver_length_le l.633: Type mismatch (#248 inherited_same_step_aft | use TCSlib.Cryptography.decGraph_fst (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:146): (decGraph x).1 = Nat.sqrt x.length | - |
| H:246 | `TCSlib.Cryptography.colVerifierRep_efficient` | TCSlib.Cryptography.colVerifierRep_efficient (lines 597; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColProofs.colVerifierRep_coins and a body-form ColProofs.colVerifierRep_next in ThreeColoring/ProtocolProofs.lean; prove colVerifierRep Com ℓ = ColProofs.colVerifierRep Com ℓ and transport | - |
| SEAL-0411 | `TCSlib.Cryptography.colVerifierRep_efficient` | TCSlib.Cryptography.colVerifierRep_efficient l.601: Type mismatch (#248 inherited_same_nat | add TCSlib.Cryptography.ColProofs.colVerifierRep_coins and a body-form ColProofs.colVerifierRep_next in ThreeColoring/ProtocolProofs.lean; prove colVerifierRep Com ℓ = ColProofs.colVerifierRep Com ℓ and transport | - |
| H:244 | `TCSlib.Cryptography.colVerifier_efficient` | TCSlib.Cryptography.colVerifier_efficient (lines 582; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColProofs.colVerifier_coins and a body-form ColProofs.colVerifier_next in ThreeColoring/ProtocolProofs.lean; prove colVerifier Com ℓ = ColProofs.colVerifier Com ℓ and transport ColProofs.colVerifier_efficient | - |
| SEAL-0409 | `TCSlib.Cryptography.colVerifier_efficient` | TCSlib.Cryptography.colVerifier_efficient l.586: Type mismatch (#248 inherited_same_native | add TCSlib.Cryptography.ColProofs.colVerifier_coins and a body-form ColProofs.colVerifier_next in ThreeColoring/ProtocolProofs.lean; prove colVerifier Com ℓ = ColProofs.colVerifier Com ℓ and transport ColProofs.colVerifier_efficient | - |
| H:249 | `TCSlib.Cryptography.uprob_check_uniform_le` | TCSlib.Cryptography.uprob_check_uniform_le (lines 790; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColProofs.finOneEquiv_apply (finOneEquiv m e = (fun _ => e, ())) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean | - |
| SEAL-0414 | `TCSlib.Cryptography.uprob_check_uniform_le` | TCSlib.Cryptography.uprob_check_uniform_le l.794: Type mismatch (#248 inherited_same_nativ | add TCSlib.Cryptography.ColProofs.finOneEquiv_apply (finOneEquiv m e = (fun _ => e, ())) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean** (11 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:254 | `TCSlib.Cryptography.ColProofs.colProverRep_next_eq` | TCSlib.Cryptography.ColProofs.colProverRep_next_eq (lines 297; #248 OPEN_TYPED_COINS) | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:136) | - |
| SEAL-0421 | `TCSlib.Cryptography.ColProofs.colProverRep_next_eq` | TCSlib.Cryptography.ColProofs.colProverRep_next_eq l.298: Tactic `rfl` failed: The left-ha | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:136) | - |
| H:252 | `TCSlib.Cryptography.ColProofs.colProver_next_eq` | TCSlib.Cryptography.ColProofs.colProver_next_eq (lines 180; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| SEAL-0416 | `TCSlib.Cryptography.ColProofs.colProver_next_eq` | TCSlib.Cryptography.ColProofs.colProver_next_eq l.180: Tactic `rfl` failed: The left-hand  | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| H:255 | `TCSlib.Cryptography.ColProofs.colVerifierRep_next_eq` | TCSlib.Cryptography.ColProofs.colVerifierRep_next_eq (lines 329; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.edgeMsg_def (edgeMsg e = List.replicate e true) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean | - |
| SEAL-0422 | `TCSlib.Cryptography.ColProofs.colVerifierRep_next_eq` | TCSlib.Cryptography.ColProofs.colVerifierRep_next_eq l.330: Tactic `rfl` failed: The left- | add TCSlib.Cryptography.edgeMsg_def (edgeMsg e = List.replicate e true) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean | - |
| H:253 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq (lines 224, 231, 233, 243; #248 OPEN_INC | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (ZeroKnowledge/Interaction.lean:136) at l.224/231/243; add TCSlib.Cryptography.edgeMsg_def (edgeMsg e = List.replicate e true) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean for the rfl at l.233 | - |
| SEAL-0417 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq l.224: Tactic `rfl` failed: The left-han | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (ZeroKnowledge/Interaction.lean:136) at l.224/231/243; add TCSlib.Cryptography.edgeMsg_def (edgeMsg e = List.replicate e true) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean for the rfl at l.233 | - |
| SEAL-0418 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq l.231: Tactic `rfl` failed: The left-han | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (ZeroKnowledge/Interaction.lean:136) at l.224/231/243; add TCSlib.Cryptography.edgeMsg_def (edgeMsg e = List.replicate e true) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean for the rfl at l.233 | - |
| SEAL-0419 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq l.233: Tactic `rfl` failed: The left-han | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (ZeroKnowledge/Interaction.lean:136) at l.224/231/243; add TCSlib.Cryptography.edgeMsg_def (edgeMsg e = List.replicate e true) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean for the rfl at l.233 | - |
| SEAL-0420 | `TCSlib.Cryptography.ColProofs.colVerifier_next_eq` | TCSlib.Cryptography.ColProofs.colVerifier_next_eq l.243: Tactic `rfl` failed: The left-han | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (ZeroKnowledge/Interaction.lean:136) at l.224/231/243; add TCSlib.Cryptography.edgeMsg_def (edgeMsg e = List.replicate e true) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean for the rfl at l.233 | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean** (17 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| H:263 | `TCSlib.Cryptography.Negligible.comp_sqrt` | TCSlib.Cryptography.Negligible.comp_sqrt (lines 690; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| SEAL-0430 | `TCSlib.Cryptography.Negligible.comp_sqrt` | TCSlib.Cryptography.Negligible.comp_sqrt l.1189: Tactic `introN` failed: There are no addi | use TCSlib.Cryptography.negligible_iff (TCSlib/Cryptography/Foundations/Negligible.lean) | - |
| H:261 | `TCSlib.Cryptography.colSimAttemptPlanted_H` | TCSlib.Cryptography.colSimAttemptPlanted_H (lines 499; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.colCommit_eq (ThreeColoring/Protocol.lean:131) and TCSlib.Cryptography.multiCom_def (ZeroKnowledge/Commitment.lean) before the `show` at l.501 | - |
| SEAL-0427 | `TCSlib.Cryptography.colSimAttemptPlanted_H` | TCSlib.Cryptography.colSimAttemptPlanted_H l.501: 'show' tactic failed, pattern (#248 inhe | use TCSlib.Cryptography.colCommit_eq (ThreeColoring/Protocol.lean:131) and TCSlib.Cryptography.multiCom_def (ZeroKnowledge/Commitment.lean) before the `show` at l.501 | - |
| H:260 | `TCSlib.Cryptography.colSimAttemptPlanted_W` | TCSlib.Cryptography.colSimAttemptPlanted_W (lines 448; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.colCommit_eq (ThreeColoring/Protocol.lean:131) and TCSlib.Cryptography.multiCom_def (ZeroKnowledge/Commitment.lean) before the `show` at l.450 | - |
| SEAL-0426 | `TCSlib.Cryptography.colSimAttemptPlanted_W` | TCSlib.Cryptography.colSimAttemptPlanted_W l.450: 'show' tactic failed, pattern (#248 inhe | use TCSlib.Cryptography.colCommit_eq (ThreeColoring/Protocol.lean:131) and TCSlib.Cryptography.multiCom_def (ZeroKnowledge/Commitment.lean) before the `show` at l.450 | - |
| H:264 | `TCSlib.Cryptography.col_hvzk` | TCSlib.Cryptography.col_hvzk (lines 789; #248 OPEN_INCOMPLETE) | use TCSlib.Cryptography.colProtocol_V (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:480) to turn colVerifier_efficient into (colProtocol Com ℓ).V.Efficient at l.1646 | - |
| SEAL-0431 | `TCSlib.Cryptography.col_hvzk` | TCSlib.Cryptography.col_hvzk l.1646: Application type mismatch: The argument (#248 inherit | use TCSlib.Cryptography.colProtocol_V (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:480) to turn colVerifier_efficient into (colProtocol Com ℓ).V.Efficient at l.1646 | - |
| H:262 | `TCSlib.Cryptography.exists_colSimulator` | TCSlib.Cryptography.exists_colSimulator (lines 676, 676; #248 OPEN_TYPED_COINS) | add TCSlib.Cryptography.ColSimMachine.simCoins_def (simCoins ℓ V' = .mul (.mul .var .var) (blockPoly ℓ V')) and ColSimMachine.blockPoly_def in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean; use the published ColSimMachine.sim_def (SimulatorNumeric.lean:125) with the attemptStr readers to identify ColSimMachine.sim with colSim | - |
| SEAL-0428 | `TCSlib.Cryptography.exists_colSimulator` | TCSlib.Cryptography.exists_colSimulator l.718: Application type mismatch: The argument (#2 | add TCSlib.Cryptography.ColSimMachine.simCoins_def (simCoins ℓ V' = .mul (.mul .var .var) (blockPoly ℓ V')) and ColSimMachine.blockPoly_def in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean; use the published ColSimMachine.sim_def (SimulatorNumeric.lean:125) with the attemptStr readers to identify ColSimMachine.sim with colSim | - |
| SEAL-0429 | `TCSlib.Cryptography.exists_colSimulator` | TCSlib.Cryptography.exists_colSimulator l.718: Application type mismatch: The argument (#2 | add TCSlib.Cryptography.ColSimMachine.simCoins_def (simCoins ℓ V' = .mul (.mul .var .var) (blockPoly ℓ V')) and ColSimMachine.blockPoly_def in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean; use the published ColSimMachine.sim_def (SimulatorNumeric.lean:125) with the attemptStr readers to identify ColSimMachine.sim with colSim | - |
| H:259 | `TCSlib.Cryptography.statClose_colSimTruncH` | TCSlib.Cryptography.statClose_colSimTruncH (lines 356; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColSimLemmas.truncAttempts_def (truncAttempts att N w = (List.finRange N).findSome? fun t => att (w t)) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean; rewrite colSimTruncH (local firstSome) to truncAttempts before the exact at l.358 | - |
| SEAL-0425 | `TCSlib.Cryptography.statClose_colSimTruncH` | TCSlib.Cryptography.statClose_colSimTruncH l.358: Type mismatch (#248 inherited_same_nativ | add TCSlib.Cryptography.ColSimLemmas.truncAttempts_def (truncAttempts att N w = (List.finRange N).findSome? fun t => att (w t)) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean; rewrite colSimTruncH (local firstSome) to truncAttempts before the exact at l.358 | - |
| H:257 | `TCSlib.Cryptography.uprob_colSimAttemptH_none` | TCSlib.Cryptography.uprob_colSimAttemptH_none (lines 261; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColSimLemmas.attemptCoinsEquiv_symm_apply ((attemptCoinsEquiv m R ρ).symm z = (((z.2, z.1.1.1), z.1.1.2), z.1.2)) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean | - |
| SEAL-0423 | `TCSlib.Cryptography.uprob_colSimAttemptH_none` | TCSlib.Cryptography.uprob_colSimAttemptH_none l.263: 'show' tactic failed, pattern (#248 i | add TCSlib.Cryptography.ColSimLemmas.attemptCoinsEquiv_symm_apply ((attemptCoinsEquiv m R ρ).symm z = (((z.2, z.1.1.1), z.1.1.2), z.1.2)) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas.lean | - |
| H:258 | `TCSlib.Cryptography.uprob_colSimAttemptH_some` | TCSlib.Cryptography.uprob_colSimAttemptH_some (lines 300; #248 OPEN_INCOMPLETE) | add TCSlib.Cryptography.ColSimLemmas.attemptCoinsEquiv_symm_apply (as for uprob_colSimAttemptH_none) in ThreeColoring/SimulatorLemmas.lean; for the match on edgeAt in the right-hand side use the published edgeAt_eq_some_edgeOf (ThreeColoring/Language.lean) | - |
| SEAL-0424 | `TCSlib.Cryptography.uprob_colSimAttemptH_some` | TCSlib.Cryptography.uprob_colSimAttemptH_some l.302: 'show' tactic failed, pattern (#248 i | add TCSlib.Cryptography.ColSimLemmas.attemptCoinsEquiv_symm_apply (as for uprob_colSimAttemptH_none) in ThreeColoring/SimulatorLemmas.lean; for the match on edgeAt in the right-hand side use the published edgeAt_eq_some_edgeOf (ThreeColoring/Language.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine.lean** (14 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0436 | `TCSlib.Cryptography.ColSimMachine.baseR_poly` | TCSlib.Cryptography.ColSimMachine.baseR_poly l.273: Type mismatch (#248 inherited_same_nat | add TCSlib.Cryptography.ColSimMachine.baseR_def (baseR x = (x.length + 1) ^ 2 + 3 * x.length) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0433 | `TCSlib.Cryptography.ColSimMachine.blk_poly` | TCSlib.Cryptography.ColSimMachine.blk_poly l.258: Type mismatch (#248 inherited_same_nativ | use TCSlib.Cryptography.colCoinSlice_eq (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:498) | - |
| SEAL-0439 | `TCSlib.Cryptography.ColSimMachine.chunk_poly` | TCSlib.Cryptography.ColSimMachine.chunk_poly l.402: Type mismatch (#248 inherited_same_nat | add TCSlib.Cryptography.ColSimMachine.chunk_def (chunk Com ℓ x blk c i = pairEncode (Com (pairEncode (EnsembleLemmas.padL (nV x) (encColor (c i))) (rrStr ℓ x blk i))) []) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0441 | `TCSlib.Cryptography.ColSimMachine.comStr0_poly` | TCSlib.Cryptography.ColSimMachine.comStr0_poly l.428: Type mismatch (#248 inherited_same_n | add TCSlib.Cryptography.ColSimMachine.nV_def (nV x = Nat.sqrt x.length) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0440 | `TCSlib.Cryptography.ColSimMachine.comStr_poly` | TCSlib.Cryptography.ColSimMachine.comStr_poly l.417: Type mismatch (#248 inherited_same_na | add TCSlib.Cryptography.ColSimMachine.nV_def (nV x = Nat.sqrt x.length) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0445 | `TCSlib.Cryptography.ColSimMachine.exists_simulator` | TCSlib.Cryptography.ColSimMachine.exists_simulator l.632: Application type mismatch: The a | use Complexity.NUPPT.coins_ofPolyTimeUniform (TCSlib/Complexity/Randomized/PPT.lean:412) for the `rfl` at l.632 | - |
| SEAL-0438 | `TCSlib.Cryptography.ColSimMachine.kPos_poly` | TCSlib.Cryptography.ColSimMachine.kPos_poly l.320: Type mismatch (#248 inherited_same_nati | add TCSlib.Cryptography.ColSimMachine.kPos_def (kPos x blk = edgePos (nV x) x (eIdx x blk)) and ColSimMachine.edgePos_def (edgePos n x e = firstIdx (fun k => x.getD k false && decide (countBits x k = e)) (n * n)) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0432 | `TCSlib.Cryptography.ColSimMachine.length_simX_le` | TCSlib.Cryptography.ColSimMachine.length_simX_le l.235: Application type mismatch: The arg | use Complexity.NUPPT.inArg_eq (TCSlib/Complexity/Randomized/Closure.lean) | - |
| SEAL-0435 | `TCSlib.Cryptography.ColSimMachine.mE_poly` | TCSlib.Cryptography.ColSimMachine.mE_poly l.268: Type mismatch (#248 inherited_same_native | add TCSlib.Cryptography.ColSimMachine.mE_def (mE x = countBits x (nV x * nV x)) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0434 | `TCSlib.Cryptography.ColSimMachine.nV_poly` | TCSlib.Cryptography.ColSimMachine.nV_poly l.263: Type mismatch (#248 inherited_same_native | add TCSlib.Cryptography.ColSimMachine.nV_def (nV x = Nat.sqrt x.length) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0442 | `TCSlib.Cryptography.ColSimMachine.opnStr_poly` | TCSlib.Cryptography.ColSimMachine.opnStr_poly l.476: Type mismatch (#248 inherited_same_na | add TCSlib.Cryptography.ColSimMachine.opnStr_def (opnStr ℓ x blk = pairEncode (pairEncode (encColor (colorNum x blk (kPos x blk / nV x))) (rrStr ℓ x blk (kPos x blk / nV x))) (pairEncode (encColor (colorNum ..  % ..)) (rrStr .. % ..))) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0444 | `TCSlib.Cryptography.ColSimMachine.sim_eq` | TCSlib.Cryptography.ColSimMachine.sim_eq l.573: Type mismatch (#248 inherited_same_step_af | add TCSlib.Cryptography.ColSimMachine.mE_def and ColSimMachine.nV_def in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean; with the published decGraph_fst (ZeroKnowledge/Encoding.lean:146) | - |
| SEAL-0437 | `TCSlib.Cryptography.ColSimMachine.vIdx_poly` | TCSlib.Cryptography.ColSimMachine.vIdx_poly l.301: Type mismatch (#248 inherited_same_step | add TCSlib.Cryptography.ColSimMachine.vIdx_def (vIdx x blk = sampleNum 6 3 x.length (blk.drop ((x.length + 1) ^ 2))) in TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean | - |
| SEAL-0443 | `TCSlib.Cryptography.ColSimMachine.view_poly` | TCSlib.Cryptography.ColSimMachine.view_poly l.484: Type mismatch (#248 inherited_same_nati | use TCSlib.Cryptography.View.encode_mk and Strategy.encodeMsgs_cons / encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |

**TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean** (20 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0451 | `TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum` | TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum l.652: Type mismatch (#248 inhe | use TCSlib.Cryptography.decGraph_fst (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:146) at l.652-653 | - |
| SEAL-0452 | `TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum` | TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum l.653: Type mismatch (#248 inhe | use TCSlib.Cryptography.decGraph_fst (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:146) at l.652-653 | - |
| C1-0342 | `TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum` | 698 unfold TCSlib.Cryptography.colOpen | use TCSlib.Cryptography.colOpen_eq (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean) | - |
| C1-0325 | `TCSlib.Cryptography.ColSimMachine.bitsToNat_getD_eq_blockVal` | 138 simp TCSlib.Cryptography.bitsToNat | use TCSlib.Cryptography.bitsToNat_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| C1-0326 | `TCSlib.Cryptography.ColSimMachine.bitsToNat_getD_eq_blockVal` | 141 unfold TCSlib.Cryptography.bitsToNat | use TCSlib.Cryptography.bitsToNat_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |
| SEAL-0450 | `TCSlib.Cryptography.ColSimMachine.colCommit_eq_comStr` | TCSlib.Cryptography.ColSimMachine.colCommit_eq_comStr l.638: Tactic `rfl` failed: The left | use TCSlib.Cryptography.padColor_def (ThreeColoring/Language.lean:315) and TCSlib.Cryptography.EnsembleLemmas.ofFn_padFin_eq_padL (Asymptotic/EnsemblesLemmas.lean:198) before the rfl at l.638 | - |
| C1-0340 | `TCSlib.Cryptography.ColSimMachine.colCommit_eq_comStr` | 634 unfold TCSlib.Cryptography.colCommit | use TCSlib.Cryptography.colCommit_eq (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean) | - |
| C1-0341 | `TCSlib.Cryptography.ColSimMachine.colCommit_eq_comStr` | 634 unfold TCSlib.Cryptography.multiCom | use TCSlib.Cryptography.multiCom_def (TCSlib/Cryptography/ZeroKnowledge/Commitment.lean) | - |
| SEAL-0448 | `TCSlib.Cryptography.ColSimMachine.edgeList_eq_map` | TCSlib.Cryptography.ColSimMachine.edgeList_eq_map l.357: 'show' tactic failed, pattern (#2 | use TCSlib.Cryptography.decGraph_snd_apply (TCSlib/Cryptography/ZeroKnowledge/Encoding.lean:151) before the `show` at l.357 | - |
| C1-0333 | `TCSlib.Cryptography.ColSimMachine.edgeList_eq_map` | 352 unfold TCSlib.Cryptography.edgeList | use TCSlib.Cryptography.edgeList_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean) | - |
| C1-0334 | `TCSlib.Cryptography.ColSimMachine.edgeOf_val_eq` | 480 unfold TCSlib.Cryptography.edgeOf | use TCSlib.Cryptography.edgeOf_eq (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean) | - |
| SEAL-0449 | `TCSlib.Cryptography.ColSimMachine.encodeMsgs_eq_flatMap` | TCSlib.Cryptography.ColSimMachine.encodeMsgs_eq_flatMap l.506: Tactic `rfl` failed: The le | use TCSlib.Cryptography.Strategy.encodeMsgs_nil (TCSlib/Cryptography/ZeroKnowledge/Interaction.lean) | - |
| C1-0337 | `TCSlib.Cryptography.ColSimMachine.encodeMsgs_eq_flatMap` | 509 simp Turing.pairEncode | use Turing.pairEncode_eq (TCSlib/Complexity/TuringMachine/Encoding.lean) | - |
| C1-0327 | `TCSlib.Cryptography.ColSimMachine.findSome?_range_eq` | 161 simp TCSlib.Cryptography.EncodingMachines.firstIdx | use TCSlib.Cryptography.EncodingMachines.firstIdx_eq_of_forall (TCSlib/Cryptography/ZeroKnowledge/EncodingMachines.lean:263), vacuous at T = 0 | - |
| C1-0338 | `TCSlib.Cryptography.ColSimMachine.ofFn_getD_eq_padL` | 526 unfold TCSlib.Cryptography.EnsembleLemmas.padL | use TCSlib.Cryptography.EnsembleLemmas.ofFn_padFin_eq_padL (TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean:198): rw [← ofFn_padFin_eq_padL] | - |
| C1-0339 | `TCSlib.Cryptography.ColSimMachine.ofFn_getD_eq_padL` | 529 simp TCSlib.Cryptography.padFin | use TCSlib.Cryptography.padFin_def (TCSlib/Cryptography/Asymptotic/Adversary.lean) | - |
| C1-0330 | `TCSlib.Cryptography.ColSimMachine.sampleEdgeIdx_eq` | 234 unfold TCSlib.Cryptography.sampleEdgeIdx | use TCSlib.Cryptography.sampleEdgeIdx_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean) | - |
| SEAL-0446 | `TCSlib.Cryptography.ColSimMachine.sampleIdx_eq` | TCSlib.Cryptography.ColSimMachine.sampleIdx_eq l.213: 'show' tactic failed, pattern (#248  | use TCSlib.Cryptography.sampleIdx_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:347) for the show at l.213; add TCSlib.Cryptography.EncodingMachines.trialIdx_def (trialIdx n k T r i = firstIdx (fun t => decide (blockVal r ((i * T + t) * k) k < n - i)) T) in TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations.lean for the show at l.224 | - |
| SEAL-0447 | `TCSlib.Cryptography.ColSimMachine.sampleIdx_eq` | TCSlib.Cryptography.ColSimMachine.sampleIdx_eq l.224: 'show' tactic failed, pattern (#248  | use TCSlib.Cryptography.sampleIdx_def (TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean:347) for the show at l.213; add TCSlib.Cryptography.EncodingMachines.trialIdx_def (trialIdx n k T r i = firstIdx (fun t => decide (blockVal r ((i * T + t) * k) k < n - i)) T) in TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations.lean for the show at l.224 | - |
| C1-0329 | `TCSlib.Cryptography.ColSimMachine.sampleIdx_eq` | 218 simp TCSlib.Cryptography.uniformFromBits | use TCSlib.Cryptography.uniformFromBits_def (TCSlib/Cryptography/Asymptotic/Sampling.lean) | - |

**TCSlib/InformationTheory/Entropy.lean** (3 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| NEW:226 | `TCSlib.InformationTheory.FinDist.IsFlatSource.isSource` | first error l.181: Application type mismatch: The argument | use TCSlib.InformationTheory.FinDist.hasMinEntropy_iff | - |
| NEW:228 | `TCSlib.InformationTheory.FinDist.isSource_uniform` | first error l.209: Application type mismatch: The argument; providers TCSlib.InformationTh | use TCSlib.InformationTheory.FinDist.hasMinEntropy_iff | - |
| NEW:230 | `TCSlib.InformationTheory.FinDist.le_minEntropy_iff` | first error l.139: Tactic X failed: The left-hand side | use TCSlib.InformationTheory.FinDist.hasMinEntropy_iff | - |

**TCSlib/InformationTheory/LeftoverHash.lean** (8 items)

| item | declaration | read | fix | pending |
|---|---|---|---|---|
| SEAL-0458 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.96: Tactic `rewrite` failed: Did not find | use TCSlib.InformationTheory.isUniversal_iff (hf is applied as a function) and TCSlib.InformationTheory.FinDist.collision_def | - |
| SEAL-0459 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.111: Function expected at (#248 inherited | use TCSlib.InformationTheory.isUniversal_iff (hf is applied as a function) and TCSlib.InformationTheory.FinDist.collision_def | - |
| SEAL-0460 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.125: Application type mismatch: The argum | use TCSlib.InformationTheory.isUniversal_iff (hf is applied as a function) and TCSlib.InformationTheory.FinDist.collision_def | - |
| SEAL-0461 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.128: Application type mismatch: The argum | use TCSlib.InformationTheory.isUniversal_iff (hf is applied as a function) and TCSlib.InformationTheory.FinDist.collision_def | - |
| SEAL-0462 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.132: unsolved goals (#248 inherited_same_ | use TCSlib.InformationTheory.isUniversal_iff (hf is applied as a function) and TCSlib.InformationTheory.FinDist.collision_def | - |
| SEAL-0463 | `TCSlib.InformationTheory.collision_hashPair_le` | TCSlib.InformationTheory.collision_hashPair_le l.135: Tactic `rewrite` failed: Did not fin | use TCSlib.InformationTheory.isUniversal_iff (hf is applied as a function) and TCSlib.InformationTheory.FinDist.collision_def | - |
| C1-0343 | `TCSlib.InformationTheory.collision_hashPair_le` | 94 simp TCSlib.InformationTheory.FinDist.collision | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |
| C1-0344 | `TCSlib.InformationTheory.collision_hashPair_le` | 134 simp TCSlib.InformationTheory.FinDist.collision | use TCSlib.InformationTheory.FinDist.collision_def (TCSlib/InformationTheory/FinDist.lean) | - |

Totals per file: Complexity/Randomized/Build/IterateFind.lean 23; Complexity/Randomized/Build/IterateFindHost.lean 32; Complexity/Randomized/Build/PairSplit.lean 49; Complexity/Randomized/Build/UnaryMul.lean 13; Complexity/Randomized/Primitives.lean 2; Complexity/TuringMachine/Build/ModuleHost.lean 20; Cryptography/Asymptotic/Collections.lean 2; Cryptography/Asymptotic/Ensembles.lean 20; Cryptography/Asymptotic/EnsemblesLemmas.lean 11; Cryptography/Asymptotic/GoldreichLevinDomain.lean 2; Cryptography/Asymptotic/HardCore/Functions.lean 12; Cryptography/Asymptotic/HardCoreCollection.lean 14; Cryptography/Asymptotic/HardCoreGL.lean 8; Cryptography/Asymptotic/HardCoreLemmas.lean 2; Cryptography/Asymptotic/OneWayYao.lean 14; Cryptography/Asymptotic/SamplingFinDist.lean 3; Cryptography/Asymptotic/Universal.lean 9; Cryptography/Asymptotic/UniversalLemmas.lean 5; Cryptography/Asymptotic/UniversalPadding.lean 10; Cryptography/Candidates/Concrete.lean 1; Cryptography/Encryption/PublicKey/EnsembleSecurity.lean 10; Cryptography/Encryption/PublicKey/Hybrid.lean 5; Cryptography/Encryption/PublicKey/HybridMachine.lean 2; Cryptography/Encryption/PublicKey/Trapdoor.lean 6; Cryptography/Encryption/PublicKey/TrapdoorPredictor.lean 4; Cryptography/HardcoreBit/InnerProduct.lean 5; Cryptography/NumberTheory/Chebyshev.lean 1; Cryptography/NumberTheory/Primality.lean 1; Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean 7; Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean 18; Cryptography/Pseudorandom/Generators/Asymptotic/Defs.lean 7; Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean 3; Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean 8; Cryptography/ZeroKnowledge/Commitment.lean 13; Cryptography/ZeroKnowledge/CommitmentLemmas.lean 6; Cryptography/ZeroKnowledge/Defs.lean 16; Cryptography/ZeroKnowledge/EncodingPermutations.lean 7; Cryptography/ZeroKnowledge/GraphIsomorphism.lean 33; Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete.lean 4; Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean 4; Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI.lean 3; Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean 7; Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean 13; Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean 9; Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean 6; Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness.lean 18; Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator.lean 8; Cryptography/ZeroKnowledge/InteractiveProofs.lean 10; Cryptography/ZeroKnowledge/NP.lean 7; Cryptography/ZeroKnowledge/NPLemmas.lean 15; Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean 16; Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs.lean 11; Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean 17; Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine.lean 14; Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric.lean 20; InformationTheory/Entropy.lean 3; InformationTheory/LeftoverHash.lean 8 (total 597).

### Provider-reader list (STAGE2-PROVIDER-READER), by provider file

**TCSlib/Complexity/TuringMachine/Encoding.lean**

| reader needed | owner items |
|---|---|
| add Turing.CodeTM.toFinTM_tm (the tm/State fields of c.toFinTM are c.tm and Fin (c.numStates + 1)) | H:120, H:121, SEAL-0281, SEAL-0282, SEAL-0283 |
| add the case equations of Turing.pairDecode (pairDecode (false :: false :: r) = (pairDecode r).map (fun p => (false :: p.1, p.2)) | NEW:271, NEW:274, NEW:275, NEW:276, NEW:277, NEW:278, NEW:316, NEW:317, NEW:318, NEW:319, NEW:320, NEW:321 |

### For separate ruling: SEAL-B-ONLY

| file | items | declarations |
|---|---|---|
| Complexity/Randomized/PPT.lean | 1 | `Complexity.NUPPT.runAtL_ofPolyTimeUniform` |
| Complexity/Randomized/Primitives.lean | 1 | `Complexity.polyTimeComputable_unaryPoly` |
| Complexity/Randomized/Repetition.lean | 1 | `Complexity.polyTimeComputable_majority` |
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
| Cryptography/Authentication/Signatures/Lamport.lean | 16 | `TCSlib.Cryptography.Authentication.lamportOWF_f`, `TCSlib.Cryptography.Authentication.lamportOWF_inLen`, `TCSlib.Cryptography.Authentication.lamportOWF_outLen`, `TCSlib.Cryptography.Authentication.lamportOWF`, `TCSlib.Cryptography.Authentication.lamport_exists_best_position`, `TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability`, `TCSlib.Cryptography.Authentication.la |
| Cryptography/Candidates/DDH.lean | 1 | `TCSlib.Cryptography.Candidates.eval_ddhLen` |
| Cryptography/Candidates/Factoring.lean | 12 | `TCSlib.Cryptography.Candidates.eval_fmultBlocks`, `TCSlib.Cryptography.Candidates.exists_plantFactorer`, `TCSlib.Cryptography.Candidates.fac_prodInverter_eq_yaoB`, `TCSlib.Cryptography.Candidates.fac_strong_key`, `TCSlib.Cryptography.Candidates.fac_weak_key`, `TCSlib.Cryptography.Candidates.fmult_easy`, `TCSlib.Cryptography.Candidates.fmult_f`, `TCSlib.Cryptography.Candidates.fmult_inLen`, `TCSli |
| Cryptography/Candidates/RSA.lean | 3 | `TCSlib.Cryptography.Candidates.eval_rsaBlock`, `TCSlib.Cryptography.Candidates.eval_rsaSampleCoins`, `TCSlib.Cryptography.Candidates.eval_rsaTrials` |
| Cryptography/Candidates/Rabin.lean | 2 | `TCSlib.Cryptography.Candidates.rabin_genCore_eq`, `TCSlib.Cryptography.Candidates.rabin_genIndex` |
| Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean | 1 | `TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure.singleMessageSecure` |
| Cryptography/Encryption/PrivateKey/FromPRF.lean | 4 | `TCSlib.Cryptography.prfScheme_coinsEquiv_ofFn`, `TCSlib.Cryptography.prfScheme_coinsEquiv`, `TCSlib.Cryptography.prfScheme_multiMessageSecure`, `TCSlib.Cryptography.prfScheme` |
| Cryptography/Encryption/PrivateKey/FromPRF/MultiMsgOut.lean | 1 | `TCSlib.Cryptography.MultiMsg.exists_negligible_distAdv_prfEncRealOut` |
| Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean | 2 | `TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt`, `TCSlib.Cryptography.MultiMsg.postFun_layout` |
| Cryptography/Encryption/PrivateKey/FromPRG.lean | 5 | `TCSlib.Cryptography.prgScheme_encCoinsEquiv_ofFn`, `TCSlib.Cryptography.prgScheme_encCoinsEquiv`, `TCSlib.Cryptography.prgScheme_genCoinsEquiv_ofFn`, `TCSlib.Cryptography.prgScheme_genCoinsEquiv`, `TCSlib.Cryptography.prgScheme` |
| Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean | 3 | `TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler_finish`, `TCSlib.Cryptography.Composability.AdaptiveCPA.acTapes_apply`, `TCSlib.Cryptography.Composability.AdaptiveCPA.acTapes` |
| Cryptography/Encryption/PublicKey/EnsembleSecurity.lean | 1 | `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` |
| Cryptography/Encryption/PublicKey/OracleSecurity.lean | 2 | `TCSlib.Cryptography.BitPublicKeyScheme.padded`, `TCSlib.Cryptography.PublicKeyScheme.padded` |
| Cryptography/NumberTheory/Primality.lean | 1 | `TCSlib.Cryptography.NumberTheory.eval_samplePrimeCoins` |
| Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean | 5 | `TCSlib.Cryptography.OracleEnsemble.Indist.negligible_prfAdv`, `TCSlib.Cryptography.PRF.negligible_prfAdv`, `TCSlib.Cryptography.PRF`, `TCSlib.Cryptography.prfAdv_toOracleAdversary_out`, `TCSlib.Cryptography.prfAdv_toOracleAdversary` |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM.lean | 2 | `TCSlib.Cryptography.ggmPRF_prf`, `TCSlib.Cryptography.thm_97_3_1` |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean | 1 | `TCSlib.Cryptography.GGMRed.coinPoly_eval` |
| Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean | 11 | `TCSlib.Cryptography.PermFamily.iterPRG_eq_expand`, `TCSlib.Cryptography.PermFamily.iterPRG`, `TCSlib.Cryptography.cor_81_7`, `TCSlib.Cryptography.owpGenPRG_G_castSucc`, `TCSlib.Cryptography.owpGenPRG_G_last`, `TCSlib.Cryptography.owpGenPRG_G_outEquiv`, `TCSlib.Cryptography.owpGenPRG_outEquiv_ofFn`, `TCSlib.Cryptography.owpGenPRG_outEquiv`, `TCSlib.Cryptography.owpGenPRG`, `TCSlib.Cryptography.owp |
| Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean | 7 | `TCSlib.Cryptography.DoublingPRG.negligible_prgAdv`, `TCSlib.Cryptography.PRG.Secure.doubling`, `TCSlib.Cryptography.PRG.Secure.truncate`, `TCSlib.Cryptography.PRG.oneBit_G`, `TCSlib.Cryptography.PRG.oneBit_secure_iff`, `TCSlib.Cryptography.PRG.oneBit`, `TCSlib.Cryptography.doublingEnsemble` |
| Cryptography/Pseudorandom/Generators/Asymptotic/StretchMachine.lean | 1 | `TCSlib.Cryptography.prgIterFun_poly` |
| Cryptography/SecureComputation/Compose.lean | 1 | `TCSlib.Cryptography.SecureComputation.HybridProtocol.compose_rounds_eval` |
| Cryptography/SecureComputation/Defs.lean | 8 | `TCSlib.Cryptography.SecureComputation.otFunctionality_f_snd_apply`, `TCSlib.Cryptography.SecureComputation.otFunctionality_f_snd`, `TCSlib.Cryptography.SecureComputation.otFunctionality_f`, `TCSlib.Cryptography.SecureComputation.otFunctionality_inA`, `TCSlib.Cryptography.SecureComputation.otFunctionality_inB`, `TCSlib.Cryptography.SecureComputation.otFunctionality_outA`, `TCSlib.Cryptography.Secu |
| Cryptography/SecureComputation/GarblingSecurity.lean | 2 | `TCSlib.Cryptography.SecureComputation.garbling_good_whp`, `TCSlib.Cryptography.SecureComputation.nestedSpecial_wrongKeyBot` |
| Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean | 1 | `TCSlib.Cryptography.SecureComputation.GarblingCoins.nestedSpecial_wrongKeyBot_of_string_bounds` |
| Cryptography/SecureComputation/SpecialEncryptionSecurity.lean | 5 | `TCSlib.Cryptography.SecureComputation.PRFOut`, `TCSlib.Cryptography.SecureComputation.prfOut_var_iff`, `TCSlib.Cryptography.SecureComputation.spDecStr_wrongKey`, `TCSlib.Cryptography.SecureComputation.specialScheme_multiMessageSecure`, `TCSlib.Cryptography.SecureComputation.specialScheme_wrongKey` |
| Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean | 1 | `TCSlib.Cryptography.SecureComputation.SpecialWrongKey.exists_negligible_prefix_collision` |
| Cryptography/SecureComputation/Yao.lean | 9 | `TCSlib.Cryptography.SecureComputation.yaoCoins_eval`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_answersB_getD`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_callA`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_callB`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_hbcSecure`, `TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime`, `TCSlib.Cryptography.SecureComputation.yaoHyb |
| Cryptography/SecureComputation/YaoReal.lean | 1 | `TCSlib.Cryptography.SecureComputation.yaoProtocol_hbcSecure` |
| Cryptography/ZeroKnowledge/Commitment.lean | 3 | `TCSlib.Cryptography.multiAdvBound_eval`, `TCSlib.Cryptography.owpComLen_eval`, `TCSlib.Cryptography.owpComStr_ofFn` |
| Cryptography/ZeroKnowledge/CommitmentLemmas.lean | 2 | `TCSlib.Cryptography.CommitmentLemmas.ComLoop.init_poly`, `TCSlib.Cryptography.CommitmentLemmas.ComLoop.loopOut_poly` |
| Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean | 1 | `TCSlib.Cryptography.GI.unarySqrt_poly` |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean | 2 | `TCSlib.Cryptography.GI.iterUnary_poly`, `TCSlib.Cryptography.GI.peelLoop_poly` |
| Cryptography/ZeroKnowledge/NP.lean | 2 | `TCSlib.Cryptography.LevinReduction.refl`, `TCSlib.Cryptography.outV_pullback_cheat` |
| Cryptography/ZeroKnowledge/NPLemmas.lean | 2 | `TCSlib.Cryptography.LevinTransfer.exists_liftDistinguisher`, `TCSlib.Cryptography.LevinTransfer.polyExpr_eval_const_or_strictMono` |
| Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean | 1 | `TCSlib.Cryptography.ColMachines.eRep_poly` |

### For separate ruling: STATEMENT

| file | items | declarations |
|---|---|---|
| Complexity/Randomized/Build/IterateFindHost.lean | 3 | `Complexity.IterateFind.host_branch`, `Complexity.IterateFind.host_dispatch`, `Complexity.IterateFind.host_halt` |

### STRICT-ONLY (notation, no fix): recorded diagnostics only (Q3)

| file | items | strict errors (A+B) |
|---|---|---|
| Cryptography/Foundations/Experiments.lean | 2 | 6 |
| Cryptography/Games/Probability.lean | 1 | 2 |
| Cryptography/Randomness/Extraction/Rejection.lean | 16 | 36 |
| InformationTheory/Entropy.lean | 5 | 10 |
| InformationTheory/Extractors.lean | 4 | 12 |
| InformationTheory/LeftoverHash.lean | 1 | 2 |
| InformationTheory/StatisticalDistance.lean | 2 | 8 |

### Harness interactions: file-level `failed to set [local irreducible]` (DW10-W5; no class)

| file | item | status | line | errors per variant (sA/sB/cA/cB) |
|---|---|---|---|---|
| Complexity/ClassP/BinaryArith/Unary.lean | NEW:1 | NEW | <outside src:37> | 3/3/3/3 |
| Complexity/ClassP/BinaryArith/Unary.lean | NEW:2 | NEW | <outside src:38> | 3/3/3/3 |
| Complexity/Randomized/UnaryPolynomial.lean | NEW:30 | NEW | <outside src:38> | 2/2/2/2 |
| Complexity/TuringMachine/Build/WordTiming.lean | NEW:31 | NEW | <outside src:33> | 2/2/2/2 |
| Complexity/TuringMachine/Build/WordTiming.lean | NEW:32 | NEW | <outside src:34> | 3/3/3/3 |
| Cryptography/Asymptotic/UniversalPadding/BinaryRoot.lean | NEW:94 | NEW | <outside src:36> | 4/4/4/4 |
| Cryptography/Asymptotic/UniversalPadding/BinaryRoot.lean | NEW:95 | NEW | <outside src:37> | 4/4/4/4 |
| Cryptography/Asymptotic/UniversalPadding/BinaryRoot.lean | NEW:96 | NEW | <outside src:38> | 2/2/2/2 |
| Cryptography/Asymptotic/UniversalPadding/Machine.lean | NEW:97 | NEW | <outside src:39> | 2/2/2/2 |
| Cryptography/Asymptotic/UniversalPadding/Machine.lean | NEW:98 | NEW | <outside src:40> | 3/3/3/3 |
| Cryptography/Asymptotic/UniversalPadding/Machine.lean | NEW:99 | NEW | <outside src:41> | 5/5/5/5 |
| Cryptography/Pseudorandom/Functions/GGM.lean | NEW:166 | NEW | <outside src:68> | 2/2/2/2 |
| Cryptography/Pseudorandom/Functions/SubHybrids.lean | SEAL-0306 | STILL_OPEN | <outside src:68> | 2/2/2/2 |
| Cryptography/Pseudorandom/Functions/SubHybrids.lean | SEAL-0307 | STILL_OPEN | <outside src:68> | 2/2/2/2 |

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
| Complexity/ClassP/BinaryArith/Unary.lean | 2 | 0 | 0 | Gate 11 | - 2 |
| Complexity/Randomized/Build/IterateFind.lean | 1 | 0 | 0 | F-01 | STAGE2 1 |
| Complexity/Randomized/Build/IterateFindHost.lean | 8 | 27 | 0 | DW-9 | STAGE2 32, STATEMENT 3 |
| Complexity/Randomized/Build/PairSplit.lean | 10 | 45 | 0 | Gate 11 | STAGE2 49, STAGE2-PROVIDER-READER 6 |
| Complexity/Randomized/Build/UnaryMul.lean | 3 | 16 | 0 | - | STAGE2 13, STAGE2-PROVIDER-READER 6 |
| Complexity/Randomized/PPT.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Complexity/Randomized/Primitives.lean | 3 | 0 | 0 | Gate 11 | STAGE2 2, SEAL-B-ONLY 1 |
| Complexity/Randomized/Repetition.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Complexity/Randomized/UnaryPolynomial.lean | 1 | 0 | 0 | Gate 11 | - 1 |
| Complexity/TuringMachine/Build/WordTiming.lean | 2 | 0 | 0 | Gate 11 | - 2 |
| Cryptography/Asymptotic/BlockEncryptor.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Asymptotic/Collections.lean | 5 | 0 | 0 | - | SEAL-B-ONLY 5 |
| Cryptography/Asymptotic/Ensembles.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Asymptotic/GoldreichLevinDomain.lean | 1 | 1 | 0 | - | STAGE2 2 |
| Cryptography/Asymptotic/HardCore/Functions.lean | 13 | 0 | 0 | - | SEAL-B-ONLY 13 |
| Cryptography/Asymptotic/HardCoreCollection.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Asymptotic/HardCoreGL.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Asymptotic/HardCoreGLColl.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Asymptotic/HardCoreGLFamily.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Asymptotic/HardCoreLemmas.lean | 3 | 0 | 0 | - | SEAL-B-ONLY 3 |
| Cryptography/Asymptotic/HardCorePermutation/GoldreichLevin.lean | 6 | 0 | 0 | - | SEAL-B-ONLY 6 |
| Cryptography/Asymptotic/OneWay.lean | 20 | 0 | 0 | - | SEAL-B-ONLY 20 |
| Cryptography/Asymptotic/OneWayYao.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Asymptotic/SamplingFinDist.lean | 1 | 1 | 1 | - | STAGE2 3 |
| Cryptography/Asymptotic/Universal.lean | 2 | 0 | 0 | Gate 35; Gate 11 | SEAL-B-ONLY 2 |
| Cryptography/Asymptotic/UniversalPadding/BinaryRoot.lean | 3 | 0 | 0 | Gate 11 | - 3 |
| Cryptography/Asymptotic/UniversalPadding/Machine.lean | 3 | 0 | 0 | Gate 11 | - 3 |
| Cryptography/Authentication/Signatures/Lamport.lean | 16 | 0 | 0 | - | SEAL-B-ONLY 16 |
| Cryptography/Candidates/DDH.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Candidates/Factoring.lean | 12 | 0 | 0 | - | SEAL-B-ONLY 12 |
| Cryptography/Candidates/RSA.lean | 3 | 0 | 0 | - | SEAL-B-ONLY 3 |
| Cryptography/Candidates/Rabin.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Encryption/PrivateKey/EnsembleSecurity.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Encryption/PrivateKey/FromPRF.lean | 4 | 0 | 0 | - | SEAL-B-ONLY 4 |
| Cryptography/Encryption/PrivateKey/FromPRF/MultiMsgOut.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Encryption/PrivateKey/FromPRG.lean | 5 | 0 | 0 | - | SEAL-B-ONLY 5 |
| Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean | 3 | 0 | 0 | - | SEAL-B-ONLY 3 |
| Cryptography/Encryption/PublicKey/EnsembleSecurity.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Encryption/PublicKey/OracleSecurity.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Foundations/Experiments.lean | 2 | 0 | 0 | - | STRICT-ONLY (notation, no fix) 2 |
| Cryptography/Games/Probability.lean | 1 | 0 | 0 | BS-F06 | STRICT-ONLY (notation, no fix) 1 |
| Cryptography/NumberTheory/Chebyshev.lean | 1 | 0 | 0 | - | STAGE2 1 |
| Cryptography/NumberTheory/Primality.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean | 5 | 0 | 0 | - | SEAL-B-ONLY 5 |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Run.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Pseudorandom/Functions/GGM.lean | 1 | 0 | 0 | - | - 1 |
| Cryptography/Pseudorandom/Generators/Asymptotic/FromPermutation.lean | 9 | 0 | 0 | - | SEAL-B-ONLY 9 |
| Cryptography/Pseudorandom/Generators/Asymptotic/Stretch.lean | 7 | 0 | 0 | - | SEAL-B-ONLY 7 |
| Cryptography/Pseudorandom/Generators/Asymptotic/StretchMachine.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/Randomness/Extraction/Rejection.lean | 16 | 0 | 0 | - | STRICT-ONLY (notation, no fix) 16 |
| Cryptography/SecureComputation/Compose.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/SecureComputation/Defs.lean | 8 | 0 | 0 | - | SEAL-B-ONLY 8 |
| Cryptography/SecureComputation/YaoReal.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/ZeroKnowledge/Commitment.lean | 3 | 0 | 0 | - | SEAL-B-ONLY 3 |
| Cryptography/ZeroKnowledge/CommitmentLemmas.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/ZeroKnowledge/InteractiveProofs.lean | 3 | 7 | 0 | - | STAGE2 10 |
| Cryptography/ZeroKnowledge/NP.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/ZeroKnowledge/NPLemmas.lean | 2 | 0 | 0 | - | SEAL-B-ONLY 2 |
| Cryptography/ZeroKnowledge/ThreeColoring/Parties.lean | 1 | 0 | 0 | - | SEAL-B-ONLY 1 |
| InformationTheory/Entropy.lean | 8 | 0 | 0 | - | STAGE2 3, STRICT-ONLY (notation, no fix) 5 |



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
- **DW10-W5. File-level `failed to set [local irreducible]` diagnostics.** Some owner files already make a definition locally
  irreducible with their own `attribute [local irreducible] …` line. Under the seal that line fails ("`X` is currently
  `[irreducible]`, `[semireducible]` expected"). The definition is already irreducible, so no later step is masked. #248 recorded
  two of these, SEAL-0306 and SEAL-0307 (`SubHybrids` l.68, disposition `inherited_source_attribute_interaction`, scope
  NO-DECLARATION). They reproduce at the base, and the NEW rows add the same diagnostic at the attribute lines of `Unary`,
  `UnaryPolynomial`, `WordTiming`, `UniversalPadding/BinaryRoot`, `UniversalPadding/Machine` and `Pseudorandom/Functions/GGM`.
  None of the five classes fits.
  (a) *Recommended, applied:* these are not seal debt. The rows keep their status (STILL_OPEN or NEW), get no class and the fix
  "none (harness interaction)", carry pending `DW10-W5`, and are listed separately. A later harness could leave out the
  definitions an owner already marks locally irreducible, or install with `allowUnsafeReducibility`.
  (b) Class them STAGE2, with the fix "drop the file's own attribute line". That would change the owner's behaviour outside the
  seal, so the job does not recommend it.
- **DW10-W6. Shadow transfers (sub-A's review, 39 rows).** Four files restate main-file definitions verbatim in their own
  namespaces (`GI`, `ColProofs`, `GIZK`, `ColSimMachine`):
  - `ZeroKnowledge/GraphIsomorphism/Proofs.lean`
  - `ThreeColoring/ProtocolProofs.lean`
  - `GraphIsomorphismZK/Simulator.lean`
  - `ThreeColoring/SimulatorNumeric.lean`

  The main files take the shadow's results over by definitional equality, which the seal breaks.
  (a) *Recommended, applied:* STAGE2. Each row's fix names a bridge equation `X = GI.X` (or the like), proved from the shadow's
  published or to-be-added readers.
  (b) Retire the shadow copies in Stage 2 and state the results once, on the main definitions. That is a larger refactor, and it
  touches no statement.
  The choice is a design decision for Stage 2; the inventory rows do not depend on it.
- **DW10-W7. Lexer false positives from local bindings.** The archived lexer resolves an unqualified name without local context,
  so a local `let P := …` read by `simp [P]` is inventoried as a read of `Complexity.P`. Four scan items are such locals:
  - `SeedMajority/Enumeration` l.71
  - `Candidates/DiscreteLogHardcore` l.2656 (C1-0284; #248 recorded it)
  - `SecureComputation/SpecialEncryptionMulti` l.301
  - `Yao/HybridProof/GarbledRun` l.117

  (a) *Recommended, applied:* drop them as not reads; they are listed in `evidence/scan-shadowed.tsv`. C1-0284 is FIXED_SINCE,
  and its `change` says why. Only a binder directly naming the item counts: `let`, `set` or `have X`, `intro`/`obtain` patterns,
  `fun` binders, and `(… X :` binders. The archived lexer is left unmodified.
  (b) Keep them as items with the fix "none".


## Evidence

`evidence/SHA256SUMS` lists every evidence file; the top-level `SHA256SUMS` every delivered file. Large directories (collector logs,
seal records and probe sources, seal logs, scan inputs, control harnesses and logs) are in `evidence/zip/<name>.partNN.zip` (at most
90 MB each) with `<name>.partNN.entries.txt` (path, bytes, SHA-256 of each uncompressed file).
