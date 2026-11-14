# Resolutions — quantum E1 epoch boundary

The epoch gate follows the phase-gate rule (`workflow.md` §3–4): it closes only on a round
reporting zero blockers and zero majors, and a debt major closes only by explicit human
acknowledgment recorded here. Round 1 reported two debt majors, repaired and acknowledged; round 2,
a full re-audit, reported zero blockers and zero majors. **The gate is closed** (§ Closing).

## Round 1

| Item | Value |
|---|---|
| Commit audited | `a97fceca7c0f7b360f91cb08d4db5a5b33bdb548` (branch `quantum/e1-fill`) |
| Pack | `pack.md` (shipped; not edited since, errata below) |
| Bundle | not committed; SHA-256 `3b73500309d40d61bd133f630ddafb2b991a6539d3b1815a2f3298bc3afde812`, built by `evidence/make_bundle.sh` |
| Auditor | an external model from a different vendor, in a fresh chat, with the bundle |
| Findings | `findings.md`, verbatim: **0 blockers, 2 majors, 7 minors**. Statement freeze confirmed independently from the diff (134 → 168 named declarations in the five files, plus the unchanged anonymous instance, which `findings.md` counts in its 135 → 169; round 2, R2-3; every carried-over name, signature and relative order unchanged; exactly 52 bodies went from `sorry` to proofs); all six new public declarations restated and argued true; answers to all seven questions |

### Dispositions

| # | Severity | Finding | Disposition | Where |
|---|---|---|---|---|
| 1 | major (debt) | An anonymous `example` restated `probQubit_basis` with the identical two-line proof; the copy screen misattributed it to `probQubit_zero_add_one` | **Repaired** (the auditor's direct repair): the `example` is deleted. **Acknowledged by the owner** (2026-11-12, below) | `Measure.lean` |
| 2 | major (debt) | `hadamardMat_mem_unitaryGroup` and `Gate.H_mul_H` each computed the four entries of the Hadamard square | **Repaired** (the auditor's construction): two public matrix-level lemmas before `Gate.H`, `hadamardMat_conjTranspose` (`Hᴴ = H`) and `hadamardMat_mul_self` (`H H = 1`). Unitarity is now `star H * H = H * H = 1` by rewriting with both; `H_mul_H` is `Subtype.ext hadamardMat_mul_self`. The square is computed once. While repairing, the copy screen showed `hadamardMat_mul_self` sharing the four-entry case split with the private `gate1_ext`; that split is now the private matrix-level `mat1_ext`, and `gate1_ext` is `Subtype.ext (mat1_ext h)`. **Acknowledged by the owner** (2026-11-12, below) | `Gates.lean` |
| 3 | minor | Two sketches described a step differently from the code | **Repaired.** `applyOn_permMat_mulVec_apply` now names `Finset.sum_eq_single`, the lemma the proof uses. The Hadamard unitarity sketch now describes the two-lemma route of the repair | `ApplyOn.lean`, `Gates.lean` |
| 4 | minor | `applyOn_mulVec_apply` and `applyOn_wire_mulVec_apply` hold for arbitrary matrices and vectors, not only the textbook's unitary gates; "new value `a`" misnamed the input bit | **Repaired.** Both docstrings call themselves coordinate formulas for an arbitrary matrix and vector that extend [dW26, §2.1.2] and [dW26, §1.4]. The one-wire docstring says `a` is the input bit and `y i` the output bit, and says "operator" rather than "gate" | `ApplyOn.lean` |
| 5 | minor | Three long proofs lacked inline step markers (policy §3) | **Repaired.** Comments mark the sketch's steps in `applyOn_mul_applyOn_of_disjoint` (the candidate `z*` and its properties; the single surviving term; the term at `z*`; uniqueness), `no_cloning_of_overlap` (the two inner products; preservation by `U`; the moduli) and `teleport_outcome_prob` (the reindexing by Bob's bit; unitarity; the bijection; the summands) | `ApplyOn.lean`, `Protocols.lean` |
| 6 | minor | `ApplyOn.lean` and `Protocols.lean` unfolded `flipAt`, `cnotMap` and `hadamardMat` from `Gates.lean` (policy §1) | **Repaired.** Every cross-file use (ten unfoldings on nine lines) now goes through the published `flipAt_eq`, `cnotMap_eq` and `hadamardMat_apply`. (One side effect, visible in the axiom census: `cnotMap.eq_1`, generated only because `Protocols.lean` unfolded `cnotMap`, is no longer generated.) Uses inside `Gates.lean`, the defining file, are unchanged | `ApplyOn.lean`, `Protocols.lean` |
| 7 | minor | `drift.py` compared declarations by name only, ignoring order, and absorbed the anonymous `example` into the preceding body | **Repaired in the round-1 evidence** (`evidence-r1/scripts/drift.py`). It now (a) treats `example` and unnamed `instance` as command boundaries, (b) checks per file that the declarations present at both commits occur in the same order, and (c) inventories anonymous commands separately, old → new. The repository's shared `scripts/copy-text-screen-v3.py` still does not open a declaration at `example`; it is used by other campaigns and is not edited here. Instead, `evidence-r1/scripts/copy_screen.sh` first lists every `example` in the screened files, and the screen's rows are exact only when that list is empty (it is). A fix to the shared screen is left to its maintainers | evidence |
| 8 | minor | Counts and counter descriptions in the fill report | **Repaired in place**, with an errata section in `campaign/fills/e1/REPORT.md`: `ApplyOn.lean` has 9 private helpers; the 19 inherited theorems were 18 equation lemmas and `Ket.nonempty_reg_zero`; the campaign lint's public count omits the anonymous instance; the sweep's second counter counts warning and error lines | `campaign/fills/e1/REPORT.md` |
| 9 | minor | The axiom attestation lacked the change by kind (`workflow.md` §4, *Counting public names*) | **Repaired.** New `evidence-r1/scripts/axiom_diff.py` compares two censuses by name and classifies changes as source declarations, generated equation lemmas, matchers, `congr_simp` lemmas or auxiliary proofs. At the round-1 commit it reproduces the auditor's count exactly (`logs/axiom_diff_gate_to_e1fill.log`: 22 added, 0 removed; 6 source theorems, 12 equation lemmas, 2 matchers, 2 `congr_simp`). The census is now described as a census of non-internal constants, with private declarations covered through the public constants that use them and by the sweep's `sorry` count | evidence, report |

### Also from the answers

- **Answer 3, smaller reuse opportunities.** Both taken. The one-wire `extend`-to-`update`
  argument, written twice in `ApplyOn.lean`, is the private `extend_wire`, used by
  `applyOn_wire_mulVec_apply` and `applyOn_wire_X_mulVec_basis`. In `Protocols.lean`,
  `X_pow_mul_self` and `Z_pow_mul_self` are replaced by one private `pow_mul_self_of_mul_self`
  (`g g = 1 → gᵐ gᵐ = 1`). Removing the two private names is not a freeze matter: neither was
  audited at the gate.
- **Answer 5.** No promotion requested; none made beyond the two Hadamard lemmas of finding 2.
- **Answer 6, process.** The single-owner fill and the in-place promotions depart from
  `workflow.md` §4's parallel batches and shared-file window. The auditor accepts
  `superdenseState_vec_aux` as the way to keep audited order, and asks that the maintainer's
  acceptance of the departures be recorded here. **Accepted by the owner** (2026-11-12, below).
- **Pack errata.** The pack said the 7 `Quantum` modules report "no diagnostic at all"; the sweep
  counts warning and error lines only (finding 8). The pack's "212 → 246 declarations" counted
  the anonymous instance as a declaration and the anonymous `example` not at all (finding 7). The
  pack is not edited (`workflow.md` §3).

### Human acknowledgments

`workflow.md` §4: "a debt major closes only by explicit human acknowledgment recorded in the
resolutions file". Both majors are repaired by removing the duplication, so what the owner
acknowledges is that disposition.

| Item | Owner decision |
|---|---|
| Major 1: the duplicate `example` removed | **Acknowledged**, a-gupte, 2026-11-12 |
| Major 2: the Hadamard square factored into `hadamardMat_mul_self` (with `hadamardMat_conjTranspose` and `mat1_ext`) | **Acknowledged**, a-gupte, 2026-11-12 |
| Answer 6: the single-owner fill and in-place promotions accepted as disclosed departures from `workflow.md` §4 | **Accepted**, a-gupte, 2026-11-12 |

### Round-2 baseline

| Item | Value |
|---|---|
| Lean commit for round 2 | `647511e33e2c8b2a8c567362b0f3c756da78d2c9` (repairs in `015279c7`, `f12a9499`, `647511e3`) |
| Change since round 1 | `evidence-r1/tcslib-r1-repairs.diff`: 4 files, 94 insertions, 66 deletions. `Register.lean` unchanged |
| Change since the gate baseline | `evidence-r1/tcslib-e1-r2.diff`: the 5 files, 747 insertions, 109 deletions |
| Drift from round 1 (`logs/drift_vs_e1.log`) | 245 → 248 named declarations: **0 signatures changed**; 2 private removed (`X_pow_mul_self`, `Z_pow_mul_self`); 5 added (public `hadamardMat_conjTranspose`, `hadamardMat_mul_self`; private `mat1_ext`, `extend_wire`, `pow_mul_self_of_mul_self`); 11 bodies changed (below); 232 unchanged; order of carried-over declarations the same in every file; anonymous commands: `Measure.lean` 1 → 0 (the `example`), `ApplyOn.lean` 1 → 1 (the `Decidable` instance) |
| The 11 changed bodies | finding 2: `hadamardMat_mem_unitaryGroup`, `H_mul_H`, `gate1_ext`; finding 6: `applyOn_wires20_CNOT_mulVec_basis`, `cnot_extend_wires01`, `flipAt_const`, `superdenseState_vec_aux`, `teleportState_vec`; finding 6 and `extend_wire`: `applyOn_wire_X_mulVec_basis`; `extend_wire`: `applyOn_wire_mulVec_apply`; `pow_mul_self_of_mul_self`: `teleport_correct`. The step comments of finding 5 are comments, which the drift check strips |
| Drift from the gate baseline (`logs/drift_vs_gate.log`) | 211 → 248 named declarations: **0 removed, 0 signatures changed, exactly 52 bodies changed** (the former `sorry`s), 37 added (8 public, 29 private), 159 unchanged; order the same in every file; anonymous commands 1 → 1 (`ApplyOn`'s instance) |
| Sweep (`logs/sweep.log`) | 14 modules pass; the 7 `Quantum` modules have no `sorry` warning and no other warning or error line; 33 `sorry` warnings, all in `Promise` and `Counting` |
| Axiom census (`logs/axioms.log`) | 267 non-internal constants. All **174** `Quantum` constants use only `propext`, `Classical.choice`, `Quot.sound` (or none); 33 `SORRY`, all outside `Quantum`. Against the gate (`axiom_diff_vs_gate.log`): 21 added (8 source theorems, 11 equation lemmas, 2 `congr_simp`), 0 removed, 90 carried over from `SORRY` to `CLEAN`. Against round 1 (`axiom_diff_vs_e1.log`): 2 added (the two Hadamard theorems), 3 removed (`cnotMap.eq_1`; the matchers `applyOn_wire_mulVec_apply.match_1_1` and `applyOn_wire_X_mulVec_basis.match_1_1`, whose patterns moved into the private `extend_wire`) |
| Lints | `style_lint.py`: 0 findings over the 14 P1 files (10 modules and 4 facades). `campaign_style_lint.py`: 0 FAIL, 0 WARN. No line exceeds 100 characters |
| Copy screen (`logs/copy_screen.log`) | boundary check: no `example`. 132 declarations, 22 pairs: 15 among the E1 files (was 21), 7 inside the two older files (unchanged). Gone: the misattributed `Measure` pair, both Hadamard directions, and the three `hadamardMat_mem_unitaryGroup` pairs. The 15 left: 10 among `X_mul_X`, `Z_mul_Z`, `S_mul_S`, `H_mul_Z_mul_H` (the `gate1_ext` / `fin_cases` / `simp` idiom across four different gate identities); 4 among `X_mulVec_apply`, `cnot_mulVec_apply`, `teleportState_vec_sum` (the permutation-gate rewrite chain, three different gates); `superdenseState_vec_aux` / `teleportState_vec` (the closing case split, two protocols) |

`campaign/gates/02-quantum-e1/evidence-r1/` holds the scripts (E1's sweep, axiom probe and lint
wrapper unchanged; the revised `drift.py`, `copy_screen.sh`, and the new `axiom_diff.py`) and all
logs above.

## Round 2

| Item | Value |
|---|---|
| Lean commit audited | `647511e33e2c8b2a8c567362b0f3c756da78d2c9` (records on top in `c678475b`, `a7a507eb`) |
| Pack | `pack-r2.md` (shipped; not edited since) |
| Bundle | not committed; SHA-256 `b7d6d29769401c3c8faa45f4d1b1fe246e9a372d959c49dbfc12458f781458c7`, 326,038 bytes, 30 attachment sections after the pack, built by `evidence-r1/make_bundle.sh` (the auditor confirmed the hash) |
| Auditor | an external model from a different vendor, in a fresh chat, with the bundle |
| Findings | `findings-r2.md`, verbatim: **0 blockers, 0 majors, 3 minors, 1 note**. All nine round-1 repairs verified, major 2 confirmed as the proposed construction; the cumulative freeze re-checked independently by reverse-applying both diffs (134 → 171 named declarations in the five files, 52 former `sorry` bodies, 82 other baseline bodies unchanged, no removal, re-signature or reordering); both new public declarations restated and argued true, with a targeted check that pinned Mathlib has no duplicate; every copy-screen row reclassified (15 E1 rows, all idiom; `H_mul_Z_mul_H` a different character sum from `H H = 1`); `axiom_diff.py` re-run on the logs, reproducing all three breakdowns |

### Dispositions

Under the gate rule, minors may be swept in the closing commit and re-verified (`workflow.md` §3).
All four items are swept in `9cbfdc60`.

| # | Severity | Finding | Disposition | Where |
|---|---|---|---|---|
| R2-1 | minor | E1 still passed core/Mathlib definitions to `simp`/`rw` (`mulVec`, `dotProduct`, `Function.comp`, `finTwoArrowEquiv`), against policy §1 | **Repaired.** Pinned Mathlib has no equation lemma for `dotProduct` or for an entry of `mulVec`, so each use becomes the definitional step policy §1 permits: `rw [show (M *ᵥ v) y = ∑ z, M y z * v z from rfl]` (`permMat_mulVec_basis`, `applyOn_mulVec_apply`, `applyOn_mulVec_basis`, `wire_sum_eq_mulVec`), the same for `star w ⬝ᵥ w` (`sum_norm_sq_eq_dotProduct`), a local `rfl` fact `hdot` (`no_cloning_of_overlap`), a `show` (`applyOn_mulVec_proj`) and a `change … at h` (`applyOn_mul`). `Function.comp` becomes core's `Function.comp_apply` (`applyOn_mul_applyOn_of_disjoint`), and `finTwoArrowEquiv` its `simps` lemma `finTwoArrowEquiv_symm_apply` (`sum_norm_sq_bellVec`). A scan of every `simp`/`rw` argument in the five files finds no other definition outside its own file. No public declaration was added. (Visible in the census: `finTwoArrowEquiv.eq_1`, generated only by that unfolding, is gone.) | `Register`, `Gates`, `ApplyOn`, `Measure`, `Protocols` |
| R2-2 | minor | The fill report's historical ledger still said "Copies of proved material: none" | **Repaired.** The ledger in `campaign/fills/e1/REPORT.md` is marked superseded, names both admitted duplicates, points to this file's current ledger, and keeps its counts tied to `a97fceca`. The errata list the change | `campaign/fills/e1/REPORT.md` |
| R2-3 | minor | "135 → 169 named" counted the anonymous instance; the report's "Sixteen sketches" listed 17 | **Repaired.** Round 1's row now reads 134 → 168 named declarations plus the unchanged instance; round 1's `findings.md`, which says 135 → 169, stays verbatim, and this row records the correction. The report says seventeen. (The round-1 `pack.md` also says sixteen; packs are not edited, so this is a pack erratum.) | this file, `REPORT.md` |
| R2-4 | note | `pow_mul_self_of_mul_self` is Mathlib's `pow_mul_pow_eq_one` at `a = b = g` | **Taken.** The private helper is deleted, and `teleport_correct` uses `pow_mul_pow_eq_one _ Gate.X_mul_X` and `… Gate.Z_mul_Z`; its sketch names the lemma | `Protocols.lean` |

The auditor's notes on tooling limits are recorded, not acted on now: `drift.py` is a source-text
heuristic (not nested-comment aware, short names, first `:=` split), which did not affect any
comparison here; a non-empty `example` list from `copy_screen.sh` would invalidate the screen's
rows until the examples are delimited (a fix to the shared screen is a suggested separate task);
and `axiom_diff.py` does not yet classify `_simp_N` or public instances derived for private types,
neither of which occurs.

## Closing

| Item | Value |
|---|---|
| Closing Lean commit | `9cbfdc606cf8ee585395cdb1e5b93bfb54bbef11` |
| Change since round 2 | `evidence-close/tcslib-r2-close.diff`: the five files, 23 insertions, 21 deletions |
| Drift from round 2 (`evidence-close/logs/drift_vs_r2.log`) | 248 → 247 named declarations; **0 signatures changed**; 1 private removed (`pow_mul_self_of_mul_self`, R2-4); 0 added; 11 bodies changed, exactly the R2-1 and R2-4 sites: `sum_norm_sq_eq_dotProduct`, `permMat_mulVec_basis`, `applyOn_mulVec_apply`, `applyOn_mul`, `applyOn_mul_applyOn_of_disjoint`, `applyOn_mulVec_basis`, `applyOn_mulVec_proj`, `no_cloning_of_overlap`, `sum_norm_sq_bellVec`, `wire_sum_eq_mulVec`, `teleport_correct`; 236 unchanged; order the same; anonymous commands unchanged (`ApplyOn`'s instance only) |
| Drift from the gate baseline (`evidence-close/logs/drift_vs_gate.log`) | 211 → 247 named declarations: **0 removed, 0 signatures changed, exactly 52 bodies changed** (the former `sorry`s), 36 added (8 public, 28 private), 159 unchanged; order the same in every file |
| Sweep (`evidence-close/logs/sweep.log`) | 14 modules pass; the 7 `Quantum` modules have no `sorry` warning and no other warning or error line; 33 `sorry` warnings, all in `Promise` and `Counting` |
| Axiom census (`evidence-close/logs/axioms.log`) | 266 non-internal constants. All **173** `Quantum` constants use only `propext`, `Classical.choice`, `Quot.sound` (or none). Against round 2 (`axiom_diff_vs_r2.log`): 0 added, 1 removed (`finTwoArrowEquiv.eq_1`). Against the gate (`axiom_diff_vs_gate.log`): 20 added (8 source theorems, 10 equation lemmas, 2 `congr_simp`), 0 removed, 90 carried over from `SORRY` to `CLEAN` |
| Lints | `style_lint.py`: 0 findings over the 14 P1 files. `campaign_style_lint.py`: 0 FAIL, 0 WARN. No line exceeds 100 characters |
| Copy screen (`evidence-close/logs/copy_screen.log`) | boundary check: no `example`. 22 pairs, unchanged: the same 15 E1 rows and 7 older rows as round 2. The screen now reports 135 declarations screened (132 in round 2) because it screens only bodies of at least 60 characters, and the `show … from rfl` steps lengthened three short proofs past that threshold |

**Gate closed** (2026-11-14): round 2 reported zero blockers and zero majors; its three minors and
its note are swept in `9cbfdc60` and re-verified above; both round-1 debt majors and the process
departure are acknowledged by the owner (§ Round 1). Epoch E1 is complete.
