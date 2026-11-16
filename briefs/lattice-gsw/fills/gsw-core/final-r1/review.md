# gsw-core · maintainer delivery review (r1)

**Verdict: ACCEPT.** All 29 targets are proved with the standard three axioms only. The review finds 0 blockers,
0 majors, 0 minors and six info findings. No landing edit is proposed: the delivered head lands as is.

## Delivery and landing
- **Delivery:** Claude, a lead with two sub-agents:
  - A: F1 and F2, in `Gadget` and `Noise`;
  - B: F3 and F7, in `Scheme` and `Symmetric`;
  - the lead: F4 in `Eval`, plus integration, every commit and the final checks.
- **Exchange commits:** the final is `9e52a5019258c51d67b1f28d3675c66cf787209b` and the checkpoint is
  `5b72e346bd5484fb059cbaadd836de88f4adf0a2`. Both touch only `inbox/fills/gsw-core/`.
- **Issue base:** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, #333's head, with #332 as an ancestor.
- **Head:** `d4ebb0be088e5985337ccb4e0a61cb3a662e8b73`, three commits:
  - `243a44cd`: F1 and F2;
  - `a1bc6aac`: F4, with `decrypt_keygen_eval` proved modulo F3 at that point;
  - `d4ebb0be`: F3 and F7.

  The checkpoint carried the first two commits, with the same hashes.
- **Files:** the five owned files only, +542/−89:

  | File | Lines (base → final) |
  |---|---|
  | `Gadget` | 204 → 236 |
  | `Noise` | 235 → 321 |
  | `Scheme` | 215 → 364 |
  | `Symmetric` | 111 → 185 |
  | `Eval` | 209 → 321 |

  No import was added. No frozen file, helper module or facade was touched, and there was no scope request.
- **Landing:**
  - The base is an ancestor of the records tip `4941b5119c82431452face78071bd4376ee3e427`; #332 and #333 are merged.
    Since the tip used in Phase 1 (`d0007941`), the tip has changed only in records.
  - `git merge-tree` of the tip and `d4ebb0be` is clean and gives tree `76fae5c89bce2097cf32b536edfdec6544a49bcb`. It
    differs from the tip only in the five files, each blob-equal to the delivered one. This is the tree that was built.
  - Between the base and the tip, two modules in the build order changed, both by additions only: `DAGCircuit` gained
    `isFaninTwo_iff` and `Randomized/Classes` gained `inBPP_iff`. Neither name clashes with the fill.
- **Evidence:** `gsw-core-r1-evidence.zip`, SHA-256 `4c481a79b6995ffb7fc3135a83683ec790a210018e2f5f77cd5392d74029a61c`, 1096 entries. It does not include the delivery,
  which is on the exchange.

## Checks
- **Integrity.**
  - The top-level manifest verifies 544/544, and its path set equals the delivered files exactly, with no `./`.
  - `evidence/SHA256SUMS` verifies 533/533 with an exact path set (534 files including the manifest).
  - `git am` at the base, with the recorded identities and dates, reproduces all three hashes, unsigned. The five
    files equal `src/`.
- **Build, on the merged tree with `dl-oleans`.**
  - 650 modules were rebuilt and 638 reused. All 650 give rc 0, with 0 errors in both forms and no `error`
    substring. That covers root `TCSlib` and both `audits/*/Checks`, in 5863 s.
  - The pinned Mathlib `NthRootLemmas` was built separately (rc 0).
  - The whole-tree check covers 1288 modules: OK. The state check is OK.
  - The five owned modules have 0 warnings. `Security`, the GSW, Homomorphic and AdvancedEncryption facades, root
    `TCSlib` and both `Checks` give rc 0.
- **Statements.** I checked them with my own script, independently of the delivery's.
  - Every base item of the five files reappears in order.
  - The 29 targets keep their headers byte-identical, and their docstrings byte-identical up to `**Proof sketch.**`.
  - Everything else is byte-identical: every definition, reader, structure and abbrev, every `variable`, `section`,
    `open` and `set_option`, every import, and the module docstrings.
  - Result: 0 differences, 0 removals and 0 order violations. The only additions are the three private helpers.
  - All nine controls pass:
    - a one-character change to a header, and to prose, each give exactly 1 difference;
    - a deleted reader gives exactly 1 removal;
    - a changed definition body gives 1 difference;
    - swapping two blocks gives order violations;
    - an edited `variable` line and a deleted import each give 1 removal;
    - an added public theorem is reported as `PUBLIC`;
    - a sketch-only edit gives 0.
  - `decls2.py` reports 0 public changes. `touched.py` reports 29 CHANGED (the targets), 3 ADDED and 52 UNCHANGED.
- **Style.**
  - Line widths are ≤ 100 (the maximum, 100, is in `Symmetric` and was there at the base). Files are ≤ 364 lines.
  - There is no `µ`, tab, trailing space, `@[simp]` or `attribute` command.
  - Every proof of 15 lines or more has a sketch and step comments, and every rewritten sketch describes the delivered
    proof.
  - The three private helpers have docstrings ("Technical glue", no tag).
- **Sources.** The source tags are identical at base and final: none was added, and no sketch carries a tag.
- **New declarations and clashes.** There are three, all `private`:
  - `halfVector_eq_zero_of_ne_last` (`Scheme:201`);
  - `decrypt_eq_decode_errorSum` (`Scheme:213`);
  - `exists_equiv_symEncrypt` (`Symmetric:110`).

  None of these names exists in `TCSlib/` or `audits/` at the base or the tip, nor in the Mathlib, Batteries or core
  sources at the pin.
- **Duplication.**
  - I searched the tip and the Mathlib/Batteries/core sources for each new declaration and each disclosed inline
    re-proof. I also looked for undisclosed ones: getD of `List.ofFn`, Bool `toNat` of `&&` and `!`, LWE sample
    equality, `Fin.snoc` away from the last index, casts of binary sums, block and column equivalences, and the
    triangle and equivalence lemmas for `acceptProb`.
  - I found **no undisclosed duplicate of a public lemma**. The disclosures are accurate (GC-01 to GC-03).
- **Axioms (my census probe).**
  - `#print axioms` gives exactly `propext`, `Classical.choice` and `Quot.sound` for all 29 targets.
  - The five modules store 114 constants. Their axiom union is the standard three, and none uses `sorryAx`.
  - A dependency trace of the 29 targets and the 3 helpers reaches no sorried constant.
  - The closure sizes equal the delivered ones; for example, `decrypt_keygen_eval` has 7627.
- **Admissions.** The census goes from 237 at the tip to 208 on the merged tree, over 1288 modules. The difference is
  exactly the 29 targets: Gadget 5, Noise 12, Scheme 6, Symmetric 2 and Eval 4. Six admissions remain, in `Columns` (2)
  and `Security` (4); these are gsw-security's.
- **Rule 10.**
  - **Seals.** I built my own seals over each file's full TCSlib import closure, from the elaborated terms plus matchers
    (`mkseals_ab`/`mkseals_coe`), and ran them with `-DmaxErrors=0`. All 20 probes pass with 0 errors in both forms,
    each with install and EOF records. They cover strict A and B and coe A and B for each of the five files.
  - **Canonical coe-A:** 0 failing declarations.
  - **Request counts (strict/coe):** Gadget 51/51, Noise 59/59, Scheme 102/101, Symmetric 107/106, Eval 154/153.
    A = B, since `PolyExpr.eval` is outside every closure.
  - **Paired controls** (my `mkctl_gsw.py`), covering the type-level definitions of plan §G8 and the definitions of
    the other owned files:
    - Coe controls, A and B: ALL_OK. Every negative fails exactly once when sealed, every positive passes, and the
      unsealed probes have rc 0.
    - Strict controls: the only difference is the expected `ctlCoeReader` failure, because strict seals the FinDist
      coercion.
    - The control runs give 180 errors in total, all inside controls.
  - **Explicit-unfold scan (Phase 1).** 0 foreign TCSlib definitions and 0 core/Mathlib definitions appear as selectors.
- **Delivered evidence.** I re-parsed it from the raw logs and it agrees with the above:
  - 20/20 final and 20/20 base seal probes have 0 errors; the probes equal the source plus the install block.
  - The controls have exactly one error per negative.
  - The delivered axiom log lists 114 constants, all standard.
  - The delivered sweep shows 35 → 6 sorries.
- **Lint.** My rerun gives 92 FAIL / 101 WARN at both base and final, with identical line sets.
- **Overlap with gsw-security.** Its checkpoint touches only `Hashing/SIS/Columns.lean`, so the files are disjoint.
- **Restore.** `dl-oleans` is back to `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`:
  - the snapshot is equal, and `restoreplan` reports 0 extra, 0 changed and 0 missing;
  - a second, independent snapshot agrees;
  - the 561 backups were restored, and the 89 new oleans and the Mathlib overlay were deleted.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| GC-01 | info, disclosed | `eval_encrypts` reads the input vertices with an inline chain for getD of `List.ofFn` (`Eval.lean:262–264`: `List.getD_eq_getElem`, `List.getElem_ofFn`). This is the DL-47 class (cf. SG-F04). The brief's F4 route prescribes exactly these two Mathlib lemmas. The nearest public generic lemma, `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), cannot be imported here. REPORT §Overlap item 9 lists the chain as reuse. | No LE. Add this site to the DL-47 ledger row, so the planned generic getD reader re-points it. |
| GC-02 | info, disclosed | Six proofs prove these Bool identities inline by `cases … <;> rfl`: `((a && c).toNat : ℤ) = a.toNat * c.toNat` and `((!c).toNat : ℤ) = 1 − c.toNat`. The proofs are `mul_le`, `nand` and `encrypts_chain` in `Noise`, and `homAnd_encrypts` and `homGate_encrypts` (twice) in `Eval`; `hb` in `Scheme` is the codepoint analogue. I confirm that no core, Batteries, Mathlib or TCSlib lemma states them. | None. A small shared lemma could be added in the cleanup; the worker offers one but does not request a promotion. |
| GC-03 | info, disclosed | `exists_equiv_symEncrypt` (private) builds the column-reindexing equivalence by hand. The REPORT says "`Matrix.reindex` and `Equiv.curry` do not give the block shape"; that slightly overstates it. A composition of Mathlib equivalences would give it: `Equiv.arrowCongr` with `rowEquiv`, `Equiv.curry` and `Equiv.piComm`. This is the pattern of `Randomized.blocksEquiv`. Its augmentation step repeats the inline `keyEquiv` of `Regev/Experiments.lean:260`, which is disclosed. | None. |
| GC-04 | info | The public sketches of `decrypt_of_encrypts` and `distAdv_symEncrypt_le` name the private glue lemmas `decrypt_eq_decode_errorSum` and `exists_equiv_symEncrypt`. The sketches are accurate, but API readers cannot see those names. | None. Rewording in an LE-doc is optional. |
| GC-05 | info (tooling), settled | `homGate_encrypts` case-splits `g : DAGGate` and `GateKind`, then reduces the `match g.kind` that appears in the published readers `homGate_eq` and `DAGGate.eval_eq`, on constructors. My probe settles how the seals treat this:<br>• `DAGGate.eval` and the statement of `eval_eq` share Lean's deduplicated matcher `BoolCircuit.instReprGateKind.repr.match_1`, which comes from the derived `Repr GateKind`.<br>• With that matcher sealed irreducible, the three reader-route reductions (`.and`, `.not`, and `.or` after `subst`) still pass.<br>• With `DAGGate.eval` also sealed, the direct `rfl` read fails exactly once and the reader route passes. Unsealed, everything passes.<br>So sealing a matcher does not block reducing a `match` on constructors, and the seals cannot see such reductions. Here the reduction goes through the reader's published statement, which is the brief's route and not a read of a definition body. The definition itself is sealed and was not read: `ctlDagEval` fails when sealed. | None on the delivery. Add a note to `maintainer/tooling-followups.md`: the "plus matchers" layer of the seals does not block matcher iota. |
| GC-06 | info | Nits in the evidence and the report:<br>• `width/final.txt` repeats the `Eval` and `Symmetric` rows.<br>• Two relative citations are off by 1–2 lines: `Regev/Basic.lean:119` should be `herr` at 121, and `Lossy/Matrix.lean:128` should be `residual_conceal` at 127.<br>• Sub-agent B's report gives 365 and 186 lines; the delivered files have 364 and 185 (B's hashes match).<br>• Sub-agent A has no `final/` copies; the hashes in its report match the delivered files. | None. |

## Proposed landing edits
None. The landing is `d4ebb0be` merged (or rebased) onto the tip. The merge is clean and touches only the five files.

## Evidence (`gsw-core-r1-evidence.zip`, under `gsw-core-r1/`)
- `PROVENANCE.txt`, `PHASE2-PLAN.txt`, `SHA256SUMS`.
- Phase 1:
  - `integrity/`, `statements/` (with `frozen-final.txt` and `frozen-controls.txt`), `style/`, `sources/`, `clash/`;
  - `rule10/` (the unfold scan and its dispositions), `lint/`;
  - `delivered-evidence-check/`, `landing/`, `tools/` (`frozen.py`, `frozen_controls.py`, `unfold_scan.py`,
    `mkctl_gsw.py`).
- Phase 2 (`p2/`):
  - Setup: `merge-tree-current-tip.txt`, `export-check.txt`, `order/`, `plan/`, `tree/` (snapshot-pre and -post,
    backup lists), `ref/`.
  - Build: `build-mathlib-extra/`, `build/` (`results.jsonl`, `per-module.tsv`, every module log), `state.json`,
    `state-out/`, `records/`, `tree-final/`.
  - Results: `admissions/`, `probe-sources/`, `probe-runs/` (census, GC-05 sealed and unsealed, collector),
    `seals/`, `seals-coe/`, `seal-runs/`, `controls/`, `controls-strict/`, `control-runs/`, `summary/`
    (`sealsum-*.tsv`, `ctlcheck*.json`/`.log`, `error-counts.tsv`, `axioms-summary.txt`).
  - Restore and scripts: `restore/`, the run scripts, and `statements/touched.json`.
- `p2-tools/`: the maintainer tools reused unmodified.

**Clear to merge**: the fill's head `d4ebb0be`, by the maintainer's landing PR.
