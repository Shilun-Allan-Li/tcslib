# gsw-core · maintainer delivery review (r1)

**Verdict (interim, Phase 1 of 2): ACCEPT, pending the Phase 2 Lean checks.** Phase 1 (integrity,
statements, scope, style, duplication, sources, Rule 10 by source reading, the delivered evidence and the
landing merge) finds 0 blockers, 0 majors and 0 minors; six info findings, none needing a landing edit. No LE
edit is proposed. Phase 2 (native module checks on the merged tree, axioms, the maintainer's canonical seals,
tree restore) waits for the olean tree the maintainer names; the verdict becomes final only after it.

## Delivery and landing
- **Delivery:** Claude, a lead with two sub-agents (A: F1, F2 in `Gadget`, `Noise`; B: F3, F7 in `Scheme`,
  `Symmetric`; the lead: F4 in `Eval`, integration, every commit and the final checks). The final is exchange
  `9e52a5019258c51d67b1f28d3675c66cf787209b`; the checkpoint is `5b72e346bd5484fb059cbaadd836de88f4adf0a2`.
  Both exchange commits touch only `inbox/fills/gsw-core/`. The issue base is
  `486f44f8414c20a2d21e452c44de8b8c8d8513a0` (#333's head, with #332 as an ancestor).
- **Head:** `d4ebb0be088e5985337ccb4e0a61cb3a662e8b73`, three commits: `243a44cd` (F1, F2), `a1bc6aac` (F4,
  `decrypt_keygen_eval` proved modulo F3 at that point) and `d4ebb0be` (F3, F7). The checkpoint carried the
  first two, with the same hashes.
- **Files:** the five owned files only, +542/−89: `Gadget` 204 → 236, `Noise` 235 → 321, `Scheme` 215 → 364,
  `Symmetric` 111 → 185, `Eval` 209 → 321 lines. No import added; no frozen file, helper module or facade
  touched; no scope request.
- **Landing:** the base is now an ancestor of the records tip `d00079418c3b0bc8341a62542a98da4b5f73a5d9`
  (#332 and #333 merged). `git merge-tree` of the tip and `d4ebb0be` is clean (tree `38858c09`) and differs from
  the tip only in the five files, each equal to the delivered one. Between the base and the tip, two modules of
  the issued order changed, both additively: `DAGCircuit` (+`isFaninTwo_iff`) and `Randomized/Classes`
  (+`inBPP_iff`); neither name clashes with the fill.
- **Evidence:** `$SP/dl-review/gsw-core-r1/` (Phase 1); the ZIP and its SHA-256 are made at the end of Phase 2.

## Checks (Phase 1)
- **Integrity.** The top-level manifest verifies 544/544 and its path set equals the delivered files exactly (no
  `./`); `evidence/SHA256SUMS` verifies 533/533, path set exact (534 files with the manifest). `git am` at the
  base with the recorded identities and dates reproduces all three hashes, unsigned (`signing` = `none`); the
  five files equal `src/` byte for byte.
- **Statements (maintainer script, independent of the delivery's).** Every base item of the five files
  reappears in order. The 29 targets keep their headers byte-identical and their docstrings byte-identical up to
  `**Proof sketch.**`; every other declaration (definitions, readers, structure, abbrevs), every `variable`,
  `section`, `open`, `set_option`, import and module docstring is byte-identical. Result: 0 differences,
  0 removals, 0 order violations; additions are exactly the three private helpers. Nine controls pass: a
  one-character header change and a one-character prose change each give exactly 1 difference, a deleted reader
  exactly 1 removal, a definition-body change 1 difference, a block swap order violations, an edited `variable`
  line and a deleted import 1 removal each, an added public theorem is reported `PUBLIC`, and a sketch-only edit
  gives 0. `decls2.py` reports 0 ADDED/CHANGED/REMOVED public declarations.
- **Style.** Widths ≤ 100 (max 100, `Symmetric`, as at the base); files ≤ 364 lines; no `µ`, tab, trailing space
  or `@[simp]`/`attribute`. Every proof of 15 lines or more has a sketch and step comments; every rewritten sketch
  describes the delivered proof; the three private helpers have docstrings ("Technical glue", no tag).
- **Sources.** Source tags per file are identical at base and final (0 new); sketches carry no tag. No fabricated
  excerpt or location.
- **New declarations and clashes.** Three, all `private`: `halfVector_eq_zero_of_ne_last` (`Scheme:201`),
  `decrypt_eq_decode_errorSum` (`Scheme:213`), `exists_equiv_symEncrypt` (`Symmetric:110`). None is declared in
  `TCSlib/` or `audits/` at the base or the tip, nor in the Mathlib, Batteries or core sources at the pin.
- **Duplication.** I searched the tip and the Mathlib/Batteries/core sources for each new declaration and each
  disclosed inline re-proof, and for undisclosed ones (getD/`List.ofFn`, Bool `toNat` of `&&`/`!`, LWE sample
  equality, `Fin.snoc` off the last index, binary-sum casts, block/column equivalences, triangle and
  equivalence lemmas for `acceptProb`). I found **no undisclosed duplicate of a public lemma**. The disclosures
  are accurate (cited lines are off by 1–2 in two places, GC-06). Details in GC-01–GC-03.
- **Rule 10 (source reading).** My explicit-unfold scan of every `simp`/`rw`/`dsimp`/`unfold`/`delta` selector
  (325 tokens) finds 0 foreign TCSlib definitions and 0 core/Batteries/Mathlib definitions; the non-lemma rows
  are local hypotheses or `@[to_additive]` lemmas (dispositions recorded). The 11 `change` steps reduce only
  Mathlib `vecMul`/`mulVec`/`dotProduct`/`transpose`/`submatrix` and the file's own definitions; foreign
  definitions (`lift`, `Regev.augmented`, `decryptColumn`) stay folded and are read by their readers. The owned
  files read each other only through readers (`encrypts_iff`, `mul_eq`, `nand_eq`, `chain_*`, `gadget_apply`,
  `lift_apply`, `decompose_apply`, `decomposeVec_eq`, `secretVector_eq`, `halfVector_eq`, `decryptColumn_eq`,
  `decrypt_eq`, `encrypt_eq`, `symEncrypt_apply`, `homAnd_*`, `homGate_eq`, …).
- **Delivered seal, axiom and admission evidence (re-parsed from the raw logs).**
  - Seals: 20/20 final and 20/20 base probes are byte-equal to the source plus the install block, which is
    identical to the derand harness's (log prefix aside); all exit 0 with 0 errors in both forms, one install line
    and one EOF marker each; A = B (no `PolyExpr` in the closures). Canonical coe-A: 0 failing declarations.
  - Controls: unsealed 0 errors; sealed coe 8 errors, strict 9, exactly one per NEG (8, including the five
    type-level definitions of plan §G8) plus the COE in strict; POS pass.
  - Axioms: 114 constants, all standard; the 29 targets and the 3 helpers use only `propext`,
    `Classical.choice`, `Quot.sound`; the trace lists no sorried constant; 0 error lines.
  - Admissions: the raw base bootstrap logs show 35 sorry warnings; the final sweep shows 6, exactly
    `gsw-security`'s (`Columns` 2, `Security` 4); the five owned modules show 0. 31/31 sweep modules exit 0 with
    0 errors.
- **Lint.** My rerun at base and final: 92 FAIL / 101 WARN over 364 files at both, identical FAIL/WARN line sets,
  identical to the delivered logs; the GSW files have no FAIL/WARN line.
- **Overlap with gsw-security.** Its checkpoint touches only `Hashing/SIS/Columns.lean`; disjoint files.

## Checks (Phase 2): PENDING
To run on the merge of the tip and `d4ebb0be` once the maintainer names an olean tree: per-module native checks
of the five owned modules and their downstream (`Security`, the GSW, Homomorphic and AdvancedEncryption
facades, root `TCSlib` if the tree allows); axioms of all 29 targets with a dependency trace; the maintainer's
canonical seals (coe-A canonical; strict and coe, A and B; paired controls; `-DmaxErrors=0`; both error forms)
on the five files; restore of the tree to its base snapshot with proof.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| GC-01 | info, disclosed | `eval_encrypts` reads the input vertices with an inline getD-of-`List.ofFn` chain (`Eval.lean:262–264`: `List.getD_eq_getElem`, `List.getElem_ofFn`), the DL-47 class (cf. SG-F04). The brief's F4 route prescribes exactly these two Mathlib lemmas; the nearest public generic form, `GI.getD_ofFn_lt'` (`ZeroKnowledge/GraphIsomorphism/SoundnessRep.lean:61`), is not importable here. REPORT §Overlap item 9 lists it as reuse. | No LE. Extend the DL-47 row with this site so the planned generic getD reader re-points it. |
| GC-02 | info, disclosed | The Bool identities `((a && c).toNat : ℤ) = a.toNat * c.toNat` and `((!c).toNat : ℤ) = 1 − c.toNat` are proved inline by `cases … <;> rfl` in six proofs (`Noise`: `mul_le`, `nand`, `encrypts_chain`; `Eval`: `homAnd_encrypts`, `homGate_encrypts` twice; `Scheme`'s `hb` is the codepoint analogue). I confirm no core, Batteries, Mathlib or TCSlib lemma states them. | None. Optional small shared lemma in the cleanup (the worker offers it; no promotion requested). |
| GC-03 | info, disclosed | `exists_equiv_symEncrypt` (private) hand-builds the column reindexing equivalence. The REPORT's "`Matrix.reindex` and `Equiv.curry` do not give the block shape" is slightly overstated: a composition of Mathlib equivalences (`Equiv.arrowCongr` with `rowEquiv`, `Equiv.curry`, `Equiv.piComm`) would. Its augmentation step repeats the inline `keyEquiv` of `Regev/Experiments.lean:260` (disclosed). | None. |
| GC-04 | info | The public sketches of `decrypt_of_encrypts` and `distAdv_symEncrypt_le` name the private glue lemmas `decrypt_eq_decode_errorSum` and `exists_equiv_symEncrypt`. Accurate, but those names are not visible to API readers. | None (optional LE-doc wording). |
| GC-05 | info (tooling) | `homGate_encrypts` case-splits `g : DAGGate` and `GateKind` and reduces the `match g.kind` of the published readers `homGate_eq`/`DAGGate.eval_eq` on constructors. This is the brief's route, not a definition read. The seal catalog has no `DAGGate.eval.match_*` constant (Lean reuses an equivalent matcher), and the Eval seal passes with every TCSlib matcher sealed, which suggests sealed matchers do not block such iota reductions. | None on the delivery. Phase 2 probe to confirm; then a note for `maintainer/tooling-followups.md`. |
| GC-06 | info | Evidence and report nits: `width/final.txt` repeats the `Eval` and `Symmetric` rows; two relative cites are off by 1–2 lines (`Regev/Basic.lean:119` → `herr` at 121; `Lossy/Matrix.lean:128` → `residual_conceal` at 127); sub-agent B's report gives 365/186 lines for the files that are 364/185 delivered (its hashes match); sub-agent A has no `final/` copies (its report's hashes match the delivered files). | None. |

## Proposed landing edits
None.

## Evidence (Phase 1, `$SP/dl-review/gsw-core-r1/`)
- `PROVENANCE.txt`, `PHASE2-PLAN.txt`.
- `integrity/`: both manifest checks and exact path sets; `git-am-replay.log`; `files-vs-src.log`.
- `statements/`: base and final copies; `frozen-final.txt`; `frozen-controls.txt` and the mutated copies;
  `decls2.txt` with its note.
- `style/`: `width-size.txt`, `sketch-rule.txt`. `sources/tags.txt`. `clash/clash-scan.txt`.
- `rule10/`: `unfold-scan-final.txt`, `unfold-scan-dispositions.txt`.
- `lint/`: base and final logs, diff, comparison with the delivered logs.
- `delivered-evidence-check/`: error counts in both forms over every delivered log, sorry recount, axiom
  re-parse, seal probes versus source, install block versus the derand harness, cited-path presence.
- `landing/`: `merge-tree.txt`, `upstream-changes.txt`.
- `tools/`: `frozen.py`, `frozen_controls.py`, `unfold_scan.py` (`python3 -I`).

**Not yet clear to merge — Phase 2 (Lean checks on the merged tree) pending the maintainer's olean tree.**
