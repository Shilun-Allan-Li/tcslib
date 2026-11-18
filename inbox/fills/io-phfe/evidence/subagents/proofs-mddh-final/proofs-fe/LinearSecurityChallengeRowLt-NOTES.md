# LinearSecurity.challengeRow_lt

Scratch-only exact frozen-header replacement. The original theorem was still admitted in
live LinearSecurity/Theorems.lean:95. Its M0 prose, sketch, binders and conclusion were copied
verbatim. The fragment contains exactly one tactic block, no admissions, no new helper and
no new import. No Lean, lake, build, Git or live source edit was performed; native check
pending.

## Argument / reuse

Read multiplication of dimension polynomials through PolyExpr.eval_mul. The declared raw
PG.mCount_le_mBound field bounds the actual mCoord finite node index by the padded maximum.
Form the corresponding STANDARD `Fin(mBound) × Fin(q)` pair and read the bound of its image
under Mathlib's existing finProdFinEquiv. That image's value is j+q*node; only addition and
multiplication commutativity are required to match the frozen node*q+j row formula.
This consumes the canonical product-index bound and does not rederive its arithmetic.
No q>0 or mBound>0 premise is added: the existing j and u assumptions already support the
required finite indices, including vacuous zero-size cases.

## Actual static searches

- `rg --files TCSlib | rg '/LinearSecurity/(Theorems|Advice|Data|Widths)\.lean$'` located
  AdvancedEncryption/FunctionalEncryption/Wee20/LinearSecurity/{Theorems,Data}. Initial
  guessed paths without AdvancedEncryption failed, as did a zsh unmatched PolyExpr glob.
- Read the full live LinearSecurity/Theorems.lean to confirm challengeRow_lt remains the
  requested existing admission, and read Reductions:194-242 for the actual challengeR and
  challengeUhat row layouts. Both are precisely node*q+j and share the same padded bound.
- Read PartialGarbling/Defs:226-250 for mCoord:243 and mCount_le_mBound:239.
- `rg -n 'eval_mul|mul_eval|mul_add_lt_mul|add_mul_lt|mul_add.*lt|lt_mul_add'` over the corrected
  Complexity/Randomized/PolyExpr path and Mathlib Nat/Fin sources. The exact polynomial
  reader is PolyExpr.eval_mul:125. No published generic Nat.mul_add_lt_mul theorem was found.
- `rg -n 'finProdFinEquiv.*(val|apply)|finProdFinEquiv|Nat.mul_add_lt_mul'` in Mathlib's
  Logic/Equiv/Fin sources and the existing reduction file. Read Fin/Basic:315-344: the
  standard finProdFinEquiv:325 already supplies the needed index bound. Its value formula
  is x.2+n*x.1, so the proof uses a permitted Mathlib `change` on this coordinate value,
  never places the definition into a simp/rw/unfold list.
- Read PartialGarbling/Defs imports:1-21. Mathlib.Logic.Equiv.Fin.Basic is already imported,
  and the same file already consumes finProdFinEquiv at377, so no new root/import is needed.
- Confirmed PolyExpr.eval_mul's exact header at Complexity/Randomized/PolyExpr:108-130.

Only the published polynomial reader occurs in rw. The final simp list contains the
standard Nat.add_comm and Nat.mul_comm equation theorems. Structure fields and Fin.isLt
are direct public projections, and the finite-coordinate conversion uses existing
Mathlib machinery rather than a new representation or helper.

Proof body:10 lines, maximum71 columns. Parent should native-check this single replacement;
no successful elaboration, seal or standard-only chain is claimed by the draft.
