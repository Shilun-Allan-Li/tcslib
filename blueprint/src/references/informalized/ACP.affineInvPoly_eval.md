<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: affineInvPoly_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating the affine inverse polynomial

**Claim.** For a field `K`, `ω : K`, `i : Fin n`, and any point `x : Fin n → K`,

`(affineInvPoly ω i).eval x = 1 + ω⁻¹ - ω⁻¹ * x i`.

**Proof.** Immediate from `simp [affineInvPoly, sub_eq_add_neg, mul_comm]`:
unfolding the definition gives `(1 + ω⁻¹) + (-ω⁻¹) * x i`, and
`sub_eq_add_neg`/`mul_comm` normalize that to the stated subtraction form.

**Remark.** A `@[simp]` lemma, so downstream evaluations of the substitution are
rewritten automatically; it is the only interface most callers need to
`affineInvPoly`.
