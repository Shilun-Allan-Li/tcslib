<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: chiS_symmDiff_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Shifting a character by one coordinate

**Claim.** For `S : Finset (Fin n)`, `i : Fin n` and `x : BoolCube n`,
`chiS (S ∆ {i}) x = chiS S x * boolToSign (x i)`.

**Proof.** Immediate from `rw [← chiS_mul_chiS, chiS_singleton]`: the character
multiplication law `chiS S x * chiS T x = chiS (S ∆ T) x` turns the left side
into `chiS S x * chiS {i} x`, and `chiS_singleton` evaluates the singleton
character as `boolToSign (x i)`.

A `private` restatement of `BooleanAnalysis.chiS_mul_chiS` specialised to
`T = {i}` and oriented for use as a left-to-right rewrite.

**Used in.** The `step2` block of `signEval_eq_sum_coeffs`, where the `χ_i`
factor of the branch identity is introduced.
