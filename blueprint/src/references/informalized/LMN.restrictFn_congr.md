<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: restrictFn_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restriction respects pointwise equality of functions

**Claim.** For `f g : (Fin n → Bool) → Bool` and a restriction `ρ : Restriction n`,
if `f x = g x` for every `x` then `restrictFn f ρ x = restrictFn g ρ x` for every
`x`.

**Proof.** Immediate from `unfold restrictFn; aesop`: by definition
`restrictFn f ρ x = f (ρ.extend x)`, so the hypothesis applied at the point
`ρ.extend x` closes the goal.

**Remark.** Deliberately granular helper. Note the conclusion is stated
pointwise (`∀ x, … = …`) rather than as an equality of functions, so it composes
directly with `dtDepth_congr`, which consumes a pointwise hypothesis.

**Used in.** `switching_bernoulli_dtDepth_function` and
`depth3_second_stage_bound`, always paired with `dtDepth_congr` (and, in the
latter, `restrictFn_composeRestr`).
