<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: composedDelta_step_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Factoring the composed parameter as the (d−1) case times 1/(40l)

**Claim.** For `w : ℕ`, `l : ℝ`, `d : ℕ` with `3 ≤ d` (and an unused
`0 < l`),
`composedDelta w l d = composedDelta w l (d - 1) * (1 / (40 * l))`.
Both sides are `(1/(40w)) * (1/(40l))^(d-2)`; the width factor is untouched and
one copy of `1 / (40 * l)` is peeled off the right.

**Proof.**

1. `rcases d with (_ | _ | d)` then `norm_num [composedDelta] at *`: the cases
   `d = 0, 1` contradict `3 ≤ d`.
2. `cases d` splits the exponent-`0` case from the general one, and
   `simp_all +decide [pow_succ']` followed by `ring` matches
   `(1/(40l))^(k+1) = (1/(40l))^k * (1/(40l))`. ∎

**Used in.** `circuit_reduction_ind_step`, where it is exactly the algebraic
identity that licenses the two-stage argument: stage 1 runs at
`composedDelta w l (d-1)` (the inductive hypothesis on the children) and stage 2
at `1 / (40 * l)` (the switching lemma on the compressed width-`l` formula), and
their product is the parameter in the goal.
