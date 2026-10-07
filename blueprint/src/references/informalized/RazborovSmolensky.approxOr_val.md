<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOr_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Value-level form of the OR-approximator

**Definition.** For a vector `v : Fin width → ZMod p` and a seed
`S : Fin ℓ → Finset (Fin width)`,

`approxOr_val p v S = 1 - ∏ k, (1 - (∑ i ∈ S k, v i) ^ (p - 1))`.

This is `approxOr` with scalars in place of polynomials: the same expression
evaluated in the field `ZMod p` rather than in `MvPolynomial (Fin vars) (ZMod p)`.
Unlike `approxOr` it is a plain (computable) definition.

**Remark.** The split exists so that the counting arguments — which are about
seeds, not about polynomials — can be run entirely at the value level. The bridge
is `approxOr_eval_eq`: evaluating `approxOr` at a point `y` gives
`approxOr_val` of the evaluated coefficients. The companion `OR_val` is the
exact OR detector `1 - ∏ k, (1 - v k ^ (p - 1))`, and `approxOr_failure_iff`
characterizes precisely when the two disagree.

**Used in.** `approxOr_eval_eq`, `approxOr_failure_iff`, and the seed-counting
lemmas `count_bad_S` and `count_bad_S_or`.
