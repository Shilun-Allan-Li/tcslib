<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: exactAnd_on_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Fermat AND-product computes AND exactly on bits

**Claim.** Let `inputs : Fin width → ZMod p` take values in `{0, 1}`. Then

`∏ i, (1 - (1 - inputs i) ^ (p - 1)) = ((∏ i, bitify p (inputs i) : Fin 2) : ℕ)`

in `ZMod p`: the product of the per-input Fermat indicators of "`inputs i ≠ 0`" equals the
Boolean AND of the corresponding bits.

**Proof.** Case split on whether some input vanishes, `by_cases hzero : ∃ i, inputs i = 0`.

- **Some `inputs i = 0`.** Both sides are `0`. On the left, `Finset.mul_prod_erase` pulls
  the `i`-th factor out and `simp [hi]` shows it is `1 - (1 - 0) ^ (p - 1) = 0`. On the
  right, the same rewrite plus `simp [hi, bitify]` shows the `Fin 2` product has factor
  `bitify p 0 = 0`, so the product is `0` and its `ℕ`-cast is `0`.
- **No input vanishes.** Then `hall : ∀ i, inputs i = 1` by discharging the `0` disjunct of
  `hinputs i` against `hzero`. With `hp1 : p - 1 ≠ 0` (from `1 < p`, `omega`), the left
  side is `∏ i, (1 - 0 ^ (p - 1)) = 1` by `simp [hall, hp1]` and the right side is
  `∏ i, (1 : Fin 2) = 1` by `simp [hall, bitify]`.

**Remark.** `hp1` is what rules out `p = 1`: without `p - 1 ≠ 0` the factor
`1 - (1 - 1) ^ (p - 1)` would be `1 - 0 ^ 0 = 0`, not `1`.

**Used in.** The correctness obligation of the AND branch of `exists_poly_for_gate`
(rewriting the gate's target into the shape `approxAnd_pointwise_bad_count` expects), and
the same branch in `RazborovSmolensky/CircuitDegree.lean:450`.
