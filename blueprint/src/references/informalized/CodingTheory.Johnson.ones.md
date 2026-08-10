<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: ones -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The all-ones vector

**Definition.** `ones : Euc n` is the constant vector all of whose coordinates
equal `1`:

```
ones = WithLp.toLp 2 (fun _ => (1 : ℝ))
```

with `Euc n = EuclideanSpace ℝ (Fin n)`; `WithLp.toLp 2` only transports the
constant function into the `L²` type.

**Remark.** A plain constant, recorded as a named definition so that the shift
direction in `shifted α x = pmOne x - α • ones` has a name and so that the
`@[simp]` lemma `ones_apply` can evaluate its coordinates. Its self inner
product is `n` (`inner_ones_ones`), which is where the `α^2 * n` term of the
Rankin inequality comes from.

**Used in.** `shifted`, `inner_ones_ones`, `inner_pmOne_ones`, and hence the
expansion `inner_shifted_expand` used by
`binary_johnson_card_bound_parametric`.
