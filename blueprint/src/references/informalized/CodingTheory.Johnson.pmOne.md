<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: pmOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The ±1 embedding of a bit vector

**Definition.** For `x : BitVec n = Fin n → Bool`, `pmOne x : Euc n` is the
real vector whose `i`-th coordinate is `-1` when `x i = true` and `1` when
`x i = false`:

```
pmOne x = WithLp.toLp 2 (fun i => if x i then (-1 : ℝ) else (1 : ℝ))
```

`Euc n` abbreviates `EuclideanSpace ℝ (Fin n)`, so `WithLp.toLp 2` is only the
type-level move from a plain function to the `L²` structure; the values are
literally `±1`.

**Remark.** The sign convention is `true ↦ -1`, `false ↦ +1`, which is what
makes `inner_pmOne_pmOne` come out as `n - 2 * hdist x y`: coordinates where
`x` and `y` agree contribute `+1` and coordinates where they differ contribute
`-1` (`coord_mul_pmOne`).

**Used in.** The base object of the Johnson/Rankin argument: `shifted` is
`pmOne x - α • ones`, and the inner-product dictionary
(`coord_mul_pmOne`, `pmOne_apply_true`, `pmOne_apply_false`,
`inner_pmOne_pmOne`, `inner_pmOne_ones`) is stated in terms of it before
`binary_johnson_card_bound_parametric` turns Hamming data into geometry.
