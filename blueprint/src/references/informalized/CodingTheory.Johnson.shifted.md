<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: shifted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The α-shifted ±1 vector of a codeword

**Definition.** For `α : ℝ` and `x : BitVec n`,

```
shifted α x = pmOne x - α • ones   :   Euc n
```

i.e. the `±1` embedding of `x` translated by `α` in the all-ones direction; in
coordinates, `shifted α x i = (if x i then -1 else 1) - α`.

**Remark.** `α` is the free parameter of the Johnson/Rankin argument: shifting
by `α • ones` trades weight information against distance information, since
bilinear expansion (`inner_shifted_expand`) gives

```
⟪shifted α x, shifted α y⟫ = (n - 2·hdist x y) - α(n - 2·wt x) - α(n - 2·wt y) + α²n
```

so a good choice of `α` (namely `alpha n d`) forces all pairwise inner products
of a code to be `≤ 0` (`inner_shifted_le_expr`).

**Used in.** `binary_johnson_card_bound_parametric`, which sets
`u x = shifted α x` and applies `rankin_finset_bound` to the normalized family
`normalize (u x)`; `shifted_ne_zero_of_alpha_lt_one` supplies the required
nonvanishing when `α < 1`.
