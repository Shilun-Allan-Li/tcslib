<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: one_bit_val_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Value of a one-bit function at `false`

**Claim.** For `f : BooleanFunc 1`,

```
f (fun _ => false) = fourierCoeff f ∅ + fourierCoeff f {0}
```

i.e. writing `a = f̂(∅)` and `b = f̂({0})`, the one-bit function takes the value
`a + b` at the point `false`.

**Proof.**

1. Replace the left-hand side by its Fourier expansion,
   `conv_lhs => rw [walsh_expansion f]`, giving
   `∑ S : Finset (Fin 1), f̂(S) · χ_S(false)`.
2. Rewrite the index set as the pair `{∅, {0}}` (`finsetFin1_univ`) and split the
   sum with `Finset.sum_pair finsetFin1_ne`.
3. `simp [chiS, boolToSign]` evaluates the two characters at `false`:
   `χ_∅(false) = 1` (empty product) and `χ_{0}(false) = boolToSign false = 1`.
   Both coefficients therefore appear with sign `+`. ∎

**Used in.** With `one_bit_val_true`, it is the coordinate dictionary for the
one-bit case: `expect_abs_rpow_one_bit` uses the pair to turn `𝔼[|f|^p]` into
`(|a+b|^p + |a−b|^p)/2`, and `Hypercontractivity/General.lean` reuses it when
feeding a two-variable inequality with `f̂(∅)`, `f̂({0})`.
