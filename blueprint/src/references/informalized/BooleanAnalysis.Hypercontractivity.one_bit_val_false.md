<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: one_bit_val_false -->
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

**Used in.** `BooleanAnalysis.Hypercontractivity.noise_Lp_contraction_one_bit` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Tensorization.lean`; `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_one_bit`, `BooleanAnalysis.Hypercontractivity.two_point_rpow_le` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean`; `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_affine` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean`.
