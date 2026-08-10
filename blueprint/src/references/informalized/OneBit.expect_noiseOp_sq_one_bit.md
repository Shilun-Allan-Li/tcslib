<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: expect_noiseOp_sq_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Second moment of the noise operator on one bit

**Claim.** For `ρ : ℝ` and `f : BooleanFunc 1`,

```
expect (fun x => (noiseOp ρ f x) ^ 2) = f̂(∅) ^ 2 + ρ ^ 2 * f̂({0}) ^ 2
```

That is, `𝔼[(T_ρ f)²] = a² + ρ²b²` with `a = fourierCoeff f ∅`,
`b = fourierCoeff f {0}`.

**Proof.**

1. Recognise the second moment as an inner product:
   `𝔼[(T_ρ f)²] = innerProduct (T_ρ f) (T_ρ f)`, proved inline by
   `unfold innerProduct; congr 1; ext x; ring`.
2. `parseval (noiseOp ρ f)` turns it into `∑ S, (T_ρ f)̂(S) ^ 2`.
3. `simp only [noiseOp_fourier]` replaces each coefficient by `ρ ^ |S| · f̂(S)`.
4. `finsetFin1_univ` rewrites the index set to `{∅, {0}}` and
   `Finset.sum_pair finsetFin1_ne` splits the sum; `simp [Finset.card_empty]`
   evaluates `ρ ^ 0 = 1` and `ρ ^ 1 = ρ`, and `ring` collects the result. ∎

**Used in.** `one_bit_p2_hypercontractivity`, where it is the `h1` rewrite that
converts the left-hand side of the one-bit `(p,2)` hypercontractive inequality
into the algebraic quantity `a² + ρ²b²` handled by `two_point_ineq`.
