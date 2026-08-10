<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: sum_abs_coeffs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The spectral 1-norm is at most the number of leaves

**Claim.** For every `T : DecisionTree n`,
`∑_{S : Finset (Fin n)} |T.coeffs S| ≤ (T.size : ℝ)`, where `T.size` counts the
leaves of `T`.

**Proof.** `induction T`.

1. **Leaf `b`.** A `have habs` shows `|coeffs (.leaf b) S| = if S = ∅ then 1
   else 0` by `simp only [coeffs]; split_ifs <;> cases b <;> simp [boolToSign]`
   (both signs have absolute value 1). Rewriting with it and
   `simp [size, Finset.sum_ite_eq']` gives `1 ≤ 1`.
2. **Branch `i lo hi`, per-frequency bound.** A `have hbound` gives, for each
   `S`, the triangle-inequality estimate
   `|coeffs (.branch i lo hi) S| ≤ (|lo.coeffs S| + |hi.coeffs S|)/2
   + (|lo.coeffs (S ∆ {i})| + |hi.coeffs (S ∆ {i})|)/2`. It is proved by
   `rw [abs_le]` and `constructor <;> linarith`, fed by the eight bounds
   `le_abs_self` / `neg_abs_le` on the four coefficients involved.
3. **Branch, summation.** A `calc` chain: `Finset.sum_le_sum` applies `hbound`
   termwise; `Finset.sum_add_distrib` separates the shifted and unshifted
   blocks; `sum_symmDiff_reindex` shows the shifted block equals the unshifted
   one; `← Finset.sum_div`, `Finset.sum_add_distrib` and `ring` collapse the two
   halves into `∑ |lo.coeffs S| + ∑ |hi.coeffs S|`.
4. `add_le_add ih_lo ih_hi` bounds this by `lo.size + hi.size`, which is
   `(.branch i lo hi).size` by `simp [size]`.

**Remark.** The reindexing step is what makes the bound additive rather than
lossy: averaging and differencing each contribute half of the same total mass.

**Used in.** `spectral_one_norm_le` (O'Donnell Proposition 3.16, 1-norm bound),
and through it `sparsity_le`.
