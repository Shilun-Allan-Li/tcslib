<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: signEval_eq_sum_coeffs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The coefficient recursion really is a character expansion

**Claim.** For every `T : DecisionTree n` and every `x : BoolCube n`,
`T.signEval x = ∑_{S : Finset (Fin n)} T.coeffs S * chiS S x`. That is, the
recursively defined `coeffs` gives a pointwise character representation of the
±1-encoded tree function.

**Proof.** `induction T`.

1. **Leaf `b`.** `simp [signEval, DecisionTree.eval, coeffs, ite_mul,
   Finset.sum_ite_eq', chiS_empty]`: the `if S = ∅` in `coeffs` collapses the
   sum to its `S = ∅` term, and `chiS ∅ x = 1`.
2. **Branch `i lo hi`.** The work is one `have expand`, rewriting the sum of
   branch coefficients as `(A + B)/2 + (A − B)/2 * boolToSign (x i)` where
   `A`, `B` are the corresponding sums for `lo`, `hi`. It is assembled from
   four sub-facts:
   - `step1` unfolds `coeffs` and splits the sum in two along the recursion
     (`Finset.sum_add_distrib`, `Finset.sum_congr`, `ring`);
   - `step2` handles the shifted block: `sum_symmDiff_reindex` replaces
     `S ∆ {i}` by `S`, `chiS_symmDiff_singleton` produces the `χ_i` factor, and
     `cases x i <;> simp [boolToSign]` discharges the resulting sign square;
   - `hA` and `hB` pull the `/2` and the `boolToSign (x i)` outside the sums
     (`Finset.sum_div`, `Finset.sum_mul`, `Finset.sum_add_distrib`,
     `Finset.sum_sub_distrib`).
3. `rw [expand, ← ih_lo, ← ih_hi]` replaces `A` and `B` by `lo.signEval x` and
   `hi.signEval x`, and after `simp only [signEval, DecisionTree.eval]` the
   goal is a two-case identity in the queried bit, closed by
   `cases hxi : x i <;> simp [boolToSign] <;> ring` — the `(f_lo + f_hi)/2 ±
   (f_lo − f_hi)/2` selector.

**Used in.** `fourierCoeff_signEval`, where it is `funext`-ed into a function
equality and then hit with `fourierCoeff_sum_chiS`.
