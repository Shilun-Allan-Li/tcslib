<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.FiniteTensorization.norm_tensorization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tensorization of Norm Contractions

**Claim.** If each coordinate operator satisfies the stated weighted $p$-to-$q$ norm bound, then the product operator satisfies the corresponding product-space norm bound.

**Proof.** The proof uses duality and tensorizes a bilinear pairing estimate. Put $r=q/(q-1)$, the Hölder conjugate of $q$. To bound the output weighted $q$-norm, apply the dual characterization of that norm (`FiniteNorms.norm_le_of_pairing`): it suffices to bound its pairing against every test function $g$ by the proposed input norm times the weighted $r$-norm of $g$. Expand the product operator in the pairing and interchange the finite sums. Apply the pairing tensorization result (`pair_tensorization`) to the coordinate kernels $w_i(y)k_i(y,x)$, with exponents $p,r$. For each coordinate, the required pairing estimate follows by weighted Hölder: apply it to the coordinate output on the first function and the test function on the second, then use the assumed coordinate norm contraction on the first factor. The nonnegativity hypotheses ensure the weights and the powered sums used in these comparisons are nonnegative. The resulting product pairing bound is exactly the dual estimate, and hence gives the asserted norm contraction.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteNorms.norm_le_of_pairing`, `BooleanAnalysis.Hypercontractivity.FiniteTensorization.pair_tensorization`, `BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_holder`.
