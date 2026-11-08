<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.fourierWeightOutside_theorem9_28SmallFamily_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-family exterior weight bound

**Claim.** The Fourier weight outside the small threshold family is at most the exterior weight outside the threshold family that also excludes all sets of size greater than $k$, plus the total Fourier weight on sets of size greater than $k$.

**Proof.** Combine the two sums on the right and compare their summands with those on the left, separately for each set $S$. Write $J$ for the coordinates whose Boolean influence is at least the specified threshold. If $S\subseteq J$ and $|S|\le k$, then $S$ lies in the small family and contributes zero to the left; it also lies in the larger threshold family and contributes zero to its exterior sum, and it is not high degree. If $S\subseteq J$ but $|S|>k$, it is outside the small family, so its squared coefficient contributes on the left; it lies in the larger family through the high-degree clause and hence contributes zero to that family's exterior sum, while its weight appears in the high-degree sum. If $S\not\subseteq J$ and $|S|\le k$, it is outside both families, so its weight appears equally in the left sum and the first right-hand sum. If $S\not\subseteq J$ and $|S|>k$, it contributes on the left and in the high-degree sum on the right (and also in the first right-hand sum). Thus each left summand is bounded by the combined right summands, and summing gives the result.
