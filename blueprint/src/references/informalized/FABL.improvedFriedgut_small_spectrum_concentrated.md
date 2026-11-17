<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgut_small_spectrum_concentrated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier concentration on a small family

**Claim.** Under the stated degree concentration and positivity assumptions, the Fourier weight outside sets contained in the threshold-influential coordinates and of size at most $k$ is at most $2\epsilon$.

**Proof.** The larger-family concentration result (`improvedFriedgut_spectrum_concentrated`) bounds by $\epsilon$ the Fourier weight outside the family consisting of sets contained in the threshold-influential coordinates together with all sets of size greater than $k$. The assumed degree concentration bounds the weight of sets of size greater than $k$ by $\epsilon$: the natural-number degree version agrees with the real-indexed one (`fourierWeightAboveReal_natCast`). Any set outside the smaller family—sets both contained in the influential coordinates and of size at most $k$—must either be outside the larger family or have size greater than $k$. The weight outside the smaller family is therefore at most the sum of those two bounds, namely $2\epsilon$ (`fourierWeightOutside_improvedFriedgutSmallFamily_le_add`).

**Key facts.** `FABL.improvedFriedgut_spectrum_concentrated`, `FABL.fourierWeightAboveReal_natCast`, `FABL.fourierWeightOutside_improvedFriedgutSmallFamily_le_add`.
