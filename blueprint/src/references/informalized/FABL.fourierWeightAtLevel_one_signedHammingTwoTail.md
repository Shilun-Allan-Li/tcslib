<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.fourierWeightAtLevel_one_signedHammingTwoTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Tail Fourier Weight

**Claim.** For every real threshold $t$ and natural number $n$, the level-one Fourier weight of the signed tail function equals four times the level-one Fourier weight of the upper-tail indicator.

**Proof.** Express each level-one weight as the sum, over coordinates $i$, of the squared singleton coefficient, using the level-one expansion (`fourierWeightAtLevel_one_eq_sum_singleton`). For each coordinate, the signed-tail singleton coefficient is twice the upper-tail indicator's singleton coefficient (`fourierCoeff_signedHammingTwoTail_singleton`). Thus each squared coefficient is multiplied by $2^2=4$. Summing these equalities over all coordinates gives the claimed identity.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.fourierCoeff_signedHammingTwoTail_singleton`.
