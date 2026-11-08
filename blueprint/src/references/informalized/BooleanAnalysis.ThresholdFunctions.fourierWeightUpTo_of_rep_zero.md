<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Fourier.lean :: BooleanAnalysis.ThresholdFunctions.fourierWeightUpTo_of_rep_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weight of the zero threshold

**Claim.** If $f$ is represented by the identically zero polynomial, with threshold sign equal to $1$ at zero, then its Fourier weight on levels at most $k$ is $1$.

**Proof.** The zero polynomial has value $0$ at every point, so its threshold function is constantly $1$. This is exactly the character indexed by the empty set, hence $f=\chi_{\varnothing}$. By the orthogonality identity for characters, the Fourier coefficient of this function at $S$ is $1$ when $S=\varnothing$ and $0$ otherwise (`fourier_coeff_chi`). In the sum defining the weight, every term therefore vanishes except the empty-set term; that term is $1$, and the empty set has size at most $k$. Thus the sum equals $1$.

**Key facts.** `BooleanAnalysis.fourier_coeff_chi`.
