<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLargestFourierCoefficient.lean :: FABL.tendsto_fourierCoeff_majority_singleton_div_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic singleton Fourier coefficient

**Claim.** For any choice of a coordinate $i(m)$ in each odd-dimensional cube of dimension $2m+1$, the singleton Fourier coefficient of majority, divided by its stated Gaussian-scale approximation, tends to $1$.

**Proof.** The singleton coefficient is independent of the chosen coordinate: the identity `fourierCoeff_majority_singleton_eq_oddMajorityInfluence` identifies it with the odd-majority influence at index $m$. The approximation in the denominator is precisely `oddMajorityInfluenceMain`. Thus the ratio in the claim is the ratio of the odd-majority influence to its main term. The established asymptotic result `tendsto_oddMajorityInfluence_div_main` says this ratio tends to $1$, proving the claim.

**Key facts.** `FABL.fourierCoeff_majority_singleton_eq_oddMajorityInfluence`, `FABL.tendsto_oddMajorityInfluence_div_main`.
