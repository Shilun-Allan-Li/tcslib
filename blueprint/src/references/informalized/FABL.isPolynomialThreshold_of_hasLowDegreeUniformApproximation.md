<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.isPolynomialThreshold_of_hasLowDegreeUniformApproximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree approximation gives a threshold

**Claim.** If a Boolean function has a uniform approximation within $1/2$ by a function whose Fourier coefficients vanish above the stated cutoff, then it has a polynomial threshold representation of Fourier degree at most that cutoff.

**Proof.** Choose an approximating function $q$ witnessing the assumed approximation. At each input, the Boolean value is either $+1$ or $-1$. If it is $+1$, the strict error bound $|1-q(x)|<1/2$ forces $q(x)>0$, so its threshold sign is $+1$. If the Boolean value is $-1$, the bound $|-1-q(x)|<1/2$ forces $q(x)<0$, so its threshold sign is $-1$. Thus $q$ represents the Boolean function by thresholding. Finally, every coordinate set with size greater than the cutoff lies outside the prescribed low-degree family, so the approximation hypothesis makes the corresponding Fourier coefficient of $q$ vanish. The Fourier-degree criterion (FABL.fourierDegree_le_iff) now gives the required degree bound.

**Key facts.** `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`, `FABL.fourierDegree_le_iff`.
