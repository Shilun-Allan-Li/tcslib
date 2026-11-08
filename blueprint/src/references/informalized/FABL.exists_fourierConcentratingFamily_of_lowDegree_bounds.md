<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.exists_fourierConcentratingFamily_of_lowDegree_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A concentrating family from low-degree bounds

**Claim.** Given the stated Fourier tail and low-degree coefficient bounds, there is a finite family of coordinate sets outside which the Fourier weight is at most $\epsilon$, and whose size is at most $4L^2/\epsilon$.

**Proof.** Choose the low-degree $L^1$-concentrating family associated with $f$, $k$, and $\epsilon$. The low-degree $L^1$ concentration result shows that the Fourier weight outside this family is at most $\epsilon$, provided the Fourier weight above degree $k$ is at most $\epsilon/4$. The given tail bound has exactly this form after identifying the real-threshold version with the natural-degree version. For the size estimate, the family cardinality bound gives at most $4/\epsilon$ times the square of the Fourier $1$-norm of the degree-$k$ part. The identity expressing that norm as the sum of the absolute values of the coefficients on sets of size at most $k$ lets us apply the assumed bound by $L$, yielding $4L^2/\epsilon$.

**Key facts.** `FABL.isFourierSpectrumConcentratedOn_lowDegreeL1ConcentratingFourierFamily`, `FABL.fourierWeightAboveReal_natCast`, `FABL.card_lowDegreeL1ConcentratingFourierFamily_le`, `FABL.fourierOneNorm_lowDegreePart`.
