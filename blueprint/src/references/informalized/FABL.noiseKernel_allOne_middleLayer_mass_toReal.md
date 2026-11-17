<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.noiseKernel_allOne_middleLayer_mass_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Mass on the Middle Layer

**Claim.** If $y$ has exactly $m$ positive coordinates among its $2m$ coordinates, then the noise kernel from the all-positive vector assigns $y$ mass whose real value is $\left(\frac{1+\rho}{2}\right)^m\left(\frac{1-\rho}{2}\right)^m$.

**Proof.** The hypothesis says that exactly $m$ coordinates of $y$ are positive. The middle-layer characterization identifies the middle-layer indicator condition with having exactly $m$ negative coordinates (`middleLayerIndicator_eq_one_iff_negative_count`); since each coordinate is either $1$ or $-1$ and there are $2m$ coordinates, the remaining $m$ coordinates are negative. The independent product formula expresses the kernel's mass at $y$ as the product of its coordinate masses (`independentProductPMF_apply`). From the all-positive input, a positive output coordinate has real mass $(1+\rho)/2$, and a negative output coordinate has real mass $(1-\rho)/2$ (`coordinateNoisePMF_one_toReal`). Multiplying these contributions over the $m$ positive and $m$ negative coordinates gives the stated expression.

**Key facts.** `FABL.middleLayerIndicator_eq_one_iff_negative_count`, `FABL.independentProductPMF_apply`, `FABL.coordinateNoisePMF_one_toReal`.
