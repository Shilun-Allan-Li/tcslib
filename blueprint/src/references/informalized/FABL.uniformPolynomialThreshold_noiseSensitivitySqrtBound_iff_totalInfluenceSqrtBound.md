<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.uniformPolynomialThreshold_noiseSensitivitySqrtBound_iff_totalInfluenceSqrtBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise sensitivity and total influence bounds

**Claim.** The class has a uniform noise-sensitivity bound of order $k\sqrt{\delta}$ if and only if it has a uniform total-influence bound of order $k\sqrt n$.

**Proof.** Assume first a noise-sensitivity bound with constant $C\ge0$. We prove an influence bound with constant $\frac{2C}{1-e^{-2}}$. If $n=0$, total influence lies between $0$ and $n$ (\texttt{totalInfluence\_toReal\_mem\_Icc}), so it is zero. If $n=1$, total influence equals twice the noise sensitivity at $\delta=1/2$ (\texttt{totalInfluence\_dimension\_one\_eq\_two\_mul\_noiseSensitivity\_half}); the assumed estimate and $\sqrt{1/2}\le1$ give the desired bound with the stated constant. For $n\ge2$, use $\delta=1/n$. The inverse-dimension estimate (\texttt{totalInfluence\_le\_constant\_mul\_dimension\_of\_noiseSensitivity\_inverseDimension\_le}) bounds total influence by $\frac{2}{1-e^{-2}}n$ times the noise sensitivity at this parameter. Applying the assumed bound and using $n\sqrt{1/n}=\sqrt n$ gives the required $k\sqrt n$ estimate.

Conversely, suppose total influence is bounded by $Ck\sqrt n$. Apply the noise-sensitivity estimate in terms of total influence at the inverse noise floor, using that polynomial threshold functions are closed under negating and identifying input variables (\texttt{polynomialThresholdClass\_closedUnderNegatingInputVariables}, \texttt{polynomialThresholdClass\_closedUnderIdentifyingInputVariables}). This gives noise sensitivity at most $Ck\sqrt m/m$, where $m$ is the inverse noise floor. The bound $\sqrt{1/m}\le\sqrt{3/2}\sqrt{\delta}$ (\texttt{sqrt\_inverseNoiseFloor\_le\_sqrt\_three\_halves\_mul\_sqrt}) then yields the desired estimate with constant $C\sqrt{3/2}$. Both constants are nonnegative, completing the equivalence.

**Key facts.** `FABL.totalInfluence_toReal_mem_Icc`, `FABL.totalInfluence_dimension_one_eq_two_mul_noiseSensitivity_half`, `FABL.totalInfluence_le_constant_mul_dimension_of_noiseSensitivity_inverseDimension_le`, `FABL.polynomialThresholdClass_closedUnderNegatingInputVariables`, `FABL.polynomialThresholdClass_closedUnderIdentifyingInputVariables`, `FABL.noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound`, `FABL.sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt`.
