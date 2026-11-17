<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.noiseSensitivity_le_three_mul_rpow_of_isPolynomialThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Stability of Polynomial Thresholds

**Claim.** Every degree-$k$ polynomial threshold function has noise sensitivity at most $3\delta^{1/2^k}$ for $\delta\in(0,1/2]$.

**Proof.** Set $m=\lfloor1/delta\rfloor$. Apply the inverse noise floor bound to the degree-$k$ polynomial threshold class, which is closed under input negations and variable identifications (\texttt{polynomialThresholdClass_closedUnderNegatingInputVariables}, \texttt{polynomialThresholdClass_closedUnderIdentifyingInputVariables}). The influence bound for this class gives total influence at most $2m^{1-\beta}$, where $\beta=1/2^k$; the identity relating the influence and noise exponents is recorded in \texttt{polynomialThresholdInfluenceExponent_eq_one_sub_noiseExponent}. Thus the inverse-floor theorem bounds the noise sensitivity by $2(1/m)^\beta$ (\texttt{noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound}). The floor estimate gives $1/m\le(3/2)\delta$ (equivalently, its square-root form is \texttt{sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt}). Since $0<\beta\le1$, raising this inequality to the power $\beta$ and using $(3/2)^\beta\le3/2$ yields $(1/m)^\beta\le(3/2)\delta^\beta$. Multiplication by $2$ gives the claimed constant $3$.

**Key facts.** `FABL.noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound`, `FABL.polynomialThresholdClass_closedUnderNegatingInputVariables`, `FABL.polynomialThresholdClass_closedUnderIdentifyingInputVariables`, `FABL.totalInfluence_toReal_le_two_mul_rpow_of_isPolynomialThreshold`, `FABL.polynomialThresholdInfluenceExponent_eq_one_sub_noiseExponent`, `FABL.sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt`, `FABL.polynomialThresholdNoiseExponent_pos`, `FABL.polynomialThresholdNoiseExponent_le_one`.
