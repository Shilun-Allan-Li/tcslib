<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.fourierOneNorm_majority_odd_isEquivalent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic Fourier norm of odd majority

**Claim.** As $m$ tends to infinity, the Fourier one-norm of majority on $2m+1$ sign coordinates is asymptotic to $\frac{2}{\sqrt{\pi}}\frac{1}{\sqrt{2m+1}}2^{(2m+1)/2}$.

**Proof.** The Fourier norm has an exact expression as the reciprocal-binomial expectation times $(2m+1)2^m$ and the odd-majority influence (`fourierOneNorm_majority_odd_eq_expectation_mul_influence`). Divide it by $2\cdot 2^m$ times the main asymptotic term for the influence. The resulting ratio is the product of the normalized reciprocal-binomial expectation and the ratio of the actual influence to its main term. The first factor tends to $1$ (`tendsto_binomialHalfOddReciprocalExpectation_mul_oddArity_div_two`), and the second tends to $1$ (`tendsto_oddMajorityInfluence_div_main`); hence their product tends to $1$. This proves asymptotic equivalence to $2\cdot 2^m$ times the main influence term. The identity identifying that expression with $\frac{2}{\sqrt{\pi}}\frac{1}{\sqrt{2m+1}}2^{(2m+1)/2}$ completes the proof (`majorityFourierOneNormMain_eq_bookMain`).

**Key facts.** `FABL.tendsto_binomialHalfOddReciprocalExpectation_mul_oddArity_div_two`, `FABL.tendsto_oddMajorityInfluence_div_main`, `FABL.fourierOneNorm_majority_odd_eq_expectation_mul_influence`, `FABL.majorityFourierOneNormMain_eq_bookMain`.
