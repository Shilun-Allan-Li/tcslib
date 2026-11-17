<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.discreteDerivative_toReal_eq_polynomialDerivativeThreshold_of_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative and Polynomial Threshold

**Claim.** Under the stated nonvanishing and threshold-representation hypotheses, if the discrete derivative of the real-valued Boolean function at $x$ is nonzero, it equals the real-valued polynomial-derivative threshold function at $x$.

**Proof.** Consider the values of the representing polynomial at the two points obtained by setting coordinate $i$ to $1$ and to $-1$. Neither value is zero, so each is either negative or positive. If both have the same sign, the represented Boolean function has the same value at both points, making its discrete derivative zero by the difference formula (`discreteDerivative_apply`), contrary to the hypothesis. In the remaining two cases the polynomial values have opposite signs. If the value at the positive-coordinate point is negative and the other is positive, their difference divided by $2$ is negative; the represented Boolean values are $-1$ and $1$, so their difference divided by $2$ is also $-1$. The polynomial derivative threshold is likewise $-1$. If the polynomial values have the opposite sign pattern, both corresponding derivatives and the threshold are $1$. These evaluations use that negative inputs to the threshold map to $-1$ (`thresholdSign_of_neg`), nonnegative inputs map to $1$ (`thresholdSign_of_nonneg`), and the real values of the two signs are $-1$ and $1$ (`signValue_neg_one`, `signValue_one`).

**Key facts.** `FABL.discreteDerivative_apply`, `FABL.thresholdSign_of_neg`, `FABL.thresholdSign_of_nonneg`, `FABL.signValue_neg_one`, `FABL.signValue_one`.
