<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.discreteDerivative_mul_polynomialDerivativeThreshold_eq_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative Product Equals Its Square

**Claim.** At every point $x$, the discrete derivative of $f$ multiplied by the value of the threshold of the polynomial's discrete derivative equals the square of the discrete derivative of $f$.

**Proof.** Separate the cases according to whether the discrete derivative of $f$ at $x$ vanishes. If it is zero, both sides are zero. Otherwise, the nonvanishing-derivative identification theorem says that this derivative equals the real-valued polynomial-derivative threshold at $x$ ($\texttt{FABL.discreteDerivative\_toReal\_eq\_polynomialDerivativeThreshold\_of\_ne\_zero}$). Substituting that equality into the left side makes it the product of the derivative with itself, which is its square.

**Key facts.** `FABL.discreteDerivative_toReal_eq_polynomialDerivativeThreshold_of_ne_zero`.
