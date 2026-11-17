<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basic.lean :: BooleanAnalysis.GaussianSpace.derivative_hermite_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Gaussian Hermite polynomial

**Claim.** For every natural number $k$, the derivative of the Gaussian Hermite polynomial of degree $k+1$ is $(k+1)$ times the Gaussian Hermite polynomial of degree $k$.

**Proof.** Proceed by induction on $k$. In the base case, the identity follows directly from the degree-one Hermite polynomial. For the successor step, express the Hermite polynomial of degree $k+2$ by the Hermite recurrence in terms of the degree $k+1$ polynomial and the degree $k$ polynomial. Differentiate that recurrence using the product rule and the derivative of the variable polynomial. The induction hypothesis replaces the derivative of the degree $k+1$ polynomial by $(k+1)$ times the degree $k$ polynomial. Applying the recurrence once more and collecting coefficients gives $(k+2)$ times the degree $k+1$ polynomial, as required.
