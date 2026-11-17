<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.abs_integral_sub_taylor_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Scalar Taylor Error

**Claim.** Under the stated fourth-order invariance moment conditions, the expected value of $\psi(a+bX)$ differs from its quadratic Taylor expression at $a$ by at most $3Cb^4/8$.

**Proof.** The fourth-moment bound follows from the reasonability condition: since the second moment is one and the reasonability parameter is $9$, the fourth moment is at most $9$. Apply the expected Taylor polynomial remainder estimate with degree three (`abs_integral_sub_taylor_polynomial_le`), using the available fourth-order differentiability and derivative bound. The cubic Taylor polynomial has expectation $\psi(a)+(\psi''(a)/2)b^2$: its linear and cubic terms vanish by the first and third moment conditions, and its quadratic term uses the second moment one (`integral_taylor_cubic`). The remainder is therefore at most $(C/4!)|b|^4$ times the fourth absolute moment, hence at most $(C/24)\cdot 9 b^4=3Cb^4/8$.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_integral_sub_taylor_polynomial_le`, `BooleanAnalysis.GaussianSpace.integral_taylor_cubic`.
