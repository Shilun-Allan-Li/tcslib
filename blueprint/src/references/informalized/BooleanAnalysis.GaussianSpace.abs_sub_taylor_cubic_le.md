<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.abs_sub_taylor_cubic_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-Order Taylor Remainder

**Claim.** For a four times continuously differentiable function whose fourth derivative is bounded in absolute value by $C$, the error after the cubic Taylor polynomial at $a$, evaluated at $a+b$, is at most $Cb^4/24$.

**Proof.** Apply the arbitrary-order Taylor remainder bound with order $m=3$ (`abs_sub_taylor_le`). Its error estimate is $(C/4!)|b|^4$. Since $4!=24$ and $|b|^4=b^4$, this is exactly the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_sub_taylor_le`.
