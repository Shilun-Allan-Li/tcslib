<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.equation9_12 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-function hypercontractive bound

**Claim.** For the stated parameter $\rho\in[0,1]$, the correlated expectation of the product of two functions is bounded above by the product of their iterated $L^{1+\rho}$ norms.

**Proof.** Apply the weak two-function hypercontractivity bound with both norm parameters set to $\rho$, and with correlation parameter also set to $\rho$ (`weakTwoFunctionHypercontractivity`). Its hypotheses hold: $\rho\in[0,1]$ supplies both interval conditions and nonnegativity, while $\rho\le\sqrt{\rho\rho}=\rho$ gives the correlation constraint. The resulting norm exponents are both $1+\rho$, yielding the claimed inequality.

**Key facts.** `FABL.weakTwoFunctionHypercontractivity`.
