<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.equation9_12_signCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-function bound on the sign cube

**Claim.** For $\rho\in[0,1]$, the expectation of $f(x)g(y)$ under the correlated sign-cube distribution is at most the product of the uniform $L^{1+\rho}$ norms of $f$ and $g$.

**Proof.** Apply the weak two-function hypercontractivity bound on the sign cube with both norm parameters and the correlation parameter equal to $\rho$ (`weakTwoFunctionHypercontractivity_signCube`). The interval hypotheses and nonnegativity follow from $\rho\in[0,1]$, and the correlation constraint is $\rho\le\sqrt{\rho^2}=\rho$. The bound then has exponent $1+\rho$ in each of the two norms, as required.

**Key facts.** `FABL.weakTwoFunctionHypercontractivity_signCube`.
