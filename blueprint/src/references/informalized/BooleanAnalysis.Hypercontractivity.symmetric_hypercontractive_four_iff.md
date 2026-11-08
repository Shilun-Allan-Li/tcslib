<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Symmetric.lean :: BooleanAnalysis.Hypercontractivity.symmetric_hypercontractive_four_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric fourth-moment criterion

**Claim.** For a symmetric random variable with unit $L^2$ norm, fourth norm $C>0$, and $0\le\rho<1$, hypercontractivity from exponent $2$ to exponent $4$ holds exactly when $\rho\le\min\{1/\sqrt3,1/C\}$.

**Proof.** Write $A(a,b)=a+bX$. Symmetry identifies the moments at $b$ and $-b$, so their average has no odd-power terms. The norm-moment identity gives $\|A(a,b)\|_2^2=a^2+b^2$ and $\|A(a,b)\|_4^4=a^4+6a^2b^2+b^4C^4$. Thus the affine norm inequality at radius $\rho$ is equivalent, for every $a,b$, to $a^4+6a^2\rho^2b^2+\rho^4b^4C^4\le(a^2+b^2)^2$. For necessity, set $(a,b)=(0,1)$ to obtain $(\rho C)^4\le1$, hence $\rho\le1/C$. The same polynomial inequality forces $6\rho^2\le2$: if this failed, the positive excess in the mixed coefficient would dominate the right side for a sufficiently large choice of $a$ with $b=1$, contradicting the inequality. Since $\rho\ge0$, this is equivalent to $\rho\le1/\sqrt3$. For sufficiency, the two radius bounds imply $6\rho^2\le2$ and $\rho^4C^4\le1$. Comparing coefficients in the displayed polynomial inequality proves it for all $a,b$. The exponent, radius, and integrability conditions in the definition of hypercontractivity are already ensured by the hypotheses.
