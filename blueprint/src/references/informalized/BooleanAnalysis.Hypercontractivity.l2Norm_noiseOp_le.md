<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.l2Norm_noiseOp_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Bound for Low-Degree Functions

**Claim.** If every nonzero Fourier coefficient of $f$ is indexed by a set of size at most $k$, then for $\rho\geq1$, $\|T_\rho f\|_2\leq\rho^k\|f\|_2$.

**Proof.** Parseval's identity expresses the squared norm of a function as the sum of squares of its Fourier coefficients. The noise operator multiplies the coefficient indexed by $S$ by $\rho^{|S|}$. For a nonzero coefficient, the degree hypothesis gives $|S|\leq k$, hence $\rho^{2|S|}\leq\rho^{2k}$; a zero coefficient contributes nothing. Summing these termwise bounds by Parseval gives $\langle T_\rho f,T_\rho f\rangle\leq (\rho^k)^2\langle f,f\rangle$. Taking square roots and using $\rho^k\geq0$ proves the norm inequality.

**Key facts.** `BooleanAnalysis.noiseOp_fourier`, `BooleanAnalysis.parseval`.
