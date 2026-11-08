<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.time_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Time Bound

**Claim.** Under the hypothesis $\logSpace(n)\le S_n$, the left-hand exponential and squared-memory expression in the statement is at most the stated power of $2$.

**Proof.** Write $K_0=\mathrm{codeK}(N)$ and $E=K_0(c_0S_n+1+\mathrm{lgv}(n)+1)$. The coding-width bound gives $K_0\ge2$ ( `two_le_codeK` ). The comparisons between $\mathrm{lgv}(n)$ and $\logSpace(n)$ ( `lgv_le` and `logSpace_le_lgv` ) let us bound both the logarithmic register width and the input contribution in terms of $E$. Also $n+1\le2^{\logSpace(n)}$, so these comparisons yield $n+4\le2^{E+1}$. Using $\mathrm{kb}(N,n,c_0S_n+1)=2^E$, the definitions of $\mathrm{bigB}$ and $\mathrm{kb}$ then give two bounds: the register width $\log_2(\mathrm{bigB}(N,n,c_0S_n)+1)+1$ is at most $E+3$, and the memory-range quantity $3\mathrm{kb}(N,n,c_0S_n+1)+1$ is at most $2^{E+2}$. Set $a=K_0(c_0+3)$. The hypothesis $\logSpace(n)\le S_n$ and the bound on $\mathrm{lgv}(n)$ imply $E\le a(S_n+1)$. Consequently the total exponent, including the square of the memory-range bound, is at most $(C(a+4)+2a+4)(S_n+1)$. Monotonicity of powers of $2$ gives the desired inequality, and substituting the definition of $a$ yields the exponent displayed in the claim.

**Key facts.** `Complexity.LogProg.ExpBFS.two_le_codeK`, `Complexity.LogProg.ExpBFS.lgv_le`, `Complexity.LogProg.ExpBFS.logSpace_le_lgv`.
