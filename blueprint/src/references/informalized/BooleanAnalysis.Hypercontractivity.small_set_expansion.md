<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.small_set_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-set expansion bound

**Claim.** For $0<\rho\leq1$ and a finite set $A\subseteq\{-1,1\}^n$, the noise stability of its indicator is at most $\operatorname{volume}(A)^{2/(1+\rho)}$.

**Proof.** Apply the generalized small-set expansion theorem with $p=1+\rho$, $u=(1+\rho)/\rho$, and with both sets equal to $A$ (\texttt{generalized_small_set_expansion}). Its exponent on the first volume is $(u-1)/u=1/(1+\rho)$, and its exponent on the second is $1/p=1/(1+\rho)$, so the right side is $\operatorname{volume}(A)^{1/(1+\rho)}\operatorname{volume}(A)^{1/(1+\rho)}$. The hypotheses hold: $p\geq1$, $p\leq u$, and $u\geq2$ follow from $0<\rho\leq1$. Its radius condition is $\rho\leq\sqrt{(p-1)/(u-1)}$, which reduces to $\rho\leq\sqrt{\rho^2}=\rho$. Finally, the volume is nonnegative (\texttt{volume_nonneg}), so the usual addition law for nonnegative real powers combines the two factors into $\operatorname{volume}(A)^{2/(1+\rho)}$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.generalized_small_set_expansion`, `BooleanAnalysis.Hypercontractivity.volume_nonneg`.
