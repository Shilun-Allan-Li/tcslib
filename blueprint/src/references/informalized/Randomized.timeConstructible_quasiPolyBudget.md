<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.timeConstructible_quasiPolyBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time constructibility of the quasi-polynomial budget

**Claim.** The function $T(n)=2^{(\log_2 n)^2+1}$, with integer logarithm and $\log_2 0=0$, is time constructible: it dominates $n$, and a finite binary Turing machine outputs the binary representation of $T(|x|)$ in time bounded by a constant multiple of $T(|x|)+1$.

**Proof.** The lower bound $n\le T(n)$ is supplied by the established estimate $\texttt{le_quasiPolyBudget}$. Also, a finite binary Turing machine computes the binary representation of the budget in polynomial time, by $\texttt{polyTimeComputable_bits_quasiPolyBudget}$. Let its time bound be $C(|x|+1)^c$ for constants $C,c$. The estimate $\texttt{succ_pow_le_quasiPoly}$ bounds $(|x|+1)^c$ by $2^{c(c+1)}2^{(\log_2 |x|)^2}$. Since $2^{(\log_2 |x|)^2}\le T(|x|)+1$, multiplying these inequalities gives $C(|x|+1)^c\le (C2^{c(c+1)}+1)(T(|x|)+1)$. The machine therefore meets the required linear-in-$T+1$ time bound, with the positive integer constant $C2^{c(c+1)}+1$.

**Key facts.** `Randomized.le_quasiPolyBudget`, `Randomized.polyTimeComputable_bits_quasiPolyBudget`, `Randomized.succ_pow_le_quasiPoly`, `Turing.FinTM.ComputesInTime.mono`.
