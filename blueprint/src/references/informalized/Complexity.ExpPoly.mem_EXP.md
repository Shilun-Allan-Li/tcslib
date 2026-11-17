<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExpPoly.lean :: Complexity.ExpPoly.mem_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential-Polynomial Time Lies in EXP

**Claim.** If $T$ is exponential-polynomial and $L$ is in $\mathrm{DTIME}(T)$, then $L\in\mathrm{EXP}$.

**Proof.** Choose constants $K,k$ such that $T(n)\le 2^{K(n+1)^k}$, and choose a machine $M$ and constant $c_0$ witnessing that $L\in\mathrm{DTIME}(T)$. We bound this running time by a time bound of the form allowed in $\mathrm{EXP}$. For $n\ge 2$, we have $K\le n^K$ and $n+1\le n^2$. Therefore
\[
K(n+1)^k\le n^K(n^2)^k=n^{K+2k}.
\]
Exponentiating with base $2$ gives $2^{K(n+1)^k}\le 2^{n^{K+2k}}$. When $n<2$, instead use $(n+1)^k\le 2^k$ to get $2^{K(n+1)^k}\le 2^{K2^k}$; this is at most $2^{K2^k}2^{n^{K+2k}}$. Thus for every $n$,
\[
T(n)\le 2^{K2^k}\,2^{n^{K+2k}}.
\]
The original machine's time bound is $c_0T(n)$, so it is at most $c_0 2^{K2^k}2^{n^{K+2k}}$. By monotonicity of computation time, this same machine witnesses membership in $\mathrm{DTIME}(n\mapsto c_0 2^{K2^k}2^{n^{K+2k}})$. This is one of the time bounds in the union defining $\mathrm{EXP}$, with exponent parameter $K+2k$ and multiplier $c_0 2^{K2^k}$.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`.
