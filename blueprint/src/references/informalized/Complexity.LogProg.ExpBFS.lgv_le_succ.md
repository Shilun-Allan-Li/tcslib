<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.lgv_le_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear upper bound for the adjusted logarithm

**Claim.** For every natural number $n$, $lgv(n)\le n+1$.

**Proof.** If $n=0$, then $hv(n)=0$ and $lgv(n)=1$, so the inequality is equality. If $n>0$, then $hv(n)=\operatorname{Nat.log}(2,n)+1$. The standard bound $\operatorname{Nat.log}(2,n)<n$ for positive $n$ gives $lgv(n)=\operatorname{Nat.log}(2,n)+2\le n+1$.
