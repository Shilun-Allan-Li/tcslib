<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.lgv_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for the logarithmic quantity

**Claim.** For every natural number $n$, $lgv(n)\le \logSpace(n)+1$.

**Proof.** By definition, $lgv(n)=1+hv(n)$, while $\logSpace(n)=\operatorname{Nat.log}(2,n)+1$. If $n=0$, then $hv(n)=0$, so both sides reduce to $1\le 2$. If $n>0$, then $hv(n)=\operatorname{Nat.log}(2,n)+1$, and the claimed inequality is equality.
