<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.logSpace_le_lgv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Space Bound

**Claim.** For every natural number $n$, the logarithmic space bound is at most $\mathrm{lgv}(n)$.

**Proof.** Unfold the definitions. If $n=0$, then $\mathrm{hv}(0)=0$, so $\mathrm{lgv}(0)=1$ while $\mathrm{logSpace}(0)=1$. If $n\ne0$, then both sides reduce to $\mathrm{Nat.log}(2,n)+1$, and the inequality is equality.
