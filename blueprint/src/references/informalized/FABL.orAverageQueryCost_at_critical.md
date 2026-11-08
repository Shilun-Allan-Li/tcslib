<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.orAverageQueryCost_at_critical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Average Query Cost

**Claim.** If $p\ne0$ and $(1-p)^n=1/2$, then the average query cost $\sum_{k=0}^{n-1}(1-p)^k$ equals $1/(2p)$.

**Proof.** The geometric-sum formula expresses the cost as $(1-(1-p)^n)/p$ (`orAverageQueryCost_eq`). Substituting the critical-parameter hypothesis makes the numerator $1/2$, giving $1/(2p)$. The assumption $p\ne0$ ensures the division is valid.

**Key facts.** `FABL.orAverageQueryCost_eq`.
