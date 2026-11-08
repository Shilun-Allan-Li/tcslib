<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.orAverageQueryCost_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Query Cost Recurrence

**Claim.** For every natural number $n$ and real number $p$, the average query cost satisfies $C_{n+1}(p)=1+(1-p)C_n(p)$, where $C_n(p)=\sum_{k=0}^{n-1}(1-p)^k$.

**Proof.** Separating the last term in the sum through exponent $n$ gives $C_{n+1}(p)=C_n(p)+(1-p)^n$. The geometric-sum identity gives $(1-p)^n=1-pC_n(p)$, after rearranging the finite geometric sum. Substitution yields $C_{n+1}(p)=1+(1-p)C_n(p)$.
