<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.eventually_fknOptimalityDelta_lt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Eventual smallness of doubled set mass

**Claim.** For all sufficiently large integers $q$, the doubled uniform mass of the selected threshold set is less than $1$.

**Proof.** The doubled mass $\Delta(q)$ tends to $0$ as $q\to\infty$. Since the interval $(-\infty,1)$ is a neighborhood of $0$, convergence implies that $\Delta(q)<1$ for all sufficiently large $q$.

**Key facts.** `FABL.tendsto_fknOptimalityDelta`.
