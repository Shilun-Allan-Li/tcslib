<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majority_head_directed_influences_totalDimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority head influence limit

**Claim.** If the outside dimension tends to infinity and the head size divided by the square root of the total dimension tends to $t$, then the directed influences of the majority head coalition toward both $+1$ and $-1$ tend to $\tfrac12-Q(t)$.

**Proof.** First, the ratio using the outside dimension has the same limit: since $m(q)\to\infty$, the total-dimension ratio hypothesis implies that $k(q)/\sqrt{m(q)}\to t$ (the outside-ratio comparison lemma, `tendsto_majority_outside_ratio_of_total_ratio`). Apply the directed-influence limit theorem with this ratio and with $m(q)\to\infty$. It gives convergence of each directed influence to the stated Gaussian-tail expression (`tendsto_majority_head_directed_influences`).

**Key facts.** `FABL.tendsto_majority_outside_ratio_of_total_ratio`, `FABL.tendsto_majority_head_directed_influences`.
