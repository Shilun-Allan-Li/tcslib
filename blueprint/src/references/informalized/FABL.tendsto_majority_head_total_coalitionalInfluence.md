<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majority_head_total_coalitionalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total majority head influence limit

**Claim.** If the outside dimension tends to infinity and $k(q)/\sqrt{m(q)}\to t$, then the probability that the head coalition can make majority attain both outputs tends to $2(\tfrac12-Q(t))$.

**Proof.** The directed-influence limit theorem gives convergence of the influences toward $+1$ and toward $-1$, each to the same Gaussian-tail limit (`tendsto_majority_head_directed_influences`). Adding these convergent sequences gives convergence of their sum to twice that limit. The total coalitional influence equals this sum, by the identity decomposing it into the two directed influences (`coalitionalInfluence_eq_toward_add_toward`).

**Key facts.** `FABL.tendsto_majority_head_directed_influences`, `FABL.coalitionalInfluence_eq_toward_add_toward`.
