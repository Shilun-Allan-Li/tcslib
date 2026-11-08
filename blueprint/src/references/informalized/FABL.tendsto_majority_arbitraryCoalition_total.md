<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majority_arbitraryCoalition_total -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arbitrary Coalition Total Influence Limit

**Claim.** For any coalitions $J(q)$ of size $k(q)$ in dimension $k(q)+m(q)$, if $m(q)\to\infty$ and $k(q)/\sqrt{k(q)+m(q)}\to t$, their total coalitional influence for majority tends to $2$ times the stated Gaussian limit.

**Proof.** First use the limit theorem for the canonical coalition consisting of the first $k(q)$ coordinates: under the given growth and ratio assumptions, its total influence tends to $2$ times the Gaussian limit (`tendsto_majority_head_total_coalitionalInfluence_totalDimension`). For each $q$, the given coalition and this canonical coalition lie in the same dimension and have equal cardinality: both have size $k(q)$. Majority's total coalitional influence depends only on coalition size (`coalitionalInfluence_majority_eq_of_card`), so the two influence sequences agree term by term. Consequently the given sequence has the same limit.

**Key facts.** `FABL.tendsto_majority_head_total_coalitionalInfluence_totalDimension`, `FABL.coalitionalInfluence_majority_eq_of_card`.
