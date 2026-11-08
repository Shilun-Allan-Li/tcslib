<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majority_arbitraryCoalition_zero_of_subsqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arbitrary Coalition Influence Below Square-Root Scale

**Claim.** If $m(q)\to\infty$ and $k(q)/\sqrt{k(q)+m(q)}\to0$, then the total coalitional influence of majority tends to zero for any coalition of size $k(q)$ in dimension $k(q)+m(q)$.

**Proof.** The canonical coalition of the first $k(q)$ coordinates has total influence tending to zero under these hypotheses (`tendsto_majority_head_total_coalitionalInfluence_zero_of_subsqrt`). At each index, the arbitrary coalition and the canonical one have the same cardinality. Since majority's total coalitional influence depends only on that cardinality (`coalitionalInfluence_majority_eq_of_card`), their influence values agree, and the arbitrary-coalition sequence therefore also tends to zero.

**Key facts.** `FABL.tendsto_majority_head_total_coalitionalInfluence_zero_of_subsqrt`, `FABL.coalitionalInfluence_majority_eq_of_card`.
