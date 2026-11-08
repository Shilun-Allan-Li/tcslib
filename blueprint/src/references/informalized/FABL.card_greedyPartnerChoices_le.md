<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_greedyPartnerChoices_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Greedy partner choice bound

**Claim.** If $r,s>0$ and the remaining vertex set has size $2s$, then the number of vertices outside the part containing the greedy pivot is at most $\frac{2r-1}{r}s$.

**Proof.** Let $L$ be the number of remaining vertices in the greedy largest part, and let $C$ be the number outside that part. Since there are $2r$ parts, each containing at most $L$ remaining vertices, the total size $2s$ is at most $2rL$; hence $s\le rL$ (`remaining_card_le_parts_mul_largest`). The decomposition of the remaining vertices gives $C+L=2s$ (`card_greedyPartnerChoices_add_largest`). Therefore $rC=2rs-rL\le 2rs-s=(2r-1)s$. Dividing by the positive number $r$ gives the claimed real-valued bound.

**Key facts.** `FABL.remaining_card_le_parts_mul_largest`, `FABL.card_greedyPartnerChoices_add_largest`.
