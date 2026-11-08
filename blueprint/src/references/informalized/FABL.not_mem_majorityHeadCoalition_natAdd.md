<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.not_mem_majorityHeadCoalition_natAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail Indices Avoid the Head Coalition

**Claim.** For natural numbers $k,m$ and any $j<m$, the index $k+j$ among the $k+m$ indices does not belong to the coalition of the first $k$ indices.

**Proof.** Under the standard identification of the ordered sum of $k$ and $m$ indices with the indices of length $k+m$, the index $k+j$ corresponds to the right-summand element $j$. The right-summand exclusion fact (`not_mem_majorityHeadCoalition_right`) says that this element is outside the coalition formed from the left, or first, summand. Therefore $k+j$ is not in the head coalition.

**Key facts.** `FABL.not_mem_majorityHeadCoalition_right`.
