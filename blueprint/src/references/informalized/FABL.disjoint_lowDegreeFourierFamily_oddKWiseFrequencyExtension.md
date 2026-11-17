<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.disjoint_lowDegreeFourierFamily_oddKWiseFrequencyExtension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Frequency Families

**Claim.** The family of subsets of size at most $m$ is disjoint from the family obtained by adjoining $i$ to each $m$-element subset of the other coordinates.

**Proof.** Suppose a set $S$ belonged to both families. Membership in the low-degree family gives $|S|\le m$ (`mem_lowDegreeFourierFamily`). Membership in the extended family gives $|S|=m+1$ (`mem_oddKWiseFrequencyExtension_card`). These cardinality statements contradict one another, so the two families are disjoint.

**Key facts.** `FABL.mem_lowDegreeFourierFamily`, `FABL.mem_oddKWiseFrequencyExtension_card`.
