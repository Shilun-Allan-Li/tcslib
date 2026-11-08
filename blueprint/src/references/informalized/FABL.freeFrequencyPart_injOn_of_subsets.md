<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.freeFrequencyPart_injOn_of_subsets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Free Frequency Part

**Claim.** For a coordinate set $J$, the map sending each member $U$ of a family of subsets of $J$ to its part inside $J$ is injective on that family.

**Proof.** Take $S,T$ in the family and suppose their free parts inside $J$ agree. Since both sets are contained in $J$, each can be recovered by lifting its free part: the lift of the free part of $S$ is $S$, and the lift of the free part of $T$ is $T$ (the recovery identity `liftFreeFrequency_freeFrequencyPart_eq_of_subset`). The assumed equality of free parts therefore gives $S=T$.

**Key facts.** `FABL.liftFreeFrequency_freeFrequencyPart_eq_of_subset`.
