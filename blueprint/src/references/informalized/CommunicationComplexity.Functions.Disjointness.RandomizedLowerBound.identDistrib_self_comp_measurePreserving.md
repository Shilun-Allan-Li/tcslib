<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_self_comp_measurePreserving -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition Preserves Distribution Under Invariance

**Claim.** If $T$ preserves the measure $\mu$ and $F$ is measurable, then $F$ and $F\circ T$ are identically distributed under $\mu$.

**Proof.** Measurability of $F$ and of $T$ ensures that both random variables are measurable up to null sets. Because $T$ preserves $\mu$, its pushforward measure is again $\mu$. The pushforward law of $F\circ T$ is therefore the pushforward of $\mu$ by $F$ after first pushing $\mu$ forward by $T$; composition of pushforwards gives the same law as pushing $\mu$ forward by $F$. Thus the two random variables induce the same distribution.
