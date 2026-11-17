<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested conditioning on a subset

**Claim.** If an event $A$ is contained in the disjointness event $E$, then conditioning the uniform measure on $A$ agrees with first conditioning on $E$ and then on $A$.

**Proof.** By the conditional-conditioning identity, conditioning the original measure on $E$ and then on $A$ is the same as conditioning it on $E\cap A$. Since $A\subseteq E$, we have $E\cap A=A$, so this is precisely conditioning on $A$.
