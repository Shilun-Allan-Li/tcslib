<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DisjointModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_disjointEvent_inter_disjointModel_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of a Disjoint-Model Fiber

**Claim.** For each point $z$ in the disjoint-model space, the set of hard samples that are disjoint and map to $z$ has measure $1/(n\cdot4\cdot3^n)$, the mass of one hard sample.

**Proof.** Under the uniform measure on a finite space, a subset has measure equal to its number of elements divided by the size of the whole space (`CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`). The relevant fiber contains exactly one hard sample (`card_disjointEvent_inter_disjointModel_fiber`), while the whole hard-sample space has size $n\cdot4\cdot3^n$ (`HardSample.card`). Substituting these counts gives the claimed mass.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.card_disjointEvent_inter_disjointModel_fiber`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.HardSample.card`.
