<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.hasSum_measure_singletons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton masses sum to one

**Claim.** For a finite probability space and a bijection from its points to a finite type, the singleton masses indexed through that bijection are summable and have sum one.

**Proof.** The singletons $\{e^{-1}(a)\}$ cover the whole space: every point is the inverse image of its image under the bijection. They are pairwise disjoint because the inverse of a bijection is injective. Each singleton is measurable since the space is discrete. Countable additivity therefore identifies the measure of the whole space with the sum of these singleton measures. The whole-space measure is one, and on a finite index type this finite sum gives the asserted summability and total.
