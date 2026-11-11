<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.measureReal_finset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure of a finite set

**Claim.** For any finite subset $T$ of a finite probability space, its real-valued probability is the sum of the probabilities of its singleton points.

**Proof.** Apply the finite-preimage decomposition to the identity map on the space. The preimage of $T$ under the identity is $T$, and the preimage of each singleton $\{a\}$ is that same singleton. Thus the decomposition states exactly that the measure of $T$ is the sum of the measures of its points.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.measureReal_preimage_finset`.
