<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.ext -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extensionality of Finite Distributions

**Claim.** If two probability distributions on the same finite set assign equal probabilities to every outcome, then they are equal.

**Proof.** A finite distribution is determined by its probability function; its nonnegativity and total-mass conditions are proof fields. The hypothesis says the two probability functions agree pointwise, hence they are equal as functions by function extensionality. Once the structures are decomposed into their fields, this equality identifies the distributions.
