<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.accP_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability invariance

**Claim.** If two configurations have the same core data and the same output summary, then for every $j$ the probabilities of reaching a halted configuration with output exactly $[\mathrm{true}]$ under a uniformly random length-$j$ choice word are equal.

**Proof.** Fix a length-$j$ choice word. Equality of the configurations' core data and output summaries is preserved when both configurations are run on that word (`coreSum_runWith`). Their resulting configurations therefore have equal core data and output summaries. The acceptance criterion is determined by this combined summary: equal summaries give equivalent acceptance (`accepting_congr`). Thus, for each choice word, the run from the first configuration accepts exactly when the run from the second does. The probabilities are consequently equal, since `randProb_congr` says that pointwise equivalent events on all length-$j$ choice words have the same uniform probability.

**Key facts.** `Turing.NDTM.coreSum_runWith`, `Randomized.PolyAmp.accepting_congr`, `Randomized.randProb_congr`.
