<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.narm_space_randProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space and probability preservation

**Claim.** Under the stated hypotheses, the compiled machine has the common halting length and space bound, preserves whether true can be produced, and preserves the probability of each Boolean output.

**Proof.** First apply the space-and-acceptance theorem (`narm_space`) to obtain a length $T$ with the required halting, space, and acceptance properties. Then apply the probability-preservation theorem (`narm_randProb`) at this same $T$, using its halting hypothesis from the first result. It states that, for either Boolean value $b$, the fraction of length-$T$ compiled choice strings producing exactly $b$ equals the fraction of length-$N$ register choice strings producing $b$.

**Key facts.** `Complexity.LogProg.narm_space`, `Complexity.LogProg.narm_randProb`.
