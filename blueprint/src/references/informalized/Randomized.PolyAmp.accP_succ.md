<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.accP_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step acceptance probability recurrence

**Claim.** For every configuration $C$ and every $j$, the acceptance probability for a uniformly random choice word of length $j+1$ is the average of the length-$j$ acceptance probabilities starting after the true and false first choices.

**Proof.** A uniformly random word of length $j+1$ is obtained by choosing its first bit uniformly from true and false, then choosing a uniformly random suffix of length $j$. The recurrence for uniform word probabilities (`randProb_succ`) expresses the probability of an event as the average of the probabilities conditional on these two first bits. For a fixed first bit, the run on the whole word is the run on its suffix starting from the configuration reached by that first step. Applying this to acceptance gives the stated average.

**Key facts.** `Randomized.randProb_succ`.
