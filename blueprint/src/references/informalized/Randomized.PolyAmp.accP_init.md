<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.accP_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability at initialization

**Claim.** If every length-$T$ choice word halts when run from the initial configuration, then the probability of reaching a halted configuration with output exactly $[\mathrm{true}]$ equals the probability that the output after $T$ steps is exactly $[\mathrm{true}]$.

**Proof.** Compare the two events on each uniformly sampled length-$T$ choice word. By the halting hypothesis, the resulting configuration has state `none`. Hence it satisfies the acceptance condition precisely when its output is $[\mathrm{true}]$. The output after running that word is exactly the output used in the definition of the output probability. Thus the events agree for every choice word, and `randProb_congr` gives equality of their probabilities.

**Key facts.** `Randomized.randProb_congr`.
