<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.randProb_runWith_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Constant Run Outcome

**Claim.** If every choice word of length $S$ sends the initial configuration to $C_f$, then the probability that a decidable property $Q$ holds after such a run is $1$ when $Q(C_f)$ holds and $0$ otherwise.

**Proof.** For every length-$S$ choice word, the run ends at $C_f$ by hypothesis. Thus the event that $Q$ holds after the run is equivalent, word by word, to the constant proposition $Q(C_f)$, and the corresponding probabilities agree (`randProb_congr`). The probability of a constant proposition is $1$ if it is true and $0$ if it is false (`randProb_const`).

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_const`.
