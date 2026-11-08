<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.randProb_runWith_seg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability after a fixed run segment

**Claim.** If every choice word of length $S$ takes $C$ to $C'$, then the probability that $Q$ holds after a uniformly chosen run of length $S+T$ from $C$ equals the probability that $Q$ holds after a uniformly chosen run of length $T$ from $C'$.

**Proof.** For each choice word $r$ of length $S+T$, split it into its first $S$ choices and its remaining suffix. The run on the whole word is the run on the suffix starting from the configuration reached by the first segment, by the concatenation law for runs (`Turing.NDTM.runWith_append`). The hypothesis identifies that intermediate configuration with $C'$, since the first segment has length $S$. Thus the event being counted is exactly the event that the suffix, run from $C'$, satisfies $Q$. The uniform probability is unchanged when we discard the first $S$ choices: the fixed-segment probability lemma (`Randomized.randProb_drop`) identifies the probability of a property depending only on that suffix with its probability under a uniform length-$T$ word. The event-equivalence principle for probabilities (`Randomized.randProb_congr`) then gives the claimed equality.

**Key facts.** `Turing.NDTM.runWith_append`, `Randomized.randProb_drop`, `Randomized.randProb_congr`.
