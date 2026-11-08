<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.randProb_eq_some_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Output Probability

**Claim.** For a prefix-stable computation $r$ and lengths $t\le t'$, the probability that it outputs $v$ on a uniformly random word of length $t$ is at most the corresponding probability at length $t'$.

**Proof.** View the length-$t$ event as an event on length-$t'$ words by testing their first $t$ bits. This does not change its probability (`Randomized.randProb_take`). Whenever that prefix has output $v$, prefix stability implies the full word has output $v` (`Randomized.IsPrefixStable.of_take`). Thus the prefix event is contained in the length-$t'$ output event, and probability monotonicity under event inclusion gives the result (`Randomized.randProb_mono`).

**Key facts.** `Randomized.randProb_take`, `Randomized.IsPrefixStable.of_take`, `Randomized.randProb_mono`.
