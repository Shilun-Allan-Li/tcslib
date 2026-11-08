<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.randProb_eq_some_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Probability and Nontermination Bound

**Claim.** For a prefix-stable computation $r$, the probability that it outputs $v$ on a uniformly random word of length $t'$ is at most the probability that it outputs $v$ at length $t$, plus the probability that it has not halted at length $t$.

**Proof.** First suppose $t'\le t$. The probability of outputting $v$ is nondecreasing with word length for a prefix-stable computation (`Randomized.randProb_eq_some_mono`), so the desired bound follows after adding the nonnegative nontermination probability (`Randomized.notHaltedProb_nonneg`). Now suppose $t\le t'$. By invariance under taking an initial segment, the length-$t'$ output probability can be computed by testing the first $t$ bits (`Randomized.randProb_take`). At length $t$, the events “outputs $v$” and “has not halted” are disjoint, so the probability of their union is the sum of their probabilities (`Randomized.randProb_or_disjoint`). It remains to see that every length-$t'$ word whose length-$t$ prefix has output $v$ lies in this union: if the prefix has no output, it lies in the nontermination event; if the prefix has an output, prefix stability forces the full word to have that same output (`Randomized.IsPrefixStable.of_take`). Monotonicity of probability under event inclusion (`Randomized.randProb_mono`) then bounds the length-$t'$ output probability by that sum, as required.

**Key facts.** `Randomized.notHaltedProb_nonneg`, `Randomized.randProb_eq_some_mono`, `Randomized.randProb_take`, `Randomized.randProb_or_disjoint`, `Randomized.IsPrefixStable.of_take`, `Randomized.randProb_mono`.
