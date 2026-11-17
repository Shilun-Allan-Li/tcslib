<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.biasedProb_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Probability Respects Event Equivalence

**Claim.** If two predicates agree on every Boolean word of length $m$, then their biased probabilities for length-$m$ words are equal, for every real bias parameter.

**Proof.** Induct on $m$, allowing both predicates to vary in the induction hypothesis. At $m=0$, the only word under consideration is the empty word, and the hypothesis says the predicates have the same truth value there. The defining probability is therefore either $1$ for both predicates or $0$ for both. For the successor case, split each probability according to whether the first bit is true or false, using the one-step recurrence (`Randomized.biasedProb_succ`). In either branch, the resulting predicates on the remaining word agree on all words of length $m$: prefixing such a word by the chosen bit gives a word of length $m+1$, where the original agreement applies. The induction hypothesis equates the two branch probabilities, and thus the weighted sums in the recurrence are equal.

**Key facts.** `Randomized.biasedProb_succ`.
