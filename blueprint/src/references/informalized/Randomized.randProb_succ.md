<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-bit probability recurrence

**Claim.** For a predicate on Boolean words, its probability on uniformly random words of length $n+1$ is the average of its probabilities on length-$n$ words prefixed by true and by false.

**Proof.** Partition the length-$(n+1)$ words into the disjoint classes according to whether their first bit is true or false. Within either class, the event is determined by the remaining $n$ bits, so the product rule for word events (`Randomized.randProb_split`) says that the probability of that class together with the event is $1/2$ times the probability for the corresponding prefixed predicate. The two classes are disjoint, so their probabilities add (`Randomized.randProb_or_disjoint`). Their union is precisely the event in question, since every word has one of the two first bits; this identification preserves probability (`Randomized.randProb_congr`). Adding the two contributions gives the claimed average.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_one_eq`, `Randomized.randProb_split`, `Randomized.randProb_or_disjoint`.
