<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.randProb_choiceVerifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice Verification and Output Probability

**Claim.** Under the stated verification and halting hypotheses, the probability that a uniform length-$Q$ word $u$ makes $xu$ belong to $V$ equals the probability that the machine outputs $[\mathrm{true}]$ on a uniform length-$T$ choice word.

**Proof.** A uniform length-$Q$ word has a uniform prefix of length $T$: the probability of any predicate depending only on that prefix equals its probability on a uniform length-$T$ word (`Randomized.randProb_take`). It remains to identify the membership event with the event that the machine outputs $[\mathrm{true}]$ on this prefix. The indicator of membership equals true exactly when the word belongs to the language (`Randomized.indicator_eq_true_iff`). By the choice-to-output equivalence (`Randomized.append_mem_iff_outputWith_take`), membership of $xu$ is equivalent to the machine's output on the first $T$ choices being $[\mathrm{true}]$. Apply this equivalence to each length-$Q$ word, then use agreement of predicates on all such words to equate their probabilities (`Randomized.randProb_congr`). The result is precisely the output probability at length $T$.

**Key facts.** `Randomized.randProb_take`, `Randomized.indicator_eq_true_iff`, `Randomized.append_mem_iff_outputWith_take`, `Randomized.randProb_congr`.
