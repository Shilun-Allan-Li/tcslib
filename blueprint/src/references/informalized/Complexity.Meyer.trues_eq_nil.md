<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifier.lean :: Complexity.Meyer.trues_eq_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Empty Transducer Output

**Claim.** The output produced by the transducer that emits a true bit exactly when it reads a true bit is empty if and only if every bit of $u$ is false.

**Proof.** Induct on the input word. For the empty word, both the output and the corresponding all-false word are empty. For a word $b :: u'$, consider the two possible values of its first bit. If $b$ is true, the transducer emits a true bit, so its output cannot be empty; the word also cannot equal the all-false list of the same length. If $b$ is false, it emits nothing, and the output is empty exactly when the output on $u'$ is empty. By induction, this is equivalent to $u'$ being all false, which is exactly the condition that $b :: u'$ is all false.
