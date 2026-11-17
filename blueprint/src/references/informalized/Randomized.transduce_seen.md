<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.transduce_seen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output from the all-true initial state

**Claim.** Starting the specified transducer in state true, its output on any finite binary word $l$ is the word of $|l|$ zeroes.

**Proof.** Induct on the input word. For the empty word, both the output and the zero word are empty. For a word $b::l$, the current state is true, so the transducer emits one zero, regardless of $b$. Its next state is $\mathrm{true}\lor\neg b=\mathrm{true}$. By the induction hypothesis, the remaining input $l$ then emits $|l|$ zeroes. Together these are $|l|+1$ zeroes, as required.
