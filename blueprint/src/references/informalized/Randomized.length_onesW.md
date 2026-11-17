<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.length_onesW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the True-Bit Output

**Claim.** For every Boolean word, the word formed by deleting its false bits has length equal to the number of true bits in the original word.

**Proof.** Induct on the word. For the empty word, both quantities are zero. For a word with leading bit `b` and tail `w`, the output consists of the output contributed by `b` followed by the output from `w`: the leading contribution has length one if `b` is true and zero otherwise. The true-bit count obeys the same recurrence, adding one exactly when `b` is true. The induction hypothesis equates the tail quantities, so the lengths agree.
