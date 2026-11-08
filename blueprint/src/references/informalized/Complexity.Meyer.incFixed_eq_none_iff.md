<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.incFixed_eq_none_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow of fixed-width increment

**Claim.** A finite Boolean word overflows under fixed-width increment exactly when all of its bits are true.

**Proof.** Induct on the word. The empty word has increment result `none`, and it is also the all-true word of length zero. For a nonempty word, if its first bit is false, increment immediately returns a word, so it does not overflow; the word is not all true either. If the first bit is true, increment overflows exactly when incrementing the tail overflows. By the induction hypothesis this happens exactly when the tail consists entirely of true bits. Prepending the true first bit says precisely that the whole word is the all-true word of its length.
