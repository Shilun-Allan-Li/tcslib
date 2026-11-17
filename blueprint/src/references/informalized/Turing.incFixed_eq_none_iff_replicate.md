<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Convention.lean :: Turing.incFixed_eq_none_iff_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overflow of Fixed-Width Increment

**Claim.** For every finite Boolean word $u$, fixed-width increment overflows exactly when $u$ consists entirely of true entries.

**Proof.** Induct on the word. The empty word overflows, and it is also the replicate of length zero. For a word beginning with false, increment immediately returns a word, so overflow is false; the word is not all true either. For a word beginning with true, increment overflows exactly when it overflows on the tail. By induction this is equivalent to the tail being all true, which is equivalent to the whole word being all true.
