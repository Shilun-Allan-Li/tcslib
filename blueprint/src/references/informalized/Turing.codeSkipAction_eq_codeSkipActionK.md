<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeSkipAction_eq_codeSkipActionK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalence of transition readers

**Claim.** For every natural number $n$ and Boolean string $xs$, the transition-record reader checking four consecutive two-bit fields and then a successor-state field returns the same result as the reader checking the first field, skipping one work-field pair, checking the next field, and then checking the successor-state field.

**Proof.** The reader that repeats the work-field check once has exactly the effect of a single work-field check: for every input list, one repetition either fails if that check fails, or returns the same remainder if it succeeds. With this observation, expand both transition readers. The first checks the initial field, then the two checks that constitute one work-field pair, then the next field and the successor-state field. The second checks the initial field, performs the one work-field repetition, and then checks the same next field and successor-state field. Their stages and validity conditions coincide, so their results agree for every input.
