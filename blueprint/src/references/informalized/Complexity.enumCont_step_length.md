<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_step_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length After a Stalled Increment

**Claim.** For every finite Boolean word $s$, applying the fixed-width increment to $s$, and using $s$ itself if the increment overflows, preserves the length of $s$.

**Proof.** The fixed-width increment agrees with the ordinary increment procedure on Boolean words (`Complexity.enumCont_inc_eq`). If that procedure returns no word, the fallback is $s$ itself, so the length is unchanged. If it returns a word $u$, the increment specification says that $u$ has the same length as $s$ (`Complexity.enumInc_spec`), which gives the result in this case as well.

**Key facts.** `Complexity.enumCont_inc_eq`, `Complexity.enumInc_spec`.
