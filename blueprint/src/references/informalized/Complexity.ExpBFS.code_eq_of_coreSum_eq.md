<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.code_eq_of_coreSum_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code Determined by Core Data and Output Summary

**Claim.** If two configurations have the same state, input-head position, work-tape contents, and work-tape-head positions, and their output summaries agree, then their codes for window size $s$ are equal.

**Proof.** The tuple of core data together with the output summary determines the encoded configuration word. The hypothesis says these tuples agree, so the words agree by the configuration-word congruence theorem (\texttt{cfgWord\_congr}). Since the configuration code is obtained by applying the same binary-value map to each word, the codes are equal.

**Key facts.** `Complexity.Codec.cfgWord_congr`.
