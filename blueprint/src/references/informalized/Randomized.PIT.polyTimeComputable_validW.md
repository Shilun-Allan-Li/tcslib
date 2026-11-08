<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.polyTimeComputable_validW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Encoding Validity

**Claim.** The Boolean function that returns the validity result of a bit string as a one-bit string is computable in polynomial time.

**Proof.** The validity predicate is the conjunction of three conditions: the input contains a false bit, the scan run passes its run-validity check, and the index component of that scan run is nonempty. The false-bit test is polynomial-time computable. The run-validity check on the scan run is polynomial-time computable by composing the run-validity procedure with the scan-run procedure. Likewise, compose the scan-run procedure with index extraction and the empty-string test to obtain the third condition. Polynomial-time conjunction combines the first two conditions and then combines their result with the negation of the third condition. This gives the required one-bit output.

**Key facts.** `Randomized.PIT.polyTimeComputable_runOk`, `Randomized.PIT.polyTimeComputable_scanRun`, `Randomized.PIT.polyTimeComputable_sI`, `Complexity.polyTimeComputable_isNil`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.polyTimeComputable_hasFalse`, `Complexity.polyTimeComputable_and`, `Complexity.polyTimeComputable_not`.
