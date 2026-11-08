<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelTM_oblivious -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Obliviousness under transverse coding

**Claim.** If the original machine has identical input-head and work-tape head positions at every time on any two equal-length inputs, then its transverse binary realization has the same property on equal-length binary inputs.

**Proof.** Take binary inputs $x,y$ of equal length and a time $t$. Their symbolwise images have equal length, so obliviousness of the original machine gives equality of its input-head positions and equality of its work-tape head-position functions at time $t$. The configuration correspondence (`Complexity.parallelTM_run`) identifies each encoded run with the transverse encoding of the corresponding original run. The encoding preserves the input-head position, giving the required equality. For a work-tape index in the transverse machine, decode it as a pair consisting of an original tape and an alphabet symbol. Its head position is precisely the position of that original tape, independent of the symbol component. Equality of the original head-position functions therefore gives equality at every transverse index.

**Key facts.** `Complexity.parallelTM_run`.
