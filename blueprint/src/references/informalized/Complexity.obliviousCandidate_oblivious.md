<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.obliviousCandidate_oblivious -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Obliviousness of the candidate

**Claim.** For any two binary inputs of equal length and any time $t$, the candidate has equal input-head positions and equal work-tape head positions on the two runs.

**Proof.** The candidate is the parallel encoding of a decorated version of the schedule machine. The preservation theorem for parallel simulation (`parallelTM_oblivious`) says that parallel encoding preserves obliviousness, so it remains to establish obliviousness for the decorated schedule. The decoration theorem (`decorateTM_oblivious`) says that decorating a machine preserves obliviousness when its transitions emit no output and the underlying machine is oblivious. The schedule transitions emit no output by `obliviousSchedule_output`, and the schedule is oblivious by `obliviousSchedule_oblivious`. Applying these facts gives the required obliviousness of the candidate.

**Key facts.** `Complexity.parallelTM_oblivious`, `Complexity.decorateTM_oblivious`, `Complexity.obliviousSchedule_output`, `Complexity.obliviousSchedule_oblivious`.
