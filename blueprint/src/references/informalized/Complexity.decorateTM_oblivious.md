<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.decorateTM_oblivious -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Obliviousness under decoration

**Claim.** If the original machine emits no output and is oblivious, then its decorated machine is oblivious as well.

**Proof.** Fix equal-length inputs and a time. The exact projection of each decorated run onto the original schedule is the corresponding original run (Complexity.decorateTM_run). Thus the projected input-head positions agree by the original machine's obliviousness. For a work-tape index belonging to the original machine, its position is exactly the corresponding projected position, so those positions agree too. For an extra-tape index, the extra head position in each run equals the designated original head position in that run (Complexity.decorateTM_heads). The original designated-head positions agree by obliviousness, hence so do the extra-head positions. Since every work tape is either original or extra, all required positions agree.

**Key facts.** `Complexity.decorateTM_run`, `Complexity.decorateTM_heads`.
