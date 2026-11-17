<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.decorateTM_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extra tape head positions

**Claim.** At every time, each extra tape head in the decorated machine is at the same position as the designated work tape head.

**Proof.** Induct on the time. At time zero, all work-tape heads start at position zero. For the successor step, express the run as one step from the preceding configuration and split according to whether that configuration has halted. If it has halted, the machine stays at that configuration, so the induction hypothesis applies unchanged. Otherwise, the decorated transition assigns every extra tape the same movement as the designated original head. Both positions are therefore incremented by the same amount, and their equality is preserved.
