<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.obliviousSourceMove_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary virtual heads when halted

**Claim.** If the selected state is absent, every virtual head direction is stationary, for every payload-read vector.

**Proof.** In the absent-state branch, the selected action has zero input movement and zero movement on every work tape. The virtual movement definition uses those work-tape movements directly, and its input component either retains the zero movement or clips it to zero. Thus every coordinate is stationary.
