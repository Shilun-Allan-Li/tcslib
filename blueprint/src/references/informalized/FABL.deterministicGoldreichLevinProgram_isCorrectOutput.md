<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinProgram_isCorrectOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the deterministic Goldreich–Levin program

**Claim.** For a Boolean target whose Fourier 1-norm is at most the input bound, the deterministic Goldreich–Levin program returns a state satisfying the required correctness properties at its threshold.

**Proof.** Unfold the outer program and its costed execution. The execution’s output component is the output of the run-up-to program at the full input dimension: the execution theorem for this program identifies that component with the corresponding deterministic state (`DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinRunUpToProgram_fst`). The state correctness theorem then applies to the target under the assumed Fourier 1-norm bound and gives all the required output properties (`deterministicGoldreichLevinState_isCorrectOutput`).

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinRunUpToProgram_fst`, `FABL.deterministicGoldreichLevinState_isCorrectOutput`.
