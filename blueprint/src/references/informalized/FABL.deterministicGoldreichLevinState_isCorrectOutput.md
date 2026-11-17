<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinState_isCorrectOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Goldreich–Levin Output

**Claim.** Under the Fourier $1$-norm bound, the state after $n$ stages has an active family that contains every frequency with coefficient magnitude at least the threshold, contains only frequencies with coefficient magnitude greater than half the threshold, and satisfies both stated cardinality bounds.

**Proof.** Apply the state specification at stage $n$, which is permitted because $n\le n$. It supplies an active family recorded in the state, the active-family invariant, and the cap on its cardinality. The invariant’s completeness clause places every frequency whose Fourier coefficient has magnitude at least the threshold in the family; its soundness clause gives the strict half-threshold lower bound for each member. The active-family cardinality bound supplies the remaining numerical estimate. Together these are precisely the required output properties.

**Key facts.** `FABL.deterministicGoldreichLevinState_spec`, `FABL.goldreichLevinActiveInvariant_complete`, `FABL.goldreichLevinActiveInvariant_sound`, `FABL.goldreichLevinActiveInvariant_card_le`.
