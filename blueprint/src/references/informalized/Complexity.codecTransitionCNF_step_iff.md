<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecTransitionCNF_step_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Formula Characterizes a Step

**Claim.** For configurations in the radius-$s$ window on the same input, the transition CNF evaluated on their encoded assignments is true exactly when the core and output summary of the one-step successor of the first configuration equal those of the second.

**Proof.** 1. The transition-formula evaluation theorem (\texttt{Complexity.codecTransitionCNF_eval}) turns truth of the CNF into truth of every gate, for every position, transition case, and encoded bit. The observation-step equivalence (\texttt{Complexity.codecObserve_step_iff}) identifies equality between the successor’s observed bits and the second configuration’s row bits with equality of their core and output summary.

2. Suppose every gate is true. Choose the position from the first configuration’s encoded input-head position and work-head codes, and choose the transition case given by its state, input symbol, and work-tape symbols. The guard specification (\texttt{Complexity.codecGuard_spec}) verifies that this choice satisfies the gate guard: the position codes recover the actual head positions, using (\texttt{Complexity.codec_posCode_eq_iff}) and the window hypothesis. Thus each gate forces the second row’s bit to equal the successor’s observed bit, by the expected-bit step identity (\texttt{Complexity.codecExpected_step}). This holds for every encoded bit, so the observed successor row agrees with the second row; the observation-step equivalence gives equality of core and output summary.

3. Conversely, assume the successor’s core and output summary equal those of the second configuration. Fix any position, case, and bit for which the guard holds. The expected-bit step identity says that the gate’s expected value is the successor’s observed bit. The assumed equality and the observation-step equivalence identify that bit with the second row’s bit, which is exactly the gate’s new-bit value under the induced assignment. Hence the gate is true. Since the position, case, and bit were arbitrary, every gate is true, and the transition-formula evaluation theorem gives truth of the CNF.

**Key facts.** `Complexity.codecTransitionCNF_eval`, `Complexity.codecObserve_step_iff`, `Complexity.codecGuard_spec`, `Complexity.codec_posCode_eq_iff`, `Complexity.codecExpected_step`.
