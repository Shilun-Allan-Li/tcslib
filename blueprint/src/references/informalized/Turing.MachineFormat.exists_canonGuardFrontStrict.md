<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonGuardFrontStrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Guard-Checking Machine

**Claim.** For every machine format $F$, there is a finite Boolean-alphabet machine with at least four work tapes and an injectively indexed pair of exit states. It reaches the exit indexed by the guard decision within linear time, with the stated output, head position, and ready-tape contents, and it visits neither exit state earlier.

**Proof.** Take a machine that prepares the canonical ready words, and a guard-checking machine designed to start from those words. Join them by a seam: the first machine reaches its exit with the ready words in place, then the second runs from its entry state. The ready-word guard result provides the decision, time bound, empty output, required input-head position, and preservation of all tapes except tape 1. The seam-composition theorem identifies the combined run with this second-stage run after relabeling its states. For the strict first-visit condition, apply the seam-avoidance lemma: before the first stage exits, its states cannot be in the second-stage summand; after the handoff, the guard machine's own cut property excludes either target exit before the selected terminal time. Injectivity of the new exit map follows from the guard machine's distinct Boolean exit states. The two stage bounds combine into the stated linear bound.

**Key facts.** `Turing.MachineFormat.exists_canonReadySeam`, `Turing.MachineFormat.exists_canonGuardReady`, `Turing.seamCompTM_run_ofCfg`, `Turing.MachineFormat.canonSeam_avoids`.
