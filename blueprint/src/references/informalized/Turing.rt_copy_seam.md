<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_copy_seam -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential composition across a state seam

**Claim.** When the first machine reaches its designated exit state for the first time, the seam-composed machine takes one transition into the second machine, then follows its run; the endpoint, first-return property, and head-radius bound follow.

**Proof.** The first machine reaches configuration $b$ at time $t_1$ in state $q_1$, with no earlier visit to $q_1$. The seam-composition run theorem (`seamCompTM_run_ofCfg`) says that the composed machine follows this first run, takes one transition across the seam into the renamed entry state, and then follows the second machine for $t_2$ steps. Thus at time $t_1+1+t_2$ it is the second machine’s endpoint with states renamed into the right summand. The first-return theorem (`seamCompTM_firstReturn_ofCfg`) ensures that the target state in the right summand was not reached at any earlier time: before the seam the state is in the left summand, and during the second segment the assumed first-return condition applies. For the radius bound, every head position visited in the composed run through the endpoint belongs to the union of the positions visited during the first run and those visited during the second run. This is the visited-head inclusion (`seamCompTM_visitedByTapeHead_ofCfg`). Each member of that union satisfies the common radius bound by the corresponding hypothesis, so the bound holds throughout.

**Key facts.** `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`, `Turing.seamCompTM_visitedByTapeHead_ofCfg`.
