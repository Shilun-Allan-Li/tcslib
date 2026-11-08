<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.scan_adv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Advancing Writer Run

**Claim.** For every r at most the length of w, running the advancing writer for r steps from a configuration in state 0 gives the configuration specified by the advancing scan construction at r.

**Proof.** Fix r≤|w| and induct on r. At r=0, no transition has occurred, and the advancing scan configuration at parameter zero agrees with the initial configuration: its state is 0, its head has not moved, and the written interval is empty. For the successor case, the induction hypothesis identifies the run after r steps with the scan configuration at r. The run-after-one-more-step law expresses the next run as one machine transition (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). Since r<|w|, the writer's transition writes w[r], advances the selected tape head, and changes the state index from r to r+1. The general scan-write step lemma verifies that this transition takes the parameter-r configuration to the parameter-(r+1) configuration (`Turing.scan_write_step`). The input head remains fixed because its movement is zero (`Turing.moveInputPos_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.scan_write_step`, `Turing.moveInputPos_zero`.
