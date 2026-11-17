<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_dec_inputPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-head position during decrement

**Claim.** For every Boolean input word, work-tape index, decrement-machine configuration, and time, the input-head position after that many steps equals its initial position.

**Proof.** Induct on the number of steps. At time zero the run is the initial configuration. For the successor step, the run equation expresses the new configuration as one machine transition from the configuration at the preceding time. If that configuration is halted, the machine leaves it unchanged. Otherwise the decrement transition has zero input-head movement (`decrementTM_tr_action`), and a zero movement leaves the input-head position unchanged (`moveInputPos_zero`). The induction hypothesis identifies the preceding position with the initial one, proving the result.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.decrementTM_tr_action`, `Turing.moveInputPos_zero`.
