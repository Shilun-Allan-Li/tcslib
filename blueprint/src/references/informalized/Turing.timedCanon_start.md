<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCanon_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Canonizer Startup

**Claim.** After exactly $4|b|+3|\alpha|+8$ steps, the timed canonizer reaches the stated buffered second-phase configuration, with the canonizer initialized on $\alpha$, tag true, the prescribed input-head position, and buffer tapes holding $b$ with heads at $|b|$.

**Proof.** View the time as $(4|b|+2|\alpha|+6)+(|\alpha|+2)$ and use run addition (`runFrom_add`). The first summand is the timed prefix scan. The prefix remains live at every earlier time (`timedPrefix_live`), so the buffered first phase simulates that scan through its endpoint by `bufferedFirstCfg_run`. At the endpoint, `timedPrefix_complete` gives the completed prefix configuration, and the input-length identity (`timed_input_length`) verifies the stated head position. The prefix has halted there; therefore the first-phase rewind theorem (`bufferedFirstCfg_rewind`) applies. It says that after the output-length-plus-two rewind steps, the buffered composition enters its second phase on the first phase's output, with tag true and the same input position, tapes, and heads. The prefix output is $\alpha$, and its buffered tapes and heads are exactly the claimed copies of $b$ and positions $|b|$. Combining these identities gives the stated configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.bufferedFirstCfg_init`, `Turing.FinTM.bufferedFirstCfg_run`, `Turing.timedPrefix_live`, `Turing.timedPrefix_complete`, `Turing.FinTM.bufferedFirstCfg_rewind`, `Turing.timed_input_length`.
