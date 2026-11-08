<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedClock_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Clock-Phase Step

**Claim.** If the timed interpreter's transition in control state $q$ is the specified administrative action whenever the clock tape is read at position $p$, then one step from the configuration with that control state and clock lane produces the same configuration with control state $q'$ and clock head at $p+d$.

**Proof.** In the clock-adjusted configuration, the clock head reads the buffer-tape symbol at position $p$. The transition hypothesis therefore identifies the interpreter's action as the administrative action entering $q'$, moving the clock by $d$, and making no writes or output. Applying this action leaves the input head fixed, leaves all tape contents unchanged, and changes the clock head from $p$ to $p+d$; every other head is unchanged as well. The input head is fixed under zero movement (`moveInputPos_zero`), so the resulting configuration is exactly the stated clock-adjusted configuration.

**Key facts.** `Turing.moveInputPos_zero`.
