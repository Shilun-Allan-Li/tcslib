<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.timeout_fail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timeout failure transition

**Claim.** If the run configuration at clock value $m$ does not encode a halted machine with a one-symbol output, then the host step enters phase $p_0$ with clock head at $m-1$ when looping is enabled, and otherwise halts with clock head at $m$, preserving the other stated configuration data.

**Proof.** The run configuration has phase equal to the run phase with the encoded state and captured output. Its clock head scans cell $m$, which is blank because the yardstick has length $m$. The host transition therefore follows the blank-clock branch. If the machine state is absent and the captured output encodes one Boolean symbol, the output-capture correspondence says the original output is that singleton, contrary to the failure hypothesis. In all remaining cases the transition selects the timeout-failure action: when looping is enabled it enters phase $p_0$ and moves the clock head left; otherwise it halts and leaves the clock head in place. Applying this action preserves the input position, work tapes, and work-head positions, leaves the yardstick unchanged, and keeps output empty, giving the two asserted configurations.

**Key facts.** `Turing.NDTM.stepWith_of_state`, `Turing.capOf_eq_some_some`, `Turing.ClockHost.apply_hostCfg`.
