<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_probe_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Boundary Probe Run

**Claim.** Starting in the probe's start state on a nonempty input, the machine reaches a done state within two steps, with a flag identifying whether the initial head was at the right boundary and with the specified returned head position; its work-tape heads do not move, and no done state occurs earlier.

**Proof.** The probe uses only input-head moves, so its work-tape contents and head positions are fixed throughout the run by the native-frame result ( `recordStep_native_frame` ). Split according to whether the initial input symbol is blank. If it is not blank, the blank-position characterization ( `recordStep_input_blank` ) shows that the head is at neither boundary. The start transition therefore leaves the head in place and enters the done state with flag false. The zero-movement identity ( `moveInputPos_zero` ) gives the endpoint position, and the start state at time zero is not done.

If the scanned symbol is blank, the same characterization says that the head is at the left boundary or the right boundary. The start transition moves one step right into the peek state. On a nonempty input, from the left boundary this lands on the first input symbol, as guaranteed by `inputSymbolInner`; from the right boundary, the right-boundary movement identity ( `moveInputPos_rightBoundary` ) keeps the head at that boundary. The peek transition then moves left and enters done, setting its flag according to whether the symbol it sees is blank. In the left-boundary case it sees the first input symbol, so the flag is false and the head returns to position zero, using the negative-movement formula ( `moveInputPos_neg_val` ). In the right-boundary case it still sees a blank, so the flag is true and the head returns to position $|x|$. The start and peek states are not done, proving the required earlier-time condition. This branch takes two steps, while the nonblank branch takes one.

**Key facts.** `Turing.recordStep_native_frame`, `Turing.recordStep_input_blank`, `Turing.moveInputPos_zero`, `Turing.inputSymbolInner`, `Turing.moveInputPos_rightBoundary`, `Turing.moveInputPos_neg_val`.
