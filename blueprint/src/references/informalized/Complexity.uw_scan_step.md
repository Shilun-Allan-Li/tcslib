<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_scan_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One step of the unary scan

**Claim.** When the input bit at position $j$ is true, one step from the scan configuration at position $j$ with buffer $u$, using choice $b$, gives the scan configuration at position $j+1$ with buffer $u$ followed by $b$.

**Proof.** The scan configuration is in state $0$, which is not the query state. Thus the step is the ordinary transition action (`uw_step_scan`). The input head reads the bit at position $j$, namely true, by the input-symbol identification (`Turing.inputSymbolInner`), so the machine’s scan transition advances the input head. Its input-head move sends position $j+1$ in the shifted indexing to the next position, as guaranteed by `Turing.moveInputPos_pos_of_ne_right`. On the buffer tape, writing the choice bit at the end of the length-$j$ buffer changes its contents from $u$ to $u$ followed by $b$ (`Turing.FinTM.bufferTape_append`); the hypothesis $|u|=j$ places the write at the current work-head position. The work-head position advances accordingly, while the state remains the scan state and the output stays empty. These fieldwise agreements give the claimed scan configuration.

**Key facts.** `Complexity.uw_step_scan`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
