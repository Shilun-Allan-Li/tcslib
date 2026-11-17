<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_Interpreter_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Interpreter Step

**Claim.** The first step from the interpreter’s entry configuration yields the evaluation configuration in the initial table-rewind phase, with the table cursor at $|T|-1$, the state tape encoding state $0$, and state cursor $1$.

**Proof.** The transition from the entry control installs markers on the first and fourth work tapes and sets the control to the initial rewind-table phase. The input movement is zero, so the input position remains $p$ (`Turing.moveInputPos_zero`). The first tape retains the table buffer, and the second tape is initialized with the state-tape marker at position $0$; the marker identity identifies the resulting tape with the encoding of state $0$ (`Turing.timedCut_install_marker`). The work-tape heads are then exactly at $|T|-1$ and $1$ on the first two tapes, with the base positions on the remaining tapes. The output is unchanged. Comparing these components gives the asserted evaluation configuration.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.timedCut_install_marker`.
