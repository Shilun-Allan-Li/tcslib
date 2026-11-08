<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalInterpreter_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpreter First Step

**Claim.** The interpreter’s first step from its entry configuration produces the evaluation configuration over the initialization base, with the initial table-rewind control, table cursor $|T|-1$, state tape encoding state index $0$, and state cursor $1$.

**Proof.** Compare the configurations component by component. The start transition leaves the input head fixed, since moving it by zero preserves its position (`moveInputPos_zero`). It also sets the control to the initial table-rewind phase and places the table head at the initial table position, which is $|T|-1$ under truncated subtraction. On the state tape, the transition installs a false marker at position $0$; this is exactly the state tape for index $0$. The remaining work tapes, their head positions, and the output agree with the initialization base and the stated evaluation configuration. Thus all configuration components coincide.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.universal_install_marker`.
