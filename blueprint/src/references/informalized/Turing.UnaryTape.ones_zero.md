<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UnaryTape.lean :: Turing.UnaryTape.ones_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary tape of zero

**Claim.** The unary tape associated with $0$ is blank at every integer cell.

**Proof.** Fix an integer cell $c$. For the tape of zero to contain a symbol, its defining condition would require $0\le c<0$, which is impossible. Thus the value at every cell is `none`, proving equality with the everywhere-blank tape.
