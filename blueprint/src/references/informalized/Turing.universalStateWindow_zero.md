<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalStateWindow_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Zero-Consumption State Window

**Claim.** For every natural number $n$, the state window with zero consumed cells and $n$ remaining cells equals the unary state tape encoding of $n$.

**Proof.** Compare the two tapes at an integer cell $z$. At $z=0$, both definitions give the blank symbol. If $z>0$, then $z$ is a natural cell index: the buffer tape reads the list consisting of one initial blank followed by $n$ true symbols. Its entry at index $z$ is true exactly when $z\le n$, and otherwise the list has no entry there. The state window gives true exactly when $0<z\le n$, which is the same condition. If $z<0$, the buffer tape has no value, and the state window also has no value because its interval requires $0<z$. The tapes therefore agree at every integer cell.
