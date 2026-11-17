<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPolyTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending a Unary Tape

**Claim.** Writing a true bit at cell $q$ of the unary tape of length $q$ produces the unary tape of length $q+1$.

**Proof.** Check the tape contents at each integer cell $z$. At $z=q$, the update writes `some true`, and this is exactly the value assigned there by the unary tape of length $q+1$. At every other cell, the update leaves the old value unchanged. The conditions $0\le z<q$ and $0\le z<q+1$ agree away from $z=q$, so the old and new tape values coincide at those cells as well. Therefore the two tape functions are equal.
