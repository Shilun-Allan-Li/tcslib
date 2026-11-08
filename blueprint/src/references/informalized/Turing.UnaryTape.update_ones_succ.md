<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UnaryTape.lean :: Turing.UnaryTape.update_ones_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adding a Unary Cell

**Claim.** For every natural number $m$, changing cell $m$ of the unary tape for $m$ to $1$ and leaving all other cells unchanged gives the unary tape for $m+1$.

**Proof.** Compare the two tapes at an arbitrary integer cell $c$. If $c=m$, the original tape is blank there, and the update sets the value to $1$; this is exactly the value of the tape for $m+1$, since $0\le m<m+1$. If $c\ne m$, the update preserves the original value. Away from this boundary, the defining ranges for the tapes of lengths $m$ and $m+1$ agree: cells below $m$ contain $1$, while all other cells distinct from $m$ are blank. Hence the tapes agree at every cell.
