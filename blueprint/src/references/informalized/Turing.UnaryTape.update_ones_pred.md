<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UnaryTape.lean :: Turing.UnaryTape.update_ones_pred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Last Unary Cell

**Claim.** For every natural number $j$, changing cell $j$ of the unary tape for $j+1$ to blank and leaving all other cells unchanged gives the unary tape for $j$.

**Proof.** Compare the two tapes at an arbitrary integer cell $c$. The update changes the value only when $c=j$. At that cell, the tape for $j+1$ contains $1$, since $0\le j<j+1$, and replacing it by blank agrees with the tape for $j$, which is blank there. At every other cell, the update leaves the original value unchanged. The conditions defining the two unary tapes differ only at the boundary cell $j$: below that boundary both contain $1$, and at or beyond it both are blank. Thus the values agree at every cell, so the tapes are equal.
