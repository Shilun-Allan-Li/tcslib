<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.polyTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending a Unary Tape

**Claim.** Writing $1$ at cell $q$ on the tape $\tau_q$ gives $\tau_{q+1}$.

**Proof.** Compare the tape functions at each integer cell $z$. At $z=q$, the update assigns the value $1$, which is exactly the value of $\tau_{q+1}$ there. At every other cell the update leaves the old value unchanged. For such $z$, the conditions $0\le z<q$ and $0\le z<q+1$ are equivalent, since the only newly included integer cell is $q$. Therefore the tape values agree at every cell, proving equality of the functions.
