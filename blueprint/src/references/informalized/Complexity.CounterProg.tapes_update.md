<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.tapes_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Unary Tape Vector

**Claim.** Replacing tape $t$ in the vector of unary tapes encoding $\rho$ by the unary tape encoding $m$ gives the vector of unary tapes encoding the assignment obtained by replacing $\rho(t)$ by $m$.

**Proof.** To show that the two tape vectors are equal, compare their values at an arbitrary register $i$. If $i=t$, both sides give the unary tape encoding $m$. If $i\ne t$, the update leaves the original entry unchanged on both sides, so both give the unary tape encoding $\rho(i)$. Thus the vectors agree at every register.
