<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDiag_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanned Symbol at the Right Boundary

**Claim.** For every bit string $x$, optional control state $q$ among the six states or the halting state, and output string $w$, a configuration whose input head is at the right boundary, position $|x|+1$, scans no symbol.

**Proof.** At the right boundary the input-symbol definition returns no symbol: its second boundary condition holds when the head position is $|x|+1$. Unfolding the displayed configuration and this definition therefore gives the claimed value.
