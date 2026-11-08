<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.clr_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing a Binary Register

**Claim.** Starting with the binary representation of $n$ in a register at position zero, the prescribed rightward scan followed by the erasing run clears it and ends in the designated next state; throughout the run before termination, the head stays between $-1$ and the length of that representation.

**Proof.** Write $w$ for the binary representation of $n$. Apply the rightward-to-end run to the register in state $c_R$, starting at position zero. Its length parameter is $|w|$, so it reaches the end of the word in $|w|+1$ steps; at each earlier time the state remains $c_R$ and the head lies between zero and $|w|$ (`toEnd_run`). The resulting head position is $|w|-1$, and the register still contains $w$.

Apply the erasure run to this configuration. With prefix length $|w|$, it clears the register and reaches the next state with its head at zero after another $|w|+1$ steps (`clrE_run`). Since the empty binary representation is the representation of zero, this is the claimed terminal configuration (`Nat.zero_bits`). The run-composition law combines the two phases (`rrun_add`). For any earlier time, it lies either in the first phase, where the head bound follows from `toEnd_run`, or in the second phase, where `clrE_run` bounds the head between $-1$ and $|w|-1$. Both phases avoid oracle calls because their states satisfy the assumed non-call conditions.

**Key facts.** `Complexity.LogProg.toEnd_run`, `Complexity.LogProg.clrE_run`, `Complexity.LogProg.rrun_add`.
