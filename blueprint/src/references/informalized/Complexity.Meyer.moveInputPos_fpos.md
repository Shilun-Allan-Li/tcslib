<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.moveInputPos_fpos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Movement of an Input Position

**Claim.** If $p\le |y|$, then moving the virtual input-head position corresponding to $p$ one step to the right gives the position corresponding to $p+1$.

**Proof.** Since $p\le |y|$, the position $p$ is strictly less than the right boundary $|y|+1$. The position represented by `fpos y p` is therefore $p$, and it is not at that boundary. The right-movement fact `Turing.moveInputPos_pos_of_ne_right` consequently identifies the moved position with $p+1$. Because $p+1\le |y|+1$, the position `fpos y (p+1)` also represents exactly $p+1$. The two virtual positions are equal.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`.
