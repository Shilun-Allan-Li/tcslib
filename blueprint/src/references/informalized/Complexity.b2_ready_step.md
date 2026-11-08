<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_ready_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Leftward Assembly-Rewind Step

**Claim.** When $j<|y|$, one host step from the assembly-rewind configuration at cell $j$ moves the assembly head to cell $j-1$ and leaves the rest of the configuration unchanged.

**Proof.** At cell $j$, the assembly tape contains $y[j]$ because $j<|y|$. Thus the host is in the rewind case where the assembly cell is occupied. Its transition leaves the machine in the rewind state, makes no changes to any tape contents or outputs, and moves the assembly head one cell to the left. The input head does not move, by the fact that a zero input movement preserves its position (`Turing.moveInputPos_zero`). The resulting state, tapes, heads, and output are therefore exactly those of the rewind configuration with assembly head at $j-1$.

**Key facts.** `Turing.moveInputPos_zero`.
