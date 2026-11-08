<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_undo_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoration Step on Empty History

**Claim.** Starting the restoration machine at the checkpoint for $c$ with empty history, one step gives the completed restoration configuration for $c$ and $p$.

**Proof.** With empty history, the clock cell tested by the restoration machine is blank. The machine therefore takes its empty-history branch: it halts, makes no tape writes, and moves the clock and history heads one position to the right, from their checkpoint position $-1$ to $0$. The ordinary work-tape heads and input head do not move. Thus the tapes remain those of the empty-history checkpoint, the heads have the positions recorded in the completed restoration configuration, and the output remains empty. The input position is unchanged by zero movement (`Turing.moveInputPos_zero`), so the resulting configuration is exactly the claimed one.

**Key facts.** `Turing.moveInputPos_zero`.
