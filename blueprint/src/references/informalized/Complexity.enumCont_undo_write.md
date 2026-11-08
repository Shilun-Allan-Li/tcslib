<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_undo_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoration of the Source Configuration

**Claim.** For a configuration $c$, one-step action $a$, history $h$, and input-head position $p$, one step of the restoration machine from the intermediate restoration configuration determined by $c,a,h,p$ gives exactly the restoration checkpoint configuration determined by $c,h,p$.

**Proof.** In the intermediate configuration, the restoration machine’s state contains the symbols that were under the work heads of $c$. Its transition writes those saved symbols back at the current head positions. On each ordinary work tape, this update restores the original tape exactly (`Complexity.enumCont_restore_cell`). The history tapes are left unchanged, while the clock and history head positions are shifted back by the amounts recorded in the move history. The input head has zero movement and therefore stays at $p$ (`Turing.moveInputPos_zero`). The transition also returns to the checkpoint state and leaves the output empty. These components are exactly those of the restoration checkpoint configuration for $c$ and $h$.

**Key facts.** `Complexity.enumCont_restore_cell`, `Turing.moveInputPos_zero`.
