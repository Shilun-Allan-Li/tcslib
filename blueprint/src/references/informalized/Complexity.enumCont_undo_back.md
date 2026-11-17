<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_undo_back -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Restoration Transition

**Claim.** Starting the restoration machine at the checkpoint for the configuration obtained by applying $a$ to $c$, with history $h$ extended by the entry recording the symbols under the work heads of $c$ and the work-head moves prescribed by $a$, one step gives the intermediate restoration configuration for $c$, $a$, $h$, and $p$.

**Proof.** The appended history entry makes the clock cell at the current history position nonblank, so the restoration machine takes its branch for a nonempty history. The checkpoint’s encoded symbol histories give back the symbols under the heads of $c$, while its encoded move histories give the move codes prescribed by $a$. The transition therefore records those symbols in its state, clears the just-consumed history and clock cells, and moves the work heads in the directions that undo the recorded moves. Clearing the final sparse history cell uses the fact that blanking the last encoded cell recovers the encoding with that cell removed (`Complexity.enumCont_sparse_erase`); the clock tape is shortened in the same way (`Complexity.enumCont_clock_erase`). The move codes decode to the opposite signed displacements (`Complexity.enumCont_unmove_cast`), and the input head stays at $p$ because a zero input movement leaves its position fixed (`Turing.moveInputPos_zero`). These are precisely the state, tapes, and head positions of the stated intermediate restoration configuration.

**Key facts.** `Complexity.enumCont_clock_erase`, `Complexity.enumCont_sparse_erase`, `Complexity.enumCont_unmove_cast`, `Turing.moveInputPos_zero`.
