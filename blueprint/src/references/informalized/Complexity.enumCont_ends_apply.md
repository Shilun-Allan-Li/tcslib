<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_ends_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Two-Ended Action

**Claim.** Applying the two-ended action changes the two end tapes at their current head position according to the optional writes, moves both heads by $d$, and changes the state to $q'$, while leaving the input-head position and output unchanged.

**Proof.** The input head does not move, since its displacement is zero (`Turing.moveInputPos_zero`). For each work tape, separate the two end tapes from the intervening tapes. At tape zero, a missing write leaves its contents unchanged, while a present write updates the cell at $h$ to the specified symbol or blank. The same reasoning applies to tape $L$. Because $L>0$, these are distinct tapes. Every intermediate tape receives no write and has zero displacement, so its contents and head position remain unchanged. In all cases the end heads move from $h$ to $h+d$; the state is $q'$, and the action produces no output. These componentwise equalities establish the claimed configuration equality.

**Key facts.** `Turing.moveInputPos_zero`.
