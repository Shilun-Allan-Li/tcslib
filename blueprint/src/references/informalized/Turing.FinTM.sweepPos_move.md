<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepPos_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Movement Commutes with Position Transport

**Claim.** Transporting an input-head position after moving it in any direction gives the same result as moving the transported position in that direction.

**Proof.** The transport preserves the position’s numerical value, and the mapped input has the same length as the original input. By the definition of bounded head movement, moving a position adds the direction to its value and then keeps it if it remains within the allowed range, otherwise clamping it to the rightmost position. Since both the value and the allowed range are preserved by transport, the two orders of transport and movement yield the same position.
