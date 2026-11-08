<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_copy_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition from Copy to Rewind

**Claim.** From the end-of-copy configuration, one step reaches state $1$ with the input head at position $|x|$, while the work tape, work-head position, and empty output remain unchanged.

**Proof.** At input-head position $|x|+1$, the head is at the right-end marker, so the machine reads no input symbol. Its transition from state $0$ therefore changes to state $1$ and moves the input head one position left. The head is not at the left boundary, so this move lands at position $|x|$; this is the content of the left-move position rule (`moveInputPos_neg_of_ne_left`). The transition makes no work-tape write or work-head movement and emits no output. Hence those components remain as stated.

**Key facts.** `Turing.moveInputPos_neg_of_ne_left`.
