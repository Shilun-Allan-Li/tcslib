<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Marker Installation

**Claim.** For every Boolean input word, running the transducer for two steps from its initial configuration reaches state $2$ with the input head at the start, both work heads at cell $0$, empty output, a blank first tape, and a second tape carrying only the false marker at offset $-1$.

**Proof.** First identify the initial configuration with the canonical frame in state $0$, with input position index $0$, counter length $0$, both heads at $0$, and the second tape blank. The counter of length zero is everywhere blank, since it is the buffer of an empty replicated word. In state $0$, the machine makes a zero input move, leaves both tapes and output unchanged, moves the second head left, and enters state $1$; this frame transition follows from `Complexity.satRed_move` and the zero-move identity (`Turing.moveInputPos_zero`). In state $1$, it writes false at the second head's location $-1$, moves that head right to $0$, and enters state $2$. The empty-buffer identity (`Complexity.satRedBuffer_empty`) identifies the resulting tape as blank except for the false marker at $-1$, and `Complexity.satRedAction_apply` gives the resulting canonical frame. Combining the two transitions with the one-step run identity (`Complexity.satRed_one`) and the successor decomposition of runs (`Turing.MultiTapeTM.runFrom_succ_eq_step`) proves the stated two-step result.

**Key facts.** `Complexity.satRedAction_apply`, `Complexity.satRedBuffer_empty`, `Complexity.satRed_move`, `Complexity.satRed_one`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`.
