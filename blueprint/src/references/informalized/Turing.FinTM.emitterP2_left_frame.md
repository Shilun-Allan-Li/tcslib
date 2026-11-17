<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_left_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left-Bank Configuration Frame

**Claim.** Embedding the specified seam configuration into the host layout, with the left-bank tapes selected and the other tapes supplied by the ambient layout, and mapping its state by $e$, gives the stated canonical seam configuration.

**Proof.** Apply the framed configuration embedding with the left-bank index map. On each selected slot, the embedded tape and head are those of the source configuration; unfolding the left-bank indexing and the word layout shows they are the corresponding canonical host data. On an unselected slot, split the host index into the initial candidate slot or one of the two banks. The candidate slot retains the candidate word, the unselected slots of the left bank carry empty words, and the suffix bank carries the prescribed word $v$; all head positions are zero. These are precisely the ambient contents and heads in the target configuration. The states, input positions, and outputs agree directly, so the framing result yields the equality.

**Key facts.** `Turing.FinTM.emitterP2_frame`.
