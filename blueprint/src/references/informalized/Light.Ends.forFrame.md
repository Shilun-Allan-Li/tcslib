<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.forFrame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# For-Loop on a Framed Local List

**Claim.** Under the stated invariant, round, terminal, bound, word-limit, and cost assumptions, the for-loop from the framed local list terminates within cost $T$ in a state satisfying $Q$.

**Proof.** Use the memory-invariant loop theorem (`Light.Ends.forMem`) with local store given by the frame of $l$. Its hypotheses ask for states whose local store is obtained by updating position $i$ in that frame. The identity relating an update of a frame to framing the updated list (`Light.update_frame_setLocal`) identifies each such store with the frame of `setLocal l i j`. Rewriting by this identity turns the supplied round, terminal, and bound assumptions into exactly the hypotheses required by the memory-invariant theorem. The initial invariant, word bound, and cost estimate are already assumed, so its conclusion gives the stated termination and postcondition.

**Key facts.** `Light.Ends.forMem`, `Light.update_frame_setLocal`.
