<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitTM_tr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Behavior Under Tape Embedding

**Claim.** The embedded transition preserves the original input-head movement, output, and successor state evaluated using the symbols at the embedded tape indices; it gives each embedded tape the corresponding original action and assigns no write and zero movement to every unselected tape.

**Proof.** Evaluate the definition of the embedded transition: it applies the original transition to the work symbols read at indices $\iota(i)$, then distributes its action across the larger tape set. At an embedded index, `Turing.embedSlot_selected` identifies the slot with its original index, so the work-tape action is exactly the original one. At an index outside the image, `Turing.embedSlot_unselected` makes the slot empty, and the embedding rule supplies no write and zero movement. The input-head movement, output, and successor state are copied directly from the original action, giving the remaining equalities.

**Key facts.** `Turing.embedSlot_selected`, `Turing.embedSlot_unselected`.
