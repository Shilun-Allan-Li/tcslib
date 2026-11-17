<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.rep_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Initial Round Configuration

**Claim.** If the enlarged configuration represents $c$ and is in the entry control state, then it equals the entry state applied to the round configuration built from $c$, its transition table, its output summary, the unary word for its state, zero table and state head positions, and the enlarged configuration's output list.

**Proof.** Unpack the representation conditions. The state hypothesis on $c$ identifies the stored state word with the unary encoding of $q$, so the summary-tape contents in the representation are exactly the required summary and state word. Now compare configurations component by component. Their input positions agree by the representation; their first $k$ tapes and head positions agree by its bank condition; the table and summary tapes agree by the table and summary conditions; and both auxiliary head positions are zero. The entry-state hypothesis gives equality of the states, while the output lists agree by construction. Extensionality of configurations yields the claimed equality.
