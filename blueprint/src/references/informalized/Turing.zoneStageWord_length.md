<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStageWord_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Encoded Zone Word

**Claim.** For either encoding order, the stage word of a finite list of optional Boolean values has length twice the length of the list.

**Proof.** Induct on the list. The empty list encodes to an empty word. For a nonempty list, each optional value contributes exactly two Boolean entries, and the encoding of the tail has twice the tail's length by induction. Adding these lengths gives twice the length of the original list.
