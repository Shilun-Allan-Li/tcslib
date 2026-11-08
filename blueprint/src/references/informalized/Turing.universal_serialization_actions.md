<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_serialization_actions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization by Header and Action Groups

**Claim.** For every machine in code normal form, its canonical serialization is its header followed by the concatenation, in increasing state order, of the serialized transition records for that state's nine actions, with input read varying slowest and work read varying fastest.

**Proof.** Expand the canonical serialization and separate the initial-state unary code from the transition table. For each state, input symbol, and work symbol, the machine has one work tape, so its work-tape action is determined by its value at tape index $0$. Consequently the serialized action fields agree with the corresponding record bits. This is checked by considering the possible head movements, write options, output options, and next-state options, which are precisely the cases in the definitions of the encodings. The remaining nested list traversals enumerate states first, then input symbols, then work symbols; flattening them therefore gives the stated groups of nine records after the header.
