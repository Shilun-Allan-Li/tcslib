<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_header_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Header length within the serialization

**Claim.** For every machine $M$ in code normal form, twice the number of bits in the binary representation of its state-count parameter, plus $2$, plus its initial state index, plus $1$, is at most the length of its canonical serialization.

**Proof.** The serialization-header identity expresses the serialization as the pair encoding of the binary state-count word and a second component beginning with the unary representation of the initial state index followed by a delimiter (`universal_serialization_header`). The pair-encoding length is twice the length of its first component, plus two delimiter bits, plus the length of its second component (`universal_pair_length`). The unary initial-state prefix and delimiter contribute at least $q_0+1$ bits. Combining these lengths gives the stated lower bound.

**Key facts.** `Turing.universal_serialization_header`, `Turing.universal_pair_length`.
