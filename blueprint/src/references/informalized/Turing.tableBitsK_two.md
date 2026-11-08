<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.tableBitsK_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Tape Table Serialization

**Claim.** For a transition table acting on two Boolean work tapes, serializing its actions by enumerating each work-tape read separately gives the same list as the two-tape table encoding using the corresponding pair of reads.

**Proof.** Expand both table encodings. The enumeration of two-tape read configurations is exactly the nested enumeration of the three possible optional symbols on the first tape and the three possible optional symbols on the second, paired into a two-coordinate read function (`Turing.workReadsK_two`). Substituting this enumeration into the general serialization turns its nested concatenations into the same ordered sequence of states, input reads, and work-tape read pairs used by the two-tape encoding. Each entry therefore contributes the same action bits in the same position, so the lists agree.

**Key facts.** `Turing.workReadsK_two`.
