<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Codes2Tape.lean :: Turing.exists_effectiveMachineCode2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Tape Effective Machine-Code Scheme

**Claim.** There exists a coding scheme for deterministic two-work-tape machines over the binary alphabet with a total decoder, stable under appending any finite number of true bits to an encoding, and with a finite binary Turing machine and time bound computing the fixed serialization of the decoded machine on every binary string.

**Proof.** The construction uses the two-tape code format with `Code2TM.serialize` as its serialization and `zfBDecode` as its decoder. First, `codePrimSkipTable2` establishes that the two-tape format's skip-table operation is primitive recursive. The format's canonizer theorem then supplies a finite binary Turing machine and time bound computing the serialization of the decoded input. The format's padding theorem says that decoding a serialized machine followed by any finite number of true bits returns that machine. Combining this encoding, decoder, padding property, and canonizer with its computation proof yields the required effective scheme.

**Key facts.** `Turing.codePrimSkipTable2`, `Turing.CodeFormat.exists_canonizer`, `Turing.CodeFormat.decode_serialize_pad`.
