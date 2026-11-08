<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.exists_effectiveMachineCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effective Machine-Code Scheme

**Claim.** There exists a coding scheme for deterministic one-work-tape machines over the binary alphabet with a total decoder, stable under appending any finite number of true bits to an encoding, and with a finite binary Turing machine and time bound computing the fixed serialization of the decoded machine on every binary string.

**Proof.** Take the canonicalizer machine and its time bound supplied by `codeCanonical_machine`; that machine computes the serialization of the decoded code on every binary input. Choose `CodeTM.serialize` as the encoding and `codeDecode` as the total decoder. The padding identity `codeDecode_serialize_pad` says that decoding the serialization of any machine, followed by any finite string of true bits, recovers that machine. These choices satisfy each component of the definition of an effective machine-code scheme, and packaging them with the canonicalizer and its computation proof gives the required object.

**Key facts.** `Turing.codeCanonical_machine`, `Turing.codeDecode_serialize_pad`.
