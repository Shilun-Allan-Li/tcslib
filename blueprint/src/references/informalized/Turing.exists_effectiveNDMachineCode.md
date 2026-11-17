<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/NDCodes.lean :: Turing.exists_effectiveNDMachineCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic Effective Machine-Code Scheme

**Claim.** There exists a coding scheme for nondeterministic two-work-tape machines over the binary alphabet with a total decoder, stable under appending any finite number of true bits to an encoding, and with a finite binary Turing machine and time bound computing the fixed serialization of the decoded machine on every binary string.

**Proof.** The nondeterministic format's skip table is obtained by repeating the deterministic two-tape skip-table operation twice; the repetition construction preserves primitive recursiveness, so `codePrimRepeat` together with `codePrimSkipTable2` proves that `ndFormat.skipTable` is primitive recursive. Applying the format's canonizer theorem supplies a finite binary Turing machine and time bound that compute the serialization of the decoded input. Use `CodeNDTM.serialize` for encoding and `ndFormat.decode` for the total decoder. The format's padding identity guarantees that decoding a serialization with any finite true-bit suffix recovers the original machine. These data and the canonizer computation establish the required scheme.

**Key facts.** `Turing.codePrimRepeat`, `Turing.codePrimSkipTable2`, `Turing.CodeFormat.exists_canonizer`, `Turing.CodeFormat.decode_serialize_pad`.
