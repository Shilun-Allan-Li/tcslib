<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.decode_of_canonHeader -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fallback on a noncanonical header

**Claim.** If the canonical header extracted from a Boolean string is invalid, decoding that string in the format returns the format’s fallback code.

**Proof.** The invalid-header scan theorem (`scan_eq_none_of_canonHeaderOK`) says that scanning such a string returns no suffix. By the full-scan identity (`scan_full`), the scan is the parsed result with its code component discarded. If that mapped parse is none, the parse itself must be none. The decoding theorem for a failed full parse (`decode_of_parseFull_none`) then identifies the decoded value with the fallback.

**Key facts.** `Turing.MachineFormat.scan_eq_none_of_canonHeaderOK`, `Turing.CodeFormat.scan_full`, `Turing.CodeFormat.decode_of_parseFull_none`.
