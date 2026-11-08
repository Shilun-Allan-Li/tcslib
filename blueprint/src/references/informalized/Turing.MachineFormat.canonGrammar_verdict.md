<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonGrammar_verdict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Grammar Verdict

**Claim.** Under the stated parsing, canonical-bits, and length hypotheses, failure of the grammar check forces decoding to return the fallback code, while success of the check means scanning returns a suffix.

**Proof.** The scan agrees with the canonical grammar check under the stated parsing, canonicality, and guard-length hypotheses (`Turing.MachineFormat.scan_eq_canonGrammar`). If the grammar check fails, this equality says that scanning returns none. Scanning is the optional remainder produced by full parsing (`Turing.CodeFormat.scan_full`), so full parsing also returns none. Decoding a failed full parse gives the fallback code (`Turing.CodeFormat.decode_of_parseFull_none`). If the grammar check succeeds, its being an optional value that is present means it equals some suffix; the scan equality identifies that same suffix as the result of scanning.

**Key facts.** `Turing.MachineFormat.scan_eq_canonGrammar`, `Turing.CodeFormat.scan_full`, `Turing.CodeFormat.decode_of_parseFull_none`.
