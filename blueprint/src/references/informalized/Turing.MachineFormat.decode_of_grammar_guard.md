<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.decode_of_grammar_guard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fallback below the grammar length bound

**Claim.** If $\alpha$ parses as paired header $bits$ and suffix $rest$, and $|rest|<(4k+5)3^{k+1}(v+1)$ for the value $v$ represented by $bits$, then decoding $\alpha$ returns the format’s fallback code.

**Proof.** The guarded scanner agrees with the format scanner (`guardedScan_eq`). Under the given paired parse and strict length bound, the guarded scan rejects the input, so the format scan returns none. The full-scan identity (`scan_full`) identifies this scan with the parsed result after discarding its code component; hence the full parse is itself none. A failed full parse decodes to the fallback (`decode_of_parseFull_none`).

**Key facts.** `Turing.MachineFormat.guardedScan_eq`, `Turing.CodeFormat.scan_full`, `Turing.CodeFormat.decode_of_parseFull_none`.
