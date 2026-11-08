<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.scan_eq_none_of_canonHeaderOK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Malformed header rejection

**Claim.** If an aligned-pair parse of $\alpha$ fails, or the parsed header fails the canonical last-bit check, scanning $\alpha$ fails.

**Proof.** Split on whether the aligned-pair parser succeeds. If it fails, scanning fails at its initial parse. If it returns $(bits,rest)$, the hypothesis that the canonical header check is false rules out $bits$ being the canonical binary representation of its value: otherwise the characterization of the canonical header check would make that check true. Hence the scan’s canonicality test fails, so the scan returns none.

**Key facts.** `Turing.MachineFormat.canonHeaderOK_iff`.
