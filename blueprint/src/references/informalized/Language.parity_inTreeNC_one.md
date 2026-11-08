<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: Language.parity_inTreeNC_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity in logarithmic-depth tree circuits

**Claim.** The parity language is recognized by a family of Boolean formula trees with fan-in at most two, polynomial size, and depth bounded by a constant multiple of \(\log_2 n+1\).

**Proof.** Take the family whose circuit at length \(n\) is the parity circuit. The established bounds show that each circuit has fan-in at most two (`BoolCircuit.parityCircuit_maxFanin_le`), size at most \(32(n+1)^4\) (`BoolCircuit.parityCircuit_size_le`), and depth at most \(4(\mathrm{Nat.log}\ 2\ n+1)\) (`BoolCircuit.parityCircuit_depth_le`). To identify the language it recognizes, evaluate the circuit on the Boolean list’s indexed entries. The parity circuit’s evaluation is the XOR fold over all indices (`BoolCircuit.parityCircuit_eval`); because `List.finRange` enumerates precisely the list’s positions, this fold equals the XOR fold of the list itself. Membership in the parity language is equivalent to that fold being true (`Language.mem_parity_iff`). Thus the family recognizes parity and meets the required bounds.

**Key facts.** `BoolCircuit.parityCircuit_maxFanin_le`, `BoolCircuit.parityCircuit_size_le`, `BoolCircuit.parityCircuit_depth_le`, `BoolCircuit.TreeCircuitFamily.mem_language_iff`, `BoolCircuit.parityCircuit_eval`, `Language.mem_parity_iff`.
