<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.scan_eq_canonGrammar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan and canonical grammar agreement

**Claim.** When the aligned pair parser returns $(b,r)$, $b$ is the canonical binary representation of its value, and the canonical guard bound holds, scanning agrees with the canonical grammar check on $r$.

**Proof.** The canonical guard bound is the maximum of the format guard and the machine-format grammar guard, so it implies the format guard bound. Expand the definitions of scanning and the canonical grammar check, and use the given pair parse to identify their header and remainder. The canonical-bit hypothesis makes the bit-canonicality test pass, and the implied length bound makes the format guard pass. Both procedures therefore perform the same bounded-index skip. If that skip fails, both results are failure. If it succeeds with a suffix, rewriting the format’s table skipper as the fixed machine-format table skipper shows that the remaining table skip and the final requirement that every suffix bit be $1$ are exactly the canonical grammar check.
