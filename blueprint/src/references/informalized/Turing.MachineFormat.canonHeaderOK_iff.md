<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonHeaderOK_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Valid Canonical Headers

**Claim.** A Boolean word passes the canonical-header validity test exactly when it decodes as a pair $(bits,rest)$ and $bits$ is the canonical binary expansion of its value.

**Proof.** Split according to whether paired decoding of $\alpha$ fails or returns a pair. If decoding fails, the validity test's first condition is false, and there is no pair witnessing the stated characterization. If decoding returns $(bits,rest)$, the test's remaining condition is precisely that the decoded header passes the canonical-bits test. By the characterization of that test (`Turing.MachineFormat.canonBitsOK_iff`), this holds exactly when $bits$ equals the canonical binary expansion of the natural number given by its bit-value fold. That fold is the value denoted by $bits$, so this is the required condition.

**Key facts.** `Turing.MachineFormat.canonBitsOK_iff`.
