<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.univTM_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Simulation of Coded Machines

**Claim.** For each code string, a universal machine simulates its decoded machine on paired inputs with a constant-factor linear time bound, and every output produced by the universal machine on such an input is also produced by the decoded machine on the original input.

**Proof.** Apply the universal-machine theorem to the given coding scheme. It supplies a universal machine and, for each fixed code string, a constant with both stated properties. The machine called `univTM` is the universal machine selected from that theorem, so taking its code-specific constant gives the required pair of implications.

**Key facts.** `Turing.universal`.
