<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonHeaderBranch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Header Branch Machine

**Claim.** For every machine format $F$, there is a finite Boolean-alphabet machine with at least one work tape and two distinct exit states which, on any input, reaches the exit determined by the canonical-header validity test in linear time, with blank tapes and the required first-exit property.

**Proof.** The canonical-header validity test is computed as a one-bit output by a machine in linear time. Apply the Boolean-branch construction to this machine and the predicate that returns that test. It converts the computation into a machine whose two exits encode the Boolean result, while preserving a positive number of work tapes and ensuring that neither exit is reached earlier. The bound and final configuration follow directly from that branch construction.

**Key facts.** `Turing.MachineFormat.exists_canonHeaderOKTM`, `Turing.MachineFormat.exists_canonBoolBranch`.
