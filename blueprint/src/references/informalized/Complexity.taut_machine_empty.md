<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_machine_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier on Empty Input

**Claim.** On empty input, the verifier halts within two steps and outputs the single bit $0$.

**Proof.** The characterization of computation within a given time (`Turing.FinTM.computesInTime_iff`) reduces the claim to the machine’s state and output after two steps. Evaluating those two transitions on the empty input gives a halted state and output $[\mathrm{false}]$, as required.

**Key facts.** `Turing.FinTM.computesInTime_iff`.
