<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.run_out -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Is Extended by a Suffix

**Claim.** For every state and number of steps, the output after the run is the initial output followed by some bit string.

**Proof.** Induct on the number of steps, generalizing over the starting state. At zero steps the output is unchanged, so take the added suffix to be empty. For the successor case, the one-step output property (`Complexity.CounterProg.step_out`) gives a bit string $e$ appended during the first step. Apply the induction hypothesis to the resulting state to obtain a further suffix $e'$. The final output is the original output followed by $e$ and then $e'$, hence by the single suffix $e\mathbin{++}e'$, using associativity of list concatenation and the run decomposition law (`Complexity.CounterProg.run_succ`).

**Key facts.** `Complexity.CounterProg.run_succ`, `Complexity.CounterProg.step_out`.
