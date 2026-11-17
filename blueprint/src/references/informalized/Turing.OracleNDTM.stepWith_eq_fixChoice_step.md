<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.stepWith_eq_fixChoice_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Choice Step Equivalence

**Claim.** For any choice bit $b$, stepping the nondeterministic oracle machine using $b$ gives the same configuration as stepping the deterministic oracle machine obtained by fixing its choice to $b$.

**Proof.** The fixed-choice step theorem identifies the step of a nondeterministic machine with the step of its deterministic machine having choice $b$ fixed. Apply that theorem to the machine obtained from $N$ by fixing $b$; its nondeterministic presentation is exactly $N$, so the asserted configurations are equal.

**Key facts.** `Turing.toOracleNDTM_stepWith`.
