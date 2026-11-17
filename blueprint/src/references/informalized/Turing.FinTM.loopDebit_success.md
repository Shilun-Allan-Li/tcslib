<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopDebit_success -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrement Success Criterion

**Claim.** For every Boolean word $u$, the fixed-width decrement reports success exactly when the value of $u$ is positive.

**Proof.** Use the value-change statement for decrement (`loopDebit_value`) and split according to whether the operation reports success. If it fails, that statement gives value zero, so the value is not positive. If it succeeds, the decremented word's value plus one equals the original value; in particular, the original value is positive. These two cases establish the equivalence.

**Key facts.** `Turing.FinTM.loopDebit_value`.
