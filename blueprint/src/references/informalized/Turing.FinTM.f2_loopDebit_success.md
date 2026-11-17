<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopDebit_success -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Debit Success Criterion

**Claim.** For every Boolean word $u$, the debit operation reports success exactly when the value of $u$ is positive.

**Proof.** The value relation for a loop debit (`Turing.FinTM.f2_loopDebit_value`) says that if the flag is true, the value of the debited word plus one equals the original value; if the flag is false, the original value is zero. Split according to the flag. In the false case, the relation gives value zero, so positivity fails, matching the false success flag. In the true case, the relation gives the original value as the new word's natural-number value plus one, which is positive. Thus success holds exactly when the original value is positive.

**Key facts.** `Turing.FinTM.f2_loopDebit_value`.
