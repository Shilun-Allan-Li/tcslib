<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential Composition of Bounded Executions

**Claim.** If the first statement executes within budget $T_1$ and its final state admits an execution of the second statement within budget $T-T_1$, then their sequential composition executes within budget $T$ and ends in a state satisfying $Q$.

**Proof.** Apply the sequential composition principle (`Light.Ends.seq`) with the two component budgets $T_1$ and $T-T_1$. The assumed execution of the first statement has the required postcondition: that its final state admits the bounded execution of the second. Finally, $T_1+(T-T_1)\le T$ follows from $T_1\le T$ by natural-number subtraction. The composition principle therefore yields the claimed execution.

**Key facts.** `Light.Ends.seq`.
