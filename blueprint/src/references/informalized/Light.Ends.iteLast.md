<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.iteLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Conditional Execution

**Claim.** If the condition is safe and each branch, when selected, can execute within the budget remaining after evaluating the condition, then the conditional executes within total budget $T$ and ends in a state satisfying $Q$.

**Proof.** Apply the conditional execution principle (`Light.Ends.ite`) with branch budget $T'=T-(\mathrm{cost}(c)+1)$. Its required budget inequality is $\mathrm{cost}(c)+1+T'\le T$, which follows from $\mathrm{cost}(c)+1\le T$ by natural-number subtraction. The hypotheses provide safety of the condition and the appropriate execution for each truth value, so the principle gives the claimed execution and postcondition.

**Key facts.** `Light.Ends.ite`.
