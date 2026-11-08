<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.iteIffThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Followed by a Continuation

**Claim.** If the condition is safe and is equivalent in the initial state to proposition $p$, and either branch followed by the continuation has the stated remaining cost bound, then the conditional followed by the continuation terminates within cost $T$ in a state satisfying $Q$.

**Proof.** First translate the branch assumptions from the proposition $p$ to the truth value of the condition: the equivalence gives the first branch execution when $c$ holds and the second when $c$ fails. Apply the conditional-with-continuation result (`Light.Ends.iteThen`) to these two executions. Its safety requirement is supplied directly, and the assumed inequality $\mathrm{cost}(c)+1\le T$ provides the required budget for evaluating the condition and selecting a branch.

**Key facts.** `Light.Ends.iteThen`.
