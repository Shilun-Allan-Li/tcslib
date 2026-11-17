<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Bounded Execution

**Claim.** Increasing the cost bound and weakening the required final-state predicate preserves bounded executability.

**Proof.** Unpack the assumed bounded execution, retaining its final state, actual cost, execution, and proof of $Q$. Since the actual cost is at most $T$ and $T\le T'$, it is at most $T'$. The implication from $Q$ to $Q'$ shows that the same final state satisfies the new postcondition. These witnesses establish the result.
