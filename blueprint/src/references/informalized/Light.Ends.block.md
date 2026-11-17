<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Safe Block

**Claim.** If a statement block is safe when its operations are evaluated in sequence, its resulting state satisfies $Q$, and its block cost is at most $T$, then it has an execution of cost at most $T$ ending in a state satisfying $Q$.

**Proof.** The hypothesis $s.\mathrm{Runs}(\mathrm{lim},\sigma,Q)$ supplies both block safety at $\sigma$ and the postcondition $Q$ at the state obtained by applying the block. The block execution theorem ( `Light.Ends.of_blockSafe`) turns precisely these facts, together with the bound on block cost, into an execution ending at that resulting state with cost no greater than the block cost. Since the block cost is at most $T$, this execution meets the required bound.

**Key facts.** `Light.Ends.of_blockSafe`.
