<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.skipThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skip Before a Program

**Claim.** If $s$ can execute from $\sigma$ within budget $T$ and end in a state satisfying $Q$, then skip followed by $s$ can also do so.

**Proof.** Use the skip execution from $\sigma$ back to itself, which has cost zero. Follow it with the given execution of $s$. The sequential execution rule combines these into an execution of skip followed by $s$; its cost is the sum of zero and the cost of $s$, so it remains at most $T$, with the same final state satisfying $Q$.

**Key facts.** `Light.Ends.seq`, `Light.Ends.skip`.
