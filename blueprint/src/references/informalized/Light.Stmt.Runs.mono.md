<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Stmt.Runs.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the postcondition

**Claim.** If $s$ runs safely from $[?]$ to $R$, and every state satisfying $R$ also satisfies $R'$, then $s$ runs safely from that state to $R'$.

**Proof.** Keep the block-safety part of the assumed run unchanged. Its resulting state satisfies $R$; by the assumed implication from $R$ to $R'$, that same resulting state satisfies $R'$.
