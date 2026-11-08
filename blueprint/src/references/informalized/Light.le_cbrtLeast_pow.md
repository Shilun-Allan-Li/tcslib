<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.le_cbrtLeast_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cube bound for the least cube root

**Claim.** For every natural number $n$, the least natural number $r$ satisfying $n\le r^3$ also satisfies $n\le r^3$.

**Proof.** By definition, $r$ is the natural number selected from the nonempty set of witnesses to $n\le s^3$. The specification of the least-witness operation guarantees that the selected number satisfies the predicate, hence $n\le r^3$ (`Nat.find_spec`).

**Key facts.** `Light.exists_le_cube`.
