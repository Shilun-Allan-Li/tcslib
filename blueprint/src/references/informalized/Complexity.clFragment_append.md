<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFragment_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Serialized Fragments

**Claim.** For CNF formulas $\varphi$ and $\psi$ over natural-number variables, the fragment of their concatenation is the concatenation of their fragments.

**Proof.** Each fragment is formed by mapping each clause to its serialization with a leading marker, then concatenating the resulting lists. Mapping a function over a concatenation of lists distributes over concatenation, so the fragment of $\varphi++\psi$ is the fragment of $\varphi$ followed by the fragment of $\psi$.
