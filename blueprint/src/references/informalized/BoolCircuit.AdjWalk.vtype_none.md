<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.vtype_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Vertices Have No Gate Type

**Claim.** If $V\le n$, then $V$ lies below the circuit size and has no gate type exactly when $V<n$.

**Proof.** Expand the definitions of size and vertex type, then split according to whether $V<n$. If so, the type is none by definition, and $V$ is below the size because $V<n\le n+|\mathrm{gates}|$. Otherwise $V\le n$ forces $V=n$. At that index the type is the kind of the first gate, if one exists, and therefore is not none; the size-and-type condition fails. This proves the equivalence.
