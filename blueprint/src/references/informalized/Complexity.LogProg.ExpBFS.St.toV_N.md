<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_N -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Length Coordinate

**Claim.** For every state $S$, the input-length coordinate of its 17-entry register vector is $S.N$.

**Proof.** The vector lists the state fields in order, with $S.N$ in position $0$. The input-length coordinate has that index, so evaluating the vector there returns $S.N$ by its definition.
