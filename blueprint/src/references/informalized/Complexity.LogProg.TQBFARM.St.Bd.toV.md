<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.Bd.toV -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Bounds Under the State Encoding

**Claim.** If each of the seven registers of a state is at most $B$, then every coordinate of its register vector is at most $B$.

**Proof.** Unpack the hypothesis into the seven bounds for $K,S,P,T,Z,C,V$. The vector encoding lists exactly these registers in that order. For any coordinate, its index is one of the seven positions, so its value is the corresponding register and is bounded by the matching hypothesis.
