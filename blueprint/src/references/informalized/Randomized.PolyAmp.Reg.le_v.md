<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.le_v -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Values Are Uniformly Bounded

**Claim.** If each of a register record's fifteen components is at most $B$, then every entry of its associated register vector is at most $B$.

**Proof.** Unpack the hypothesis into the fifteen componentwise inequalities. For any vector index, it is one of the fifteen indices; at each index, the vector's definition selects the corresponding register component. The corresponding inequality therefore gives the bound.
