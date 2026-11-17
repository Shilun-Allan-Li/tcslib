<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_y -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Length Coordinate

**Claim.** For a state $st$ with query-length register $y$, the register vector’s coordinate at the query-length position is $y$.

**Proof.** By definition, the register vector lists the state’s registers in order, beginning with the query-length register. Since $r_Y=0$, evaluating the vector at that position returns $st.y$.
