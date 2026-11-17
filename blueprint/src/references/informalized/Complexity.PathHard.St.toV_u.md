<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_u -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Source Register Coordinate

**Claim.** For a state $st$ with source-vertex register $u$, the register vector’s coordinate at the source-vertex position is $u$.

**Proof.** By definition, the register vector lists the state’s registers in order, with the source-vertex register in position $13$. Since $r_U=13$, evaluating the vector there returns $st.u$.
