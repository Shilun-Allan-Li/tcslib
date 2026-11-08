<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_x -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Length Coordinate

**Claim.** For a state $st$ with input-length register $x$, the register vector’s coordinate at the input-length position is $x$.

**Proof.** By definition, the register vector lists the state’s registers in order, with the input-length register in position $2$. Since $r_X=2$, evaluating the vector there returns $st.x$.
