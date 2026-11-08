<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift Scratch Coordinate

**Claim.** For a state $st$ with shift-scratch register $z$, the register vector’s coordinate at the shift-scratch position is $z$.

**Proof.** By definition, the register vector lists the shift-scratch register last, in position $14$. Since $r_Z=14$, evaluating the vector there returns $st.z$.
