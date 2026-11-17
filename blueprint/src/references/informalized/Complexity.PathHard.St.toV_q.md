<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width-check pointer coordinate

**Claim.** For every state $st$, the register vector’s coordinate with index $10$ is the state’s width-check pointer $q$.

**Proof.** The state vector is defined by listing its registers in order, with $q$ in position $10$. Since $rQ$ is exactly that coordinate, evaluating the vector there returns $st.q$ by the definition of the vector.
