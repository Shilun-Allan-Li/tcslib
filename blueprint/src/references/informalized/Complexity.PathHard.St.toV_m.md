<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_m -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size register coordinate

**Claim.** For every state $st$, the register vector’s coordinate with index $8$ is the state’s size register $m$.

**Proof.** The state vector is defined by listing its registers in order, with $m$ in position $8$. Since $rM$ is exactly that coordinate, evaluating the vector there returns $st.m$ by the definition of the vector.
