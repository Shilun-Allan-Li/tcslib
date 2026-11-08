<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex count coordinate

**Claim.** For every state $st$, the register vector’s coordinate with index $7$ is the state’s vertex count register $n$.

**Proof.** The state vector is defined by listing its registers in order, with $n$ in position $7$. Since $rN$ is exactly that coordinate, evaluating the vector there returns $st.n$ by the definition of the vector.
