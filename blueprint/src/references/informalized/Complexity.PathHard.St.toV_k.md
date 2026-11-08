<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_k -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width cap coordinate

**Claim.** For every state $st$, the register vector’s coordinate with index $9$ is the state’s width cap $k$.

**Proof.** The state vector is defined by listing its registers in order, with $k$ in position $9$. Since $rK$ is exactly that coordinate, evaluating the vector there returns $st.k$ by the definition of the vector.
