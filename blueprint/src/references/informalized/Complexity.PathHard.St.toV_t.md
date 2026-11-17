<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_t -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch register coordinate

**Claim.** For every state $st$, the register vector’s coordinate with index $3$ is the state’s scratch register $t$.

**Proof.** The state vector is defined by listing its registers in order, with $t$ in position $3$. Since $rT$ is exactly that coordinate, evaluating the vector there returns $st.t$ by the definition of the vector.
