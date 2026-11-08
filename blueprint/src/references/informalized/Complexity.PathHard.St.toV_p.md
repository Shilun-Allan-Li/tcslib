<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_p -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair scan pointer coordinate

**Claim.** For every state $st$, the register vector’s coordinate with index $1$ is the state’s pair-scan pointer $p$.

**Proof.** The state vector is defined by listing its registers in order, with $p$ in position $1$. Since $rP$ is exactly that coordinate, evaluating the vector there returns $st.p$ by the definition of the vector.
