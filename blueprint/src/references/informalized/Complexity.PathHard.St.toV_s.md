<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Radius coordinate

**Claim.** For every state $st$, the register vector’s coordinate with index $5$ is the state’s radius register $s$.

**Proof.** The state vector is defined by listing its registers in order, with $s$ in position $5$. Since $rS$ is exactly that coordinate, evaluating the vector there returns $st.s$ by the definition of the vector.
