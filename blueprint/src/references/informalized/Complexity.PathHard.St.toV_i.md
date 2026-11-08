<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.toV_i -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Index register coordinate

**Claim.** For every state $st$, the register vector’s coordinate with index $11$ is the state’s index register $i$.

**Proof.** The state vector is defined by listing its registers in order, with $i$ in position $11$. Since $rI$ is exactly that coordinate, evaluating the vector there returns $st.i$ by the definition of the vector.
