<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_e -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vertex Exponent Update

**Claim.** For any state $st$ and natural number $v$, replacing the vertex-exponent coordinate of its register vector by $v$ gives the register vector of the state obtained from $st$ by setting its vertex exponent to $v$.

**Proof.** Compare the two functions at an arbitrary register position. At the vertex-exponent position, updating the vector gives $v$, matching the updated state’s vertex exponent. At every other position, the vector update leaves the coordinate unchanged, and changing the vertex exponent leaves all other registers unchanged. Thus the functions agree at every position.
