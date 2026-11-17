<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_c -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop Counter Update

**Claim.** For any state $st$ and natural number $v$, replacing the loop-counter coordinate of its register vector by $v$ gives the register vector of the state obtained from $st$ by setting its loop counter to $v$.

**Proof.** Compare the two functions at an arbitrary register position. At the loop-counter position, updating the vector gives $v$, which is also the loop counter of the updated state. At every other position, the vector update leaves the coordinate unchanged, and changing the state’s loop counter leaves that register unchanged. Hence the functions agree at every position.
