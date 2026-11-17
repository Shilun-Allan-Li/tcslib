<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.upd_d -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison Scratch Update

**Claim.** For any state $st$ and natural number $v$, replacing the decoding-and-comparison scratch coordinate of its register vector by $v$ gives the register vector of the state obtained from $st$ by setting that scratch register to $v$.

**Proof.** Compare the two functions at an arbitrary register position. At the decoding-and-comparison scratch position, updating the vector gives $v$, matching the updated state’s scratch register. At every other position, the vector update leaves the coordinate unchanged, and changing that scratch register leaves all other registers unchanged. The functions therefore agree everywhere.
