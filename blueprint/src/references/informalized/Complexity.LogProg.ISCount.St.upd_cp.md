<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_cp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the known-ball size

**Claim.** Updating the vector of a state at register index $9$ to $z$ yields the vector of the state with known-ball size replaced by $z$.

**Proof.** Compare the two register vectors at an arbitrary index. Checking the 17 possible indices, the updated coordinate $9$ has value $z$ on both sides, and all other coordinates retain their original values from $\sigma$. Hence the vectors agree at every coordinate.
