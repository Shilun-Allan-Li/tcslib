<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_g -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the guessed-code coordinate

**Claim.** Replacing coordinate $14$ of the vector associated with $\sigma$ by $z$ gives the vector associated with the state whose guessed-code register is replaced by $z$.

**Proof.** Compare the vectors at an arbitrary register index. At index $14$, both sides have value $z$, and at all other indices they have the same unchanged register of $\sigma$. Checking the 17 possible indices establishes equality of the vectors.
