<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_i -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the stage coordinate

**Claim.** Replacing coordinate $7$ of the vector associated with $\sigma$ by $z$ gives the vector associated with the state whose stage register is replaced by $z$.

**Proof.** Compare the vectors at an arbitrary register index. At index $7$, both sides take the value $z$; at every other index they retain the matching register of $\sigma$. Since these are the 17 possible indices, the two vectors are equal.
