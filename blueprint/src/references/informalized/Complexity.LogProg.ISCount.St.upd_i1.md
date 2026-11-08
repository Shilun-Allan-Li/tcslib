<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_i1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the next-stage coordinate

**Claim.** Replacing coordinate $8$ of the vector associated with $\sigma$ by $z$ gives the vector associated with the state whose stage-plus-one register is replaced by $z$.

**Proof.** Compare both vectors at an arbitrary index. The entry at index $8$ is $z$ on each side, while every other entry is the corresponding unchanged register of $\sigma$. Checking all 17 indices proves the desired vector equality.
