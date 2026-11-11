<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stageQ_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage query-list length bound

**Claim.** For the stage data $d$ and index $i$, the number of queries made at stage $i$ is strictly less than $2^{	ext{freshLen}(i,d.bound)}$.

**Proof.** The machine makes at most as many queries as the number of steps in the stage. The query-list length bound (`Turing.OracleTM.queriesWithin_length_le`) therefore bounds its length by $\text{freshLen}(i,d.\bound)^i+i$. By the defining choice property of the fresh length (`Complexity.freshLen_spec`), this step count is strictly less than $2^{\text{freshLen}(i,d.\bound)}$. Combining the two inequalities proves the claim.

**Key facts.** `Turing.OracleTM.queriesWithin_length_le`, `Complexity.freshLen_spec`.
