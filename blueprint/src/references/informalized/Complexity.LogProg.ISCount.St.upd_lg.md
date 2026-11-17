<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_lg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the halving count

**Claim.** Replacing coordinate 1 of the register vector of a state by $z$ gives the register vector of the state whose halving count is $z$.

**Proof.** Two vectors are equal if they agree at every coordinate. Fix a coordinate $r$ among the seventeen. If $r=1$, the update replaces the halving-count entry by $z$, which is exactly the entry at that position in the modified state. At every other coordinate, the update leaves the original entry unchanged, and the corresponding state register is unchanged as well. Thus the vectors agree at every coordinate.
