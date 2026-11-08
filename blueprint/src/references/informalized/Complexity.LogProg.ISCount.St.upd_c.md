<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_c -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the next-ball count

**Claim.** Updating the vector associated with $\sigma$ at register index $11$ to $z$ gives the vector associated with the state obtained by replacing its next-ball count $c$ with $z$.

**Proof.** Two functions on the 17 register indices are equal if they agree at every index. Fix an index and split into its 17 possible values. At index $11$, the update replaces the old coordinate $c$ by $z$, exactly matching the state with next-ball count $z$. At every other index, the update leaves the coordinate unchanged, and changing $c$ leaves those other fields unchanged. Hence the functions agree everywhere.
