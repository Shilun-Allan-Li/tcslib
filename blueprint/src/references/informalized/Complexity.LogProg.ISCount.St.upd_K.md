<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the code-bound register

**Claim.** Updating the vector associated with $\sigma$ at register index $5$ to $z$ gives the vector associated with the state obtained by replacing its code bound $K$ with $z$.

**Proof.** Two functions on the 17 register indices are equal if they agree at every index. Fix an index and split into its 17 possible values. At index $5$, the update replaces the old coordinate $K$ by $z$, exactly matching the state with code bound $z$. At every other index, the update leaves the coordinate unchanged, and changing $K$ leaves those other fields unchanged. Hence the functions agree everywhere.
