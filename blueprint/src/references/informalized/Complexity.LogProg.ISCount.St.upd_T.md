<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the scratch register

**Claim.** Updating the vector associated with $\sigma$ at register index $6$ to $z$ gives the vector associated with the state obtained by replacing its doubling scratch register $T$ with $z$.

**Proof.** Two functions on the 17 register indices are equal if they agree at every index. Fix an index and split into its 17 possible values. At index $6$, the update replaces the old coordinate $T$ by $z$, exactly matching the state with scratch register $z$. At every other index, the update leaves the coordinate unchanged, and changing $T$ leaves those other fields unchanged. Hence the functions agree everywhere.
