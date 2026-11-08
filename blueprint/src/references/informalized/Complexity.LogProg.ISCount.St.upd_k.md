<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.upd_k -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the add-twice counter

**Claim.** Replacing coordinate $2$ of the vector associated with $\sigma$ by $z$ gives the vector associated with the state whose add-twice counter is replaced by $z$.

**Proof.** Compare the vectors coordinate by coordinate. At index $2$, both the vector update and the state replacement give $z$. At each of the other 16 indices, the corresponding register remains unchanged. Thus the vectors agree at every index.
