<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_10 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Walk Length

**Claim.** Replacing coordinate $10$ of the register vector by $z$ gives the register vector of the record with walk length replaced by $z$.

**Proof.** Two functions from the fifteen coordinates to the natural numbers are equal once they agree at every coordinate. At coordinate $10$, both sides have value $z$. At each other coordinate, the update leaves the original entry unchanged, and the record update leaves every field other than the walk length unchanged. Thus the functions agree everywhere.
