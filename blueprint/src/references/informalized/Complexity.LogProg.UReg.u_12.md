<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_12 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Column Register

**Claim.** Replacing coordinate $12$ of the register vector by $z$ gives the register vector of the record with its column register replaced by $z$.

**Proof.** Two functions from the fifteen coordinates to the natural numbers are equal once they agree at every coordinate. At coordinate $12$, both sides have value $z$. At each other coordinate, the update leaves the original entry unchanged, and the record update leaves every field other than the column register unchanged. Thus the functions agree everywhere.
