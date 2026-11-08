<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_13 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Scratch Sum

**Claim.** Replacing coordinate $13$ of the register vector by $z$ gives the register vector of the record with its scratch sum replaced by $z$.

**Proof.** Two functions from the fifteen coordinates to the natural numbers are equal once they agree at every coordinate. At coordinate $13$, both sides have value $z$. At each other coordinate, the update leaves the original entry unchanged, and the record update leaves every field other than the scratch sum unchanged. Thus the functions agree everywhere.
