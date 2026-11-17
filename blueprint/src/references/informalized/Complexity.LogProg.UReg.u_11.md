<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.UReg.u_11 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Candidate Vertex

**Claim.** Replacing coordinate $11$ of the register vector by $z$ gives the register vector of the record with its candidate vertex replaced by $z$.

**Proof.** Two functions from the fifteen coordinates to the natural numbers are equal once they agree at every coordinate. At coordinate $11$, both sides have value $z$. At each other coordinate, the update leaves the original entry unchanged, and the record update leaves every field other than the candidate vertex unchanged. Thus the functions agree everywhere.
