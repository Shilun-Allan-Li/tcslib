<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_4 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 4

**Claim.** Replacing coordinate $4$ in the vector of register values by $y$ gives the vector of the record whose $K$ field is $y$.

**Proof.** The vector lists the fields in order, so coordinate $4$ contains $K$. To prove the two functions equal, compare them at each of the fifteen coordinates. At coordinate $4$, both sides have value $y$; at every other coordinate, the update leaves the value unchanged and the record update leaves the corresponding field unchanged. Thus the functions agree everywhere.
