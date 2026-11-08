<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the second register

**Claim.** Updating coordinate $1$ of the register value vector to $y$ gives the value vector of the record with its $$-component replaced by $y$.

**Proof.** To prove equality of the two vectors, compare their values at an arbitrary coordinate $r$. Split into the fifteen possible coordinates. At coordinate $1$, both sides have value $y$; at every other coordinate, the update leaves the original value unchanged and the record update leaves the corresponding field unchanged. Thus the values agree at every coordinate, so the vectors are equal.
