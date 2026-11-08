<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_14 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 14

**Claim.** Replacing coordinate $14$ of the register value vector by $y$ gives the vector of the record with its twice-count field replaced by $y$.

**Proof.** Compare the vectors at each of the fifteen coordinates. At coordinate $14$, both have value $y$; at every other coordinate, the coordinate update and the field replacement preserve the original entry. Therefore the vectors are equal.
