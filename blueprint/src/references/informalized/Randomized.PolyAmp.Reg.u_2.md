<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 2

**Claim.** Replacing coordinate $2$ of the register value vector by $y$ gives the vector of the record with its radius field replaced by $y$.

**Proof.** Compare the vectors coordinate by coordinate, considering the fifteen possible indices. Both sides have value $y$ at coordinate $2$, and at every other coordinate both updates preserve the original entry. Hence the vectors are equal.
