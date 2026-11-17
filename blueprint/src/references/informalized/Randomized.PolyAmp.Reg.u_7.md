<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_7 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 7

**Claim.** Replacing coordinate $7$ in the vector of register values by $y$ gives the vector of the record whose accepting-runs field is $y$.

**Proof.** The vector lists the fields in order, with the accepting-runs field at coordinate $7$. At that coordinate both functions take value $y$. At every other coordinate, the function update preserves the listed value, and replacing the accepting-runs field does not affect that field. Thus the two functions agree everywhere.
