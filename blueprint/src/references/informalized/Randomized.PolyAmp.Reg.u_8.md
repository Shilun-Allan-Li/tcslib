<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_8 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 8

**Claim.** Replacing coordinate $8$ in the vector of register values by $y$ gives the vector of the record whose current-code field is $y$.

**Proof.** The vector lists the current-code field at coordinate $8$. Evaluating at this coordinate gives $y$ on both sides. At each of the other fourteen coordinates, neither replacement changes the listed field value. The two functions therefore agree at every coordinate.
