<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_5 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 5

**Claim.** Replacing coordinate $5$ in the vector of register values by $y$ gives the vector of the record whose number-of-runs field is $y$.

**Proof.** The vector lists the fields in order, so coordinate $5$ contains the number-of-runs field $R$. Compare the two functions at each coordinate: both have value $y$ at coordinate $5$, while at every other coordinate both retain the original field value. Hence they agree at every coordinate and are equal.
