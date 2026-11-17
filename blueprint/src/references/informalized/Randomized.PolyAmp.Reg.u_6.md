<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_6 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 6

**Claim.** Replacing coordinate $6$ in the vector of register values by $y$ gives the vector of the record whose runs-left field is $y$.

**Proof.** The vector lists the fields in order, so coordinate $6$ contains the runs-left field $i$. Compare the functions coordinate by coordinate. At coordinate $6$ both give $y$, and at all other coordinates the update and the record replacement leave the original field values in place. Therefore the functions are equal.
