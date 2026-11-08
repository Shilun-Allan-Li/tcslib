<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_0 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Input-Length Register

**Claim.** Updating entry zero of a register record's value vector to $y$ produces the value vector of the record whose input-length component has been replaced by $y$.

**Proof.** Compare the two vectors at an arbitrary index. At index zero, the update assigns $y$, which is also the new record's input-length entry. At every other index, the update leaves the original vector entry unchanged, and replacing the input-length component does not change any of those other record components. Hence the vectors agree at every index.
