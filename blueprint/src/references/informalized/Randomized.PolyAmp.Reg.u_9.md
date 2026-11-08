<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_9 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Candidate-Code Register

**Claim.** Replacing coordinate $9$ of the register-value function by $y$ gives the register-value function of the record whose candidate-code value is $y$.

**Proof.** The candidate-code field is listed at coordinate $9$. At coordinate $9$, both functions have value $y$; at every other coordinate, the function update preserves the old value and changing the candidate-code field leaves that coordinate's field unchanged. Hence the functions agree at all coordinates.
