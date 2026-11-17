<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyMachine.lean :: Randomized.PolyAmp.Reg.u_3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating Register 3

**Claim.** Replacing coordinate $3$ of the register value vector by $y$ gives the vector of the record with its exponent field replaced by $y$.

**Proof.** Evaluate both sides at each of the fifteen coordinates. At coordinate $3$, each side has value $y$; at every other coordinate, neither update changes that coordinate's original value. The vectors consequently agree at every coordinate.
