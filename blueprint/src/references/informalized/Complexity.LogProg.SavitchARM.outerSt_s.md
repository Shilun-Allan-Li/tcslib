<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.outerSt_s -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer State Radius Register

**Claim.** For natural numbers $s,w,u,v,M$, the radius register of the outer state with parameters $s,w,u,v,M$ equals $s$.

**Proof.** The outer state is formed by updating the zero state with the radius and width, then updating its source, target, and midpoint registers. These latter updates do not alter the radius register, so its value remains $s$.
