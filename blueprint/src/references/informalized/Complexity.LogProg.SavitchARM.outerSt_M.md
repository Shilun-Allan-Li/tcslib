<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.outerSt_M -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer-search midpoint register

**Claim.** For all natural numbers $s,w,u,v,M$, the midpoint register of the outer-search state determined by these values equals $M$.

**Proof.** The outer-search state is obtained by updating the midpoint register to $M$; the construction makes no later update to that register.
