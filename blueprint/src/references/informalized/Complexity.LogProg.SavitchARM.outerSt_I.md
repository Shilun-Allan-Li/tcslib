<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.outerSt_I -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial recursion level

**Claim.** For all natural numbers $s,w,u,v,M$, the recursion-level register of the outer-search state determined by these values is $0$.

**Proof.** The outer-search state is built from a zero state by setting its radius, width, and code-bound registers, then its source, target, and midpoint registers. None of these updates changes the recursion-level register, so it remains $0$.
