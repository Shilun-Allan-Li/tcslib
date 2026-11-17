<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.outerSt_w -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer State Width Register

**Claim.** For natural numbers $s,w,u,v,M$, the width register of the outer state with parameters $s,w,u,v,M$ equals $w$.

**Proof.** The outer state is formed by updating the zero state with radius $s$ and width $w$, then updating its source, target, and midpoint registers. Those final updates leave the width register unchanged, so it equals $w$.
