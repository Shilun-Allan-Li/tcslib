<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.outerSt_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer-search code bound

**Claim.** For all natural numbers $s,w,u,v,M$, the code-bound register of the outer-search state determined by these values equals $2^w$.

**Proof.** The state construction sets the code-bound register to $2^w$. The subsequent updates of the source, target, and midpoint registers leave it unchanged.
