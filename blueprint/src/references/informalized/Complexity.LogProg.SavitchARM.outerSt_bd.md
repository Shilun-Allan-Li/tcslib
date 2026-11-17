<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.outerSt_bd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the outer state

**Claim.** If $s\le w$ and $u,v,M\le 2^w$, then every register of the outer state with parameters $s,w,u,v,M$ is at most $2^{w^2}$.

**Proof.** The state has zero in every register except the radius $s$, width $w$, code bound $2^w$, source $u$, target $v$, and midpoint $M$. By hypothesis, $s\le w$ and $u,v,M\le 2^w$. The size bound $w<2^w\le 2^{w^2}$ (`size_facts`) therefore bounds the width and code bound as well. Hence each register is at most $2^{w^2}$, as required.

**Key facts.** `Complexity.LogProg.SavitchARM.size_facts`.
