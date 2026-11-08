<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean :: Complexity.LogProg.SavitchARM.codeWidth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code Width Bound

**Claim.** If $2C\le E$, then $C((n+2)^E+\log_2(n)+1)\le(n+2)^{2E}$ for the stated value of $C$.

**Proof.** Put $s=(n+2)^E$. The logarithm estimate $\log_2(n)+1\le n+2$ follows from `Complexity.logSpace_le_succ`, and $n+2\le s$ when $E>0$. If $E=0$, the assumed bound $2C\le E$ forces $C=0$, and the claim is immediate. Thus in the positive case, $\log_2(n)+1\le s$, so the left side is at most $C(2s)$. Also $2C\le 2^E\le s$: the first inequality follows from $2C\le E$ and the elementary bound $E\le2^E$, and the second from $2\le n+2$. Hence $2Cs\le s^2$. Finally, $s^2=(n+2)^{2E}$, proving the estimate.

**Key facts.** `Complexity.logSpace_le_succ`.
