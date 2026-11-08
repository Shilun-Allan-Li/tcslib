<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean :: Complexity.LogProg.SavitchARM.outerSt_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant of the outer state

**Claim.** If $u,v<2^w$ and $M\le 2^w$, then the outer state with its level register set to $w$ satisfies the stated invariant at level $w$.

**Proof.** By construction, all scratch, input-length, exponent, power, loop, and popped-endpoint registers are zero; the radius and width are $s$ and $w$, the code-bound register is $2^w$, the source and target are $u$ and $v$, the midpoint is $M$, and the level is $w$. The hypotheses give the required bounds on the source, target, and midpoint. The endpoint and phase stacks are both zero. Their invariant bounds reduce respectively to $0<2^{w(w-w)}=1$ and $0<2^{w-w}=1$, which hold.
