<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.wk_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Width Setup Run

**Claim.** Under the stated zero-register, positivity, register-bound, and exponential-size assumptions, the width setup reaches the phase exit with the prescribed values of $w,K,Bs$ and all other components, marking, and head unchanged, while satisfying the guard throughout.

**Proof.** Put $r=S.\mathrm{toV}(\mathrm{rad}(q))$ and $w=K_0(r+S.Lg+1)$. First copy the selected radius into $X$, then copy $Lg$ into $X$, and increment $X$ once. These copy loops establish $X=r+Lg+1$. The size assumption $K_0>0$ ensures the loop that adds $X$ to $w$ runs for all $K_0$ iterations; the copy-loop result gives $w=K_0X$. Clear $X$ and set $K=1$. Copy $w$ into $C$, then run the shift loop, which changes $K$ to $2^w$ and clears $C$. Each of these loops is covered by its bounded-run result; the intermediate register bounds follow from the assumed bound $3\cdot 2^w\le B$. Next copy $K$ into $Bs$, obtaining $Bs=2^w$. In the second-search phase this is already the required value, so the remaining reachability is reflexive. In the first-search and final-scan phases, copy $K$ into $Bs$ once more, giving $Bs=2\cdot 2^w$. The copy and shift runs are joined in sequence, identifying their endpoint states and heads, to obtain the asserted run; the cited bounded-run facts ensure the guard holds throughout.

**Key facts.** `Complexity.LogProg.ExpBFS.cp_run`, `Complexity.LogProg.ExpBFS.mw_run`, `Complexity.LogProg.ExpBFS.cont`, `Complexity.LogProg.ExpBFS.step_of`, `Complexity.LogProg.ExpBFS.sh_run`, `Complexity.LogProg.ExpBFS.reach_cf`, `Complexity.LogProg.MReach.refl`, `Complexity.LogProg.MReach.trans`.
