<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean :: Complexity.Codec.le_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register minimum loop

**Claim.** The specified loop reaches yes if the initial value of register $a$ is at most that of $b$, and no otherwise. It replaces register $t$ by $\min(v(a),v(b))$, leaves every other register unchanged, and keeps the guard true throughout.

**Proof.** Let $n=\min(v(a),v(b))-v(t)$, which is a natural number by the two initial inequalities. The proof inducts on this gap, generalizing the register valuation so the induction can be applied after each increment of $t$.

If $n=0$, then $v(t)=\min(v(a),v(b))$. When $v(a)\le v(b)$, this says $v(t)=v(a)$, so the first test goes directly to yes and changes no register. When $v(a)>v(b)$, it says $v(t)=v(b)\ne v(a)$; the first test therefore proceeds to the second test, which goes to no without changing registers. In both cases the one-step run satisfies the guard.

For the successor case, the gap is positive, so $v(t)$ is strictly below both $v(a)$ and $v(b)$. The first test consequently proceeds to the second test, which proceeds to bump. At bump, increment $t$ and call the induction hypothesis on the updated valuation. Because $t,a,b$ are pairwise distinct in the required sense, updating $t$ preserves the values of $a$ and $b$. The new gap has decreased by one, and its minimum target is unchanged. The updated valuation still respects the bound: the new value of $t$ is at most $v(a)$, which was at most $B$, and all other registers retain their old bounds (\texttt{register_update_le}). The loop's precondition at each test is satisfied because the tested registers are distinct, as required by the guard. The three one-step prefixes and the inductive remainder combine by repeated use of the reachability step principle (\texttt{AReach.step}).

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`.
