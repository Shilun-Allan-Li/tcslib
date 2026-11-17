<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nsem_addTwice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Register Addition

**Claim.** The two increments of $p$ and one increment of $k$ per loop iteration preserve the stated terminating semantics, taking the configuration at $\mathrm{test}$ to the given configuration at $\mathrm{ex}$.

**Proof.** Strengthen the claim to all loop lengths $c=v(y)-v(k)$, with the post-loop values obtained by adding $2c$ to $p$ and setting $k$ to $v(y)$. If $c=0$, then $v(k)=v(y)$, so the test takes its equality branch directly to $\mathrm{ex}$; the resulting register assignment is unchanged, and the equality case of the register-test semantics gives the result. For the successor case, $v(k)\ne v(y)$. Execute the three specified instructions: increment $p$ twice, then increment $k$. The registers are distinct, so the resulting assignment $v_3$ has $v_3(p)=v(p)+2$, $v_3(k)=v(k)+1$, and $v_3(y)=v(y)$. The register bound is maintained at each increment: the intermediate $p$ values fit under $B$ by the assumed bound on $v(p)+2(c+1)$, and the incremented $k$ fits because it remains at most $v(y)$. The remaining gap is $c$, so apply the induction hypothesis at $v_3$. Its prescribed endpoint agrees with the original endpoint: the total increase to $p$ is $2+2c=2(c+1)$, and the final value of $k$ is still $v(y)$. Reassemble the loop: the unequal-register test takes the non-equality branch, followed by the two increments of $p$ and the increment of $k$. The register-update bound lemma (`register_update_le`) justifies the guard at each intermediate configuration; the semantics rules for unequal tests and increments (`NSem.jeq_neg`, `NSem.inc`) then yield the claimed semantics at the original test state.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.NSem.jeq_pos`, `Complexity.LogProg.NSem.jeq_neg`, `Complexity.LogProg.NSem.inc`.
