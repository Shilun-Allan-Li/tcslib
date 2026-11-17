<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_span_extend -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending a Marked Span

**Claim.** Updating the closed-span marker for $[\ell,h]$ to be true at $p$, when $\ell-1\le p\le h+1$, gives the closed-span marker for $[\min(\ell,p),\max(h,p)]$.

**Proof.** Compare the two marker functions at an arbitrary integer $z$. If $z=p$, the updated function is true there, and $p$ belongs to the enlarged interval because it is at least $\min(\ell,p)$ and at most $\max(h,p)$. If $z\ne p$, the update leaves its value unchanged. In this case, membership in $[\ell,h]$ is equivalent to membership in the enlarged interval: the bounds on $p$ say that extending either endpoint reaches at most one step beyond the old interval, and any newly included integer can only be $p$. Thus the two functions agree at every $z$.
