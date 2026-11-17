<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.CsCounted.succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor update of counted state

**Claim.** If the counter cells record the key counts among indices below $i$, then updating the cell for key $kf(i)$ to its previous count plus one gives the counted-state invariant for indices below $i+1$.

**Proof.** The first counter cell is unchanged by the update, since its address differs from the updated cell; it therefore remains zero. Fix a key $t<A.nb$. The count of indices below $i+1$ with key $t$ equals the count below $i$, plus one exactly when $kf(i)=t$ (the count-successor formula, `cntEq_succ`). If $kf(i)=t$, the updated cell is precisely the one for $t$, and its new value is that previous count plus one. Otherwise the cell for $t$ is unchanged, and its count is unchanged as well. In either case it has the required value.

**Key facts.** `Light.cntEq_succ`.
