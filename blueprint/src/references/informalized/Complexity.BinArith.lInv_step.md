<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.lInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Preservation of the Determinant Invariant

**Claim.** If $p\le Q$ and a determinant state satisfies the stated bounds on its rows, stored value, and counter, then one determinant step with parameter $p$ produces another state satisfying those bounds.

**Proof.** Write the state as $(R,d,m,rc)$ and use its invariant throughout. If $p<2$, the step leaves the state unchanged, so the invariant is preserved. Otherwise, if $R$ is empty, the state is again unchanged. For nonempty $R=r_0::rs$, first consider the branch $m\le rc$: the step resets the state to $([],0,0,0)$, which satisfies every clause of the invariant. In the branch $m>rc$, if the first entry of $r_0$ is zero, the step moves $r_0$ to the end of the row list and increments $rc$. The row count and each row's length and entry bounds are preserved by this rearrangement; the updated counter is at most $m$ because the old counter was strictly less than $m$. The stored value is either unchanged or replaced by $d(p-1)\bmod p$, which is less than $p\le Q$. In the remaining branch the first entry of $r_0$ is nonzero. The step replaces each row in $rs$ by its elimination row, changes the stored value to $d(r_0.headD\ 0)\bmod p$, decreases $m$ by one, and resets the counter. Each new row has length at most that of its source row by `length_elimRow`, so its length remains at most $K$. Every entry in an elimination row is less than $p$ by `lt_of_mem_elimRow`, hence less than or equal to $Q$ and, as an integer bound, strictly less than $Q$ using the branch arithmetic and the invariant's bounds. The new stored value is also less than $p\le Q$ by the remainder bound; the updated row count and counter satisfy the required inequalities. This establishes the invariant in every branch.

**Key facts.** `Complexity.BinArith.length_elimRow`, `Complexity.BinArith.lt_of_mem_elimRow`.

**Caveat.** The final entry-bound conclusion uses arithmetic in the proof that is not fully exposed by the two supplied upstream statements; in particular, the stated hypotheses alone include only $p\le Q$, while the proof's strict bound $x<Q$ from $x<p$ needs care when $p=Q$.
