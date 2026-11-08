<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.iterate_pow4Step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Growth Under Iteration

**Claim.** For every bit string $m$ and natural number $t$, iterating the fourth-power step $t$ times on the encoding of $(m,[1])$ yields an encoding of $(m,w)$ for some bit string $w$ whose length is $4^{\min(t,\operatorname{Nat.log}(4,|m|))}$.

**Proof.** Proceed by induction on $t$. At $t=0$, take $w=[1]$: the encoding is unchanged and its length is $1=4^0$. Suppose the claim holds at time $t$, with second component $w$ of length $4^{\min(t,\operatorname{Nat.log}(4,|m|))}$. The step forms four copies of this component, but keeps them only when their total length is at most $|m|$. The condition $4\cdot 4^{\min(t,\operatorname{Nat.log}(4,|m|))}\le |m|$ is equivalent to $t<\operatorname{Nat.log}(4,|m|)$; this follows from the defining threshold property of the natural logarithm, with the zero-length case handled separately. If $t$ is below that logarithm, the step accepts the four copies, and their length is $4$ times the previous length, giving the asserted exponent at time $t+1$. Otherwise it leaves $w$ unchanged; the minimum in the exponent has already reached the logarithm, so the required length remains the same. In both cases, the encoding decoder recovers the original first component and the selected second component (\texttt{Complexity.pairFstD_pairEncode}, \texttt{Complexity.pairSndD_pairEncode}).

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
