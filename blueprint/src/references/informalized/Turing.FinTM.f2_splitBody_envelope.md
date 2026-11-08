<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitBody_envelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial running-time envelope

**Claim.** For natural numbers $C,e,l,n,T$, if $l\le n+1$ and $T\le (C+1+5e)(l+1)^e+1$, then $T+5l+3n+20\le ((C+1+5e)2^e+40)(n+1)^{e+1}$.

**Proof.** Since $l\le n+1$, we have $l+1\le 2(n+1)$, and hence $(l+1)^e\le 2^e(n+1)^e\le 2^e(n+1)^{e+1}$. Multiplying by $C+1+5e$ and using the assumed bound on $T$ gives the desired contribution from $T$. Also $n+1\le(n+1)^{e+1}$, and the elementary bounds on the remaining linear terms give $5l+3n+21\le40(n+1)^{e+1}$. Adding these bounds yields the claimed inequality; rearranging the coefficient gives the displayed right-hand side.
