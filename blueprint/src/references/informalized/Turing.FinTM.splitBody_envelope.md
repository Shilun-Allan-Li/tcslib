<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitBody_envelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Envelope

**Claim.** Under the stated bounds on $l$ and $T$, one has $T+5l+3n+20\le ((C+1+5e)2^e+40)(n+1)^{e+1}$.

**Proof.** From $l\le n+1$, we have $l+1\le2(n+1)$, and raising both sides to $e$ gives $(l+1)^e\le2^e(n+1)^e\le2^e(n+1)^{e+1}$. The bound on $T$ then controls its contribution by $(C+1+5e)2^e(n+1)^{e+1}+1$. The remaining terms satisfy $5l+3n+21\le40(n+1)^{e+1}$: use $l\le n+1$ and $(n+1)^{e+1}\ge n+1$. Adding these estimates yields the claimed bound; expanding the coefficient confirms the right-hand side.
