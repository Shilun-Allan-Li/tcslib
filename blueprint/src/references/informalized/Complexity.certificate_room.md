<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.certificate_room -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Room for a marker bit

**Claim.** For all $C,c,n\in\mathbb{N}$, $C(n+1)^c+1\le (C+1)(n+1)^c$.

**Proof.** Since $n+1\ge1$, its $c$th power is at least $1$. Expanding $(C+1)(n+1)^c$ as $C(n+1)^c+(n+1)^c$ shows that it is at least $C(n+1)^c+1$.
