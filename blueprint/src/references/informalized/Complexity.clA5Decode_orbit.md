<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Decode_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the Decoding State

**Claim.** For every binary word $w$ and natural number $j$, iterating the decoding step $j$ times from the state for $w$ at count zero gives the state for $w$ at count $j$.

**Proof.** Induct on $j$. At zero, zero iterations leave the initial state unchanged. For the successor case, the iterate after $j+1$ steps is one decoding step applied to the iterate after $j$ steps. By the induction hypothesis this is the state at count $j$; the one-step state-advance identity (`clA5DecodeStep_state`) then identifies it with the state at count $j+1$.

**Key facts.** `Complexity.clA5DecodeStep_state`.
