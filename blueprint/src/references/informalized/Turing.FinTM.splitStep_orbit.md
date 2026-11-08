<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitStep_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit of the Split Step

**Claim.** For every Boolean word $w$ and every $i\le |w|+1$, applying the split-search step $i$ times to the empty word produces the unary word of length $i$.

**Proof.** Induct on $i$. At $i=0$, no steps have been applied, so the empty word is the replicate of zero true bits. For the successor case, the induction hypothesis gives the unary word of length $i$. Since $i<|w|+1$, we have $i\le |w|$, so the split step appends one true bit. The result is the unary word of length $i+1$.
