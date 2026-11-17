<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.iterate_dpStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Dynamic-Programming Update

**Claim.** Applying the dynamic-programming update $t$ times to the pairing of the context for $x,s,V$ and the initial encoded value vector gives the pairing of that same context with the encoded vector of dynamic-programming values at time $t$.

**Proof.** Proceed by induction on $t$. At time zero, iterating a function zero times leaves the initial pairing unchanged, which is exactly the asserted time-zero vector. For the successor step, apply the update once after the $t$-fold iterate. The induction hypothesis identifies the result of those first $t$ updates as the context paired with the vector at time $t$. The one-step update formula (`Randomized.BPLInP.dpStep_eq`) says that the next update preserves this context and changes the vector to its time-$(t+1)$ version, proving the successor case.

**Key facts.** `Randomized.BPLInP.dpStep_eq`.
