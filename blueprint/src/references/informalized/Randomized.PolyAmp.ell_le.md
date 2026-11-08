<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.ell_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Representation Length Bound

**Claim.** For every natural number $n$, the length of its binary representation plus one is at most $n+1$.

**Proof.** The binary-length estimate `lt_two_pow_bits` says $n<2^{|\operatorname{bits}(n)|}$. The standard size characterization of natural numbers identifies $|\operatorname{bits}(n)|$ with the binary size of $n$, and the size bound gives $|\operatorname{bits}(n)|\le n$. Adding one to both sides yields $\ell(n)=|\operatorname{bits}(n)|+1\le n+1$.

**Key facts.** `Randomized.PolyAmp.lt_two_pow_bits`.
