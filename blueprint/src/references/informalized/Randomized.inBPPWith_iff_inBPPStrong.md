<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPAmplify.lean :: Randomized.inBPPWith_iff_inBPPStrong -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strong-Error Characterization

**Claim.** For a natural number $d$, the length-dependent success bound $1-(1/2)^{(n+1)^d+1}$ in the verifier definition is exactly the bound defining strong BPP with parameter $d$.

**Proof.** The verifier, efficiency condition, random-bit length, and correctness requirements on the two sides are the same. Their success thresholds also agree at every input length $n$: both are $1-(1/2)^{(n+1)^d+1}$. Hence the two definitions state the same proposition.
