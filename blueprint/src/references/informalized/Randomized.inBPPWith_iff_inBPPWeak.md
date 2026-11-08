<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPAmplify.lean :: Randomized.inBPPWith_iff_inBPPWeak -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak-Error Characterization

**Claim.** For a natural number $c$, the length-dependent success bound $1/2+\min\{1/6,(n+1)^{-c}\}$ in the verifier definition is exactly the bound defining weak BPP with parameter $c$.

**Proof.** The two sides use the same polynomial-time verifier, random-bit length, and member and nonmember correctness conditions. By definition, the weak advantage at length $n$ is $\min\{1/6,(n+1)^{-c}\}$, so the threshold $1/2$ plus that advantage is precisely the threshold in the other definition. The propositions therefore coincide.
