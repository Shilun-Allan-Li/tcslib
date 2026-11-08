<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.poolCode_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Formula for Pool Code

**Claim.** For every natural number $N$, the pool initialization code for $N+1$ entries is the code for $N$ entries followed by the instruction that adds one to the value at $c_{\mathrm{Pool}}(N)$ and stores the result at $c_{\mathrm{Pool}}(N+1)$.

**Proof.** By definition, the code begins with the subtraction that initializes the pool’s first address, followed by one addition instruction for each index in `List.range N`. The range successor formula splits `List.range (N+1)` into `List.range N` followed by the index $N$. Mapping the instruction construction over this decomposition gives exactly the code for $N$ entries followed by the stated addition instruction.
