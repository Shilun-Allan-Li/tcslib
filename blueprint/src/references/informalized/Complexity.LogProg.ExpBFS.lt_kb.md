<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.lt_kb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Bound

**Claim.** For a finite nondeterministic Turing machine $N$ and natural numbers $n,s$, the exponent defining $\mathrm{kb}(N,n,s)$ is strictly less than $\mathrm{kb}(N,n,s)$.

**Proof.** Set $a=\mathrm{Codec.codeK}(N)(s+\mathrm{lgv}(n)+1)$. By definition, $\mathrm{kb}(N,n,s)=2^a$. The elementary natural-number bound that every exponent is strictly less than its power of two ($\mathrm{Nat.lt\_two\_pow\_self}$) gives $a<2^a$, as required.
