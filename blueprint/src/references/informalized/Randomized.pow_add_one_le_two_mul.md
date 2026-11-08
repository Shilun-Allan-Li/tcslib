<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPHard.lean :: Randomized.pow_add_one_le_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Bound by a Shifted Power

**Claim.** For all natural numbers $n,e$, one has $n^e+1\le2(n+1)^e$.

**Proof.** Since $n\le n+1$, monotonicity of natural-number powers gives $n^e\le(n+1)^e$. Also $(n+1)^e\ge1$ for every $e$. Adding these two inequalities yields $n^e+1\le2(n+1)^e$.
