<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.forLoop_bound_of_ctx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Iterated Context Length

**Claim.** Under the stated preservation and length-growth assumptions on $f$, every iterate $f^j(d)$ with $j\le |c|$ has length at most $(A+1)(|\langle c,d\rangle|+1)^2$.

**Proof.** Let $N=|\langle c,d\rangle|$. The iterate-length estimate under a preserved first projection (`length_iterate_le_of_ctx`) bounds $|f^j(d)|$ by $|d|+jA(|\pi_1(d)|+1)$. The first projection has length at most the input length (`length_pairFstD_le`), while the encoding length formula gives $|c|+|d|\le N$ and hence bounds both $j$ and $|d|$ by $N$, as well as $|\pi_1(d)|$ by $N$. Consequently the iterate length is at most $N+NA(N+1)$. This is at most $(A+1)(N+1)^2$ by elementary arithmetic, proving the desired bound.

**Key facts.** `Complexity.BinArith.length_iterate_le_of_ctx`, `Complexity.length_pairFstD_le`, `Turing.length_pairEncode`.
