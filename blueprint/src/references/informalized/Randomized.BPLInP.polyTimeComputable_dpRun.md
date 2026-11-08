<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.polyTimeComputable_dpRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Dynamic-Programming Run

**Claim.** For every finite nondeterministic Turing machine $N$ over bits and natural numbers $c,B,e$, the function mapping a bit string to the result of the associated dynamic-programming run is polynomial-time computable.

**Proof.** The run is an iteration of the dynamic-programming step, which is polynomial-time computable, starting from the polynomial-time computable initialization (Randomized.BPLInP.polyTimeComputable_dpStep and Randomized.BPLInP.polyTimeComputable_dpInit). The polynomial-iteration theorem reduces the claim to bounding the length of every intermediate encoding (Complexity.BinArith.polyTimeComputable_iterate). After $i$ steps, the iterate identity expresses the encoding as the context paired with a vector of $i$ rows (Randomized.BPLInP.iterate_dpInit); the context length is bounded by $2|x|+2s+4+V(2V+2)$, and the vector length by $V(2(2Vi+1)+2)$ (Randomized.BPLInP.length_ctxOf_le and Randomized.BPLInP.length_vecW_le), where $V=B(|x|+1)^e$ and $s=c(|	ext{bits}(|x|)|+1)$. The binary-length estimate $|	ext{bits}(n)|\le n$ (Turing.length_bits_le_self) gives $s\le c(|x|+1)$. Since $i\le B(|x|+1)^e$, the two length estimates, together with the pairing-length formula (Turing.length_pairEncode), are bounded by a fixed constant times $(|x|+1)^{3e+1}$. This supplies the required polynomial bound for every intermediate iterate and hence proves polynomial-time computability of the run.

**Key facts.** `Randomized.BPLInP.polyTimeComputable_dpStep`, `Randomized.BPLInP.polyTimeComputable_dpInit`, `Randomized.BPLInP.iterate_dpInit`, `Randomized.BPLInP.length_ctxOf_le`, `Randomized.BPLInP.length_vecW_le`, `Turing.length_bits_le_self`, `Turing.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_iterate`.
