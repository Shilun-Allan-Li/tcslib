<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_cpAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Configuration Slices

**Claim.** Fix a nondeterministic finite Turing machine $N$ and natural numbers $d,c,A,a$. If $o(y)$ can be output in unary in polynomial time, then the function sending $y$ to the slice of the second pair projection of $y$ beginning at offset $o(y)$ and having length $\mathrm{vlen}(N,d,c,|\mathrm{pairFstD}(y)|)$ is polynomial-time computable.

**Proof.** First, the second pair projection $\mathrm{pairSndD}$ is polynomial-time computable. Since the unary encoding of $o(y)$ is polynomial-time computable by hypothesis, polynomial-time closure under dropping a prefix gives the function $y\mapsto \mathrm{pairSndD}(y).\mathrm{drop}(o(y))$ as polynomial-time computable (the drop closure fact, `Complexity.TQBFHard.pt_drop`). Next, the unary encoding of the required slice length is polynomial-time computable by `pt_vlen`. Applying polynomial-time closure under taking a prefix to the dropped string, using this unary length, produces its prefix of length $\mathrm{vlen}(N,d,c,|\mathrm{pairFstD}(y)|)$. This is exactly the specified slice.

**Key facts.** `Complexity.TQBFHard.pt_drop`, `Complexity.TQBFHard.pt_take`, `Complexity.TQBFHard.pt_vlen`, `Complexity.polyTimeComputable_pairSndD`.
