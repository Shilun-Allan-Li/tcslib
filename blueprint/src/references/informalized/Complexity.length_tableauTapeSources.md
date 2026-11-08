<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.length_tableauTapeSources -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape source-list length

**Claim.** For every finite-state Turing machine $M$ with Boolean input alphabet, all $n,t\in\mathbb{N}$, and each work tape $\tau$, the source list for tape $\tau$ at time $t$ has length $B+1$, where $B$ is the number of bits in a snapshot.

**Proof.** Split according to whether the tape has a previous visit at the current head position. If there is no such visit, the source list is a repetition of one constant of length $B+1$. If there is a previous visit, the list begins with one constant and is followed by a tableau block containing $B$ entries. In either case its length is $B+1$.
