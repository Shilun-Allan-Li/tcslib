<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.unaryRest_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Rest Characterization

**Claim.** For every binary word $x$ and natural number $n$, the unary-rest condition with length $n$ is equivalent to the doubled-prefix condition for the word of $n$ ones.

**Proof.** At each index $i<n$, the replicated word has value $1$; this follows directly from the indexed-value rule for a replicated list. Unfolding the two conditions, the universal requirements therefore agree: each pair of positions $2i,2i+1$ in $x$ must equal the corresponding value in the replicated word, which is $1$. The remaining two requirements in both conditions are exactly that positions $2n$ and $2n+1$ contain $0$ and $1$, respectively. Each condition thus implies the other.
