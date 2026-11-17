<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean :: Complexity.length_adjWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the adjacency word

**Claim.** For $A:\{0,\ldots,n-1\}\times\{0,\ldots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$, the concatenated adjacency word has length $n^2$.

**Proof.** There are $n$ choices for the first coordinate. For each choice, the list of values over the $n$ second coordinates has length $n$. The length of a concatenation of lists is the sum of their lengths, so the resulting word has length $n\cdot n=n^2$.
