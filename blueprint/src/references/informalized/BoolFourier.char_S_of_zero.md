<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.char_S_of_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh character at the origin

**Claim.** For every $n$ and every subset $S$ of the coordinate set, the Walsh character $\chi_S$ evaluated at the all-zeros point is $1$.

**Proof.** At the all-zeros point, every coordinate has Boolean value false, whose sign is $1$. The character is the product of these signs over the coordinates in $S$, so every factor is $1$ and the product is $1; if $S$ is empty, the empty product is also $1$.
