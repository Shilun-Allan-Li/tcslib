<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.sum_char_S_ne_zero_aux_h_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character Sum Sign Symmetry

**Claim.** At any nonzero Boolean-cube point with a true coordinate, the sum of all Walsh characters equals the sum of their negatives.

**Proof.** Pair each subset $S$ of coordinates with the subset obtained by toggling membership of $i$: remove $i$ when it is present, and add $i$ when it is absent. This toggle is an involution, and the chosen coordinate is in exactly one member of each pair. Since $x_i$ is true, its sign is $-1$; hence toggling membership of $i$ changes the product defining the Walsh character by a factor of $-1$. Thus each summand is matched with its negative, so summing over all subsets gives the asserted equality.
