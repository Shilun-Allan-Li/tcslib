<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.char_is_degree_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characters have degree at most one

**Claim.** For every subset $S$, the Walsh character $\chi_S$ has degree at most one, so its second-order Gowers product is $1$ for every base point and pair of directions.

**Proof.** Fix a base point $x$ and directions $h_1,h_2$. A character is multiplicative across coordinatewise XOR: $\chi_S(a)\chi_S(a\oplus h)=\chi_S(h)$. Applying this identity first with $(a,h)=(x,h_1)$ and then with $(a,h)=(x\oplus h_2,h_1)$ reduces the four factors in the second-order Gowers product to $\chi_S(h_1)^2$. Every character takes values in $\{\pm1\}$, so its square is $1$ (`char_S_sq`). Thus the second-order product is $1$, as required.

**Key facts.** `BoolFourier.char_S_sq`.
