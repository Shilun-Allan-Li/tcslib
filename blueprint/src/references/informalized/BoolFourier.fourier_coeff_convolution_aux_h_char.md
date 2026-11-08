<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.fourier_coeff_convolution_aux_h_char -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character-Weighted Translation

**Claim.** For fixed $y$, translating the argument of $g$ by coordinatewise XOR with $y$ multiplies its character-weighted sum by $\chi_S(y)$.

**Proof.** Reindex the sum by the map $x\mapsto x\oplus y$. This map is a bijection of the Boolean cube: applying it twice returns the original vector, and every vector is attained. The character factor transforms according to the character-splitting identity `fourier_coeff_convolution_aux_h_split`, which states that $\chi_S(x)=\chi_S(x\oplus y)\chi_S(y)$. Substituting this identity after reindexing extracts the factor $\chi_S(y)$, leaving the character-weighted sum of $g$ over the cube.

**Key facts.** `BoolFourier.fourier_coeff_convolution_aux_h_split`.
