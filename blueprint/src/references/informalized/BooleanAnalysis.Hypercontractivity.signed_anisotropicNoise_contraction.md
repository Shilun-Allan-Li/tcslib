<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Contraction.lean :: BooleanAnalysis.Hypercontractivity.signed_anisotropicNoise_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contraction under signed product noise

**Claim.** For every $q>1$, there is $0<c\leq1$, with $c=2/5$ when $q=4$ or $q=4/3$, such that every stated finite product, sign vector, and function satisfy the asserted $q$-moment norm contraction under coordinate rates $cs_i$.

**Proof.** Choose $c$ from the uniform contraction theorem for negative coordinate noise. It gives $0<c\leq1$, the specified value in the two special cases, and contraction for a coordinate rate $-c$ on every finite product (\texttt{coordinate_noise_negative_contraction_allq}). For each coordinate, if the sign is positive, its rate is $c$; the positive-coordinate contraction theorem applies because $0\leq c\leq1$ and $q\geq1$ (\texttt{coordinate_noise_positive_contraction}). If the sign is negative, the chosen negative-coordinate theorem applies. Thus every coordinate noise step is contractive. The product-coordinate composition theorem then yields contraction for the full anisotropic noise transform (\texttt{anisotropicNoise_norm_le_of_coordinate}).

**Key facts.** `BooleanAnalysis.Hypercontractivity.coordinate_noise_negative_contraction_allq`, `BooleanAnalysis.Hypercontractivity.coordinate_noise_positive_contraction`, `BooleanAnalysis.Hypercontractivity.anisotropicNoise_norm_le_of_coordinate`.
