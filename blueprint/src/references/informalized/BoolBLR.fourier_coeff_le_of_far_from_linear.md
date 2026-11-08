<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.fourier_coeff_le_of_far_from_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Character Coefficient Bound from Farness

**Claim.** If a Boolean function is at least $\varepsilon$ far from every linear Boolean function, then every Fourier coefficient of its sign lift is at most $1-2\varepsilon$.

**Proof.** Fix $S$ and define $g(x)$ to be the parity of the number of true coordinates of $x$ that lie in $S$. Its sign lift is the character $\chi_S$: adding a coordinate with value true contributes a factor of $-1$, while a false coordinate contributes $1$. The characterization of linear Boolean functions by character lifts then shows that $g$ is linear (BoolBLR.linear_bool_iff_character). Since the original function is at least $\varepsilon$ far from this $g$, the coefficient-versus-distance inequality for a character lift gives $\widehat F(S)\le1-2\varepsilon$ (BoolBLR.fourier_coeff_le_of_dist_ge).

**Key facts.** `BooleanAnalysis.boolToSign_false`, `BooleanAnalysis.boolToSign_true`, `BoolBLR.linear_bool_iff_character`, `BoolBLR.fourier_coeff_le_of_dist_ge`.
