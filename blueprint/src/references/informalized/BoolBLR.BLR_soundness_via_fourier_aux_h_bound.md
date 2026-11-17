<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.BLR_soundness_via_fourier_aux_h_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Bound from Distance

**Claim.** If a Boolean function is at least $\varepsilon$ far from every linear Boolean function, then each Fourier coefficient of its sign lift is at most $1-2\varepsilon$.

**Proof.** Fix a subset $S$. Choose the Boolean parity function whose sign lift is the Walsh character indexed by $S$; the parity of the coordinates in $S$ has this lift. The characterization of linear Boolean functions by their character lifts shows that this parity function is linear (BoolBLR.linear_bool_iff_character). By the assumed distance condition, the original function is at least $\varepsilon$ far from this particular linear function. The coefficient-versus-distance inequality for a character lift therefore gives $\widehat F(S)\le1-2\varepsilon$ (BoolBLR.fourier_coeff_le_of_dist_ge).

**Key facts.** `BoolBLR.linear_bool_iff_character`, `BoolBLR.fourier_coeff_le_of_dist_ge`.
