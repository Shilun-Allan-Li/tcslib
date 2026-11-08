<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.khintchine_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Khintchine bounds for $p\ge2$

**Claim.** For a sign-cube linear form and $p\ge2$, its $L_2$ norm is at most its $L_p$ norm, which in turn is at most $\sqrt{p-1}$ times its $L_2$ norm.

**Proof.** Monotonicity of uniform norms gives $\|L\|_2\le\|L\|_p$ (`uniformLpNorm_mono`). Also, a linear form has Fourier degree at most one (`fourierDegree_linearForm_le_one`). Applying the degree-$k$ upper estimate with $k=1$ yields $\|L\|_p\le\sqrt{p-1}\,\|L\|_2$ (`lowDegree_uniformLpNorm_le`). Together these are the two claimed bounds.

**Key facts.** `FABL.uniformLpNorm_mono`, `FABL.fourierDegree_linearForm_le_one`, `FABL.lowDegree_uniformLpNorm_le`.
