<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.degreeTruncation_eq_self_of_fourierDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier truncation recovers the function

**Claim.** If the Fourier degree of $f$ is at most $k$, then truncating its Fourier expansion to sets of size at most $k$ gives $f$ itself.

**Proof.** Fix a point $x$. Expand both the degree-$k$ truncation and $f$ in their full Fourier expansions (`fourier_expansion`). Their coefficients at a set $S$ agree whenever $|S|\le k$, by the coefficient formula for truncation (`fourierCoeff_degreeTruncation`). If $|S|>k$, the degree hypothesis forces the coefficient of $f$ at $S$ to vanish (`fourierDegree_le_iff`), and the truncation coefficient is also zero. Hence every term in the two expansions agrees, so their values at $x$ agree. Since $x$ was arbitrary, the functions are equal.

**Key facts.** `FABL.fourier_expansion`, `FABL.fourierCoeff_degreeTruncation`, `FABL.fourierDegree_le_iff`.
