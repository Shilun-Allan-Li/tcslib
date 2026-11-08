<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.evenMomentCoefficientGap_le_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment Gap Equivalence

**Claim.** For a finite probability law, the even-moment coefficient gap is nonpositive exactly when the moment is at most the sharp even-moment bound.

**Proof.** Set $c=\binom{2r}{2l}\,\rho^{2l}$, where $\rho=(2r-1)^{-1/2}$. Since $r>0$ and $l\le r$, both factors are positive, so $c>0$. The sharp coefficient identity says $c$ times the sharp bound equals $\binom rl$ (`sharp_even_coefficient_mul_bound`). By the definition of the gap, it is therefore $c$ times the difference between the moment and the sharp bound. For positive $c$, this difference is nonpositive exactly when the moment is at most the bound, proving both directions.

**Key facts.** `FABL.sharp_even_coefficient_mul_bound`.
