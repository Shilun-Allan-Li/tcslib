<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.khintchineKahane_constant_le_inv_sqrt_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp upper bound for the constant

**Claim.** If a constant $c$ satisfies the stated two-coordinate Khintchine–Kahane inequality for equal unit coefficients, then $c\le1/\sqrt2$.

**Proof.** For two equal unit coefficients, the first and second moments of the Rademacher norm are respectively $1$ and $2$ (`rademacherNorm_two_equal_weights_moments`). Substituting these values into the assumed inequality gives $c\sqrt{2}\le1$. Since $\sqrt2>0$, division by it yields $c\le1/\sqrt2$.

**Key facts.** `FABL.rademacherNorm_two_equal_weights_moments`.
