<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.main_add_four_div_sqrt_quotient_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square-root quotient identity

**Claim.** For every $m>0$, $\frac{\sqrt{2/\pi}\,\sqrt m+4/\sqrt m}{m}=\sqrt{2/\pi}\,\sqrt{1/m}+4(1/m)^{3/2}$.

**Proof.** Since $m>0$, its square root is positive and satisfies $(\sqrt m)^2=m$. Also $1/m\ge0$, so the square-root reciprocal identity gives $\sqrt{1/m}=1/\sqrt m$. The auxiliary identity $\sqrt{x}^{\,3}=x^{3/2}$ for nonnegative $x$ (FABL.sqrt_cube_eq_rpow_three_halves), applied to $x=1/m$, gives $(1/m)^{3/2}=1/(\sqrt m)^3$. Substituting these expressions into the right-hand side and using $(\sqrt m)^2=m$ reduces both sides to the same rational expression; clearing the positive denominators verifies the equality.

**Key facts.** `FABL.sqrt_cube_eq_rpow_three_halves`.
