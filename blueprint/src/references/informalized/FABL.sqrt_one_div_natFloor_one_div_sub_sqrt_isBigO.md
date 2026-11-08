<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.sqrt_one_div_natFloor_one_div_sub_sqrt_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Floor Approximation Error Bound

**Claim.** As $\delta$ tends to $0$ through nonnegative real values, $\sqrt{1/\lfloor1/\delta\rfloor}-\sqrt\delta$ is $O(\delta^{3/2})$.

**Proof.** It suffices to establish the bound on $0\le\delta\le\tfrac12$. At $\delta=0$ the expression vanishes. For $0<\delta\le\tfrac12$, write $q=1/\lfloor1/\delta\rfloor$. The reciprocal floor estimates (`reciprocal_natFloor_one_div_bounds`) give $\delta\le q$ and $q-\delta\le2\delta^2$. Thus $\sqrt\delta\le\sqrt q$, so the difference of square roots is nonnegative. Multiplying it by $\sqrt\delta$ and using $\sqrt q+\sqrt\delta\ge\sqrt\delta$ yields
\[
(\sqrt q-\sqrt\delta)\sqrt\delta
\le(\sqrt q-\sqrt\delta)(\sqrt q+\sqrt\delta)
=q-\delta\le2\delta^2.
\]
Because $\sqrt\delta>0$, division gives $\sqrt q-\sqrt\delta\le2\delta\sqrt\delta$. Finally, $\delta^{3/2}=\sqrt\delta^{\,3}=\delta\sqrt\delta$ for nonnegative $\delta$ (`sqrt_cube_eq_rpow_three_halves`). This proves the required bound with constant $2$ in a neighborhood of zero, hence the asserted big-O estimate.

**Key facts.** `FABL.reciprocal_natFloor_one_div_bounds`, `FABL.sqrt_cube_eq_rpow_three_halves`.
