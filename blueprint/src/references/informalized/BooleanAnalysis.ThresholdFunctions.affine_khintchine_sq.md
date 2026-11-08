<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/AffineKhintchine.lean :: BooleanAnalysis.ThresholdFunctions.affine_khintchine_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First and Second Moments for Affine Polynomials

**Claim.** If the Walsh polynomial $P$ has coefficients vanishing on sets of size greater than one, then $\sum_S p(S)^2\le 2\bigl(\mathbb E|P|\bigr)^2$.

**Proof.** Set $g(x)=|P(x)|$. The Walsh inner-product identity gives $\langle g,g\rangle=\sum_S p(S)^2$, since $g(x)^2=P(x)^2$ and the Walsh characters are orthonormal (BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.innerProduct_eval_self). Taking absolute values cannot increase influence, so $I[g]\le I[P]$ (BooleanAnalysis.ThresholdFunctions.influence_abs_le). Moreover, the degree-one antipode identity says $P(x)+P(-x)=2p(\varnothing)$ (BooleanAnalysis.ThresholdFunctions.affine_sum_antipode). The inequality $\bigl||u|-|v|\bigr|\le|u-v|$, applied with $u=P(x)$ and $v=-P(-x)$, therefore bounds the difference between $g$ at antipodal points by $2|p(\varnothing)|$. The antipodal bound on level-one weight then gives $W_1(g)\le p(\varnothing)^2$ (BooleanAnalysis.ThresholdFunctions.weightLevel1_antipode_le). The spectral inequality for an arbitrary function states that $2(\langle g,g\rangle-(\mathbb E g)^2)\le I[g]+W_1(g)$ (BooleanAnalysis.ThresholdFunctions.spectral_inequality). Combining these bounds with the degree-one influence identity $I[P]+p(\varnothing)^2=\sum_Sp(S)^2$ (BooleanAnalysis.ThresholdFunctions.affine_influence), and using $\langle g,g\rangle=\sum_Sp(S)^2$, yields $2(\langle g,g\rangle-(\mathbb E g)^2)\le\langle g,g\rangle$. Rearrangement gives the claimed bound, since $\mathbb E g=\mathbb E|P|$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.innerProduct_eval_self`, `BooleanAnalysis.ThresholdFunctions.influence_abs_le`, `BooleanAnalysis.ThresholdFunctions.weightLevel1_antipode_le`, `BooleanAnalysis.ThresholdFunctions.affine_sum_antipode`, `BooleanAnalysis.ThresholdFunctions.spectral_inequality`, `BooleanAnalysis.ThresholdFunctions.affine_influence`.
