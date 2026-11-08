<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.uniform_expect_prod_le_prod_sqrt_expect_sq_twoRegular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Regular Product Expectation Bound

**Claim.** For nonnegative functions each depending only on its designated coordinates, if each coordinate is used by exactly two functions, the uniform expectation of their product is bounded by the product of their individual root-mean-square values.

**Proof.** Proceed by induction on the number $m$ of coordinates. For $m=0$, there is only one assignment, so each expectation is evaluation at that assignment. Nonnegativity gives $g_p=\sqrt{g_p^2}$ there, and the claimed inequality is equality.

For the induction step, separate the last coordinate from the first $m$ coordinates. Exactly two parts, say $p_1,p_2$, depend on this last coordinate. Fix an assignment of the first $m$ coordinates. Every other factor is constant as the last coordinate varies, by its dependence assumption. Call their product $C$, which is nonnegative. Cauchy–Schwarz bounds the average of the product of the two varying factors by the product of their root-mean-square values. Multiplying by $C$ therefore bounds the conditional average of the full product by the product of modified factors: for $p_1,p_2$, use their root-mean-square over the last coordinate; for every other part, retain its fixed value.

These modified factors remain nonnegative and depend only on their original coordinates among the first $m$. Each remaining coordinate still belongs to exactly two dependency sets. Apply the induction hypothesis to them. For each part, averaging the square of its modified factor over the first $m$ coordinates gives the original average of $g_p^2$: for a part containing the last coordinate this follows by averaging first over that coordinate, and for a part not containing it the factor is constant in that coordinate. The iterated averaging identity for a uniform product space ($\texttt{expect_fin_snoc}$) then identifies the resulting bound with the claimed product of root-mean-square values.

**Key facts.** `FABL.expect_fin_snoc`.
