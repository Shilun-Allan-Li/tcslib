<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.derivativeThresholdCrossMoment_le_half_influences -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cross moment bound by influences

**Claim.** For a real-valued function $p$ on the sign cube and distinct coordinates $i,j$, the expected product of the two input signs and the two thresholded discrete derivatives is at most half the sum of the influence in coordinate $j$ of the thresholded derivative in coordinate $i$ and the influence in coordinate $i$ of the thresholded derivative in coordinate $j$.

**Proof.** By the cross moment identity ($\texttt{FABL.derivativeThresholdCrossMoment\_eq\_expect\_derivatives}$), the left-hand side is the expectation of $D_jg_i\,D_ig_j$, where $g_i,g_j$ are the real-valued thresholded derivatives. For any real numbers $a,b$, $ab\le (a^2+b^2)/2$, since $(a-b)^2\ge0$. Apply this pointwise with $a=D_jg_i$ and $b=D_ig_j$, then average. Linearity of expectation over sums and constants identifies the resulting expression with $\bigl(I_j[g_i]+I_i[g_j]\bigr)/2$, as required.

**Key facts.** `FABL.derivativeThresholdCrossMoment_eq_expect_derivatives`.
