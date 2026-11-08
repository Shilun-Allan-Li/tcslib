<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean :: BooleanAnalysis.ThresholdFunctions.finite_algebra -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Exponential Degree Bound

**Claim.** Under the stated hypotheses on $m,k,A,B,M$ and $t$, the inequalities imply $B\le\left((1+1/m)^{m+1}\right)^{2k}A^2$.

**Proof.** Set $C=1+1/m$ and $D=m/(m+1)$. Since $m\ge1$, these satisfy $C\ge1$, $D\ge0$, and $CD=1$. Substituting the given value of $t$ shows $t-1=D$, $2-t=1/(m+1)$, and $2/t=2(m+1)/(2m+1)$. Thus the interpolation hypothesis becomes $M\le A^{1/(m+1)}B^{m/(m+1)}$, while the other hypothesis becomes $D^kB\le M^{2(m+1)/(2m+1)}$.

Raise the latter inequality to the positive integer power $2m+1$; nonnegativity of its sides gives $(D^kB)^{2m+1}\le M^{2(m+1)}$ (`hc_pow`). The interpolation bound, raised to the corresponding power and using nonnegativity, gives $M^{2(m+1)}\le A^2B^{2m}$ (`interp_pow`). Combining these yields the two inequalities required by the cancellation estimate. Applying that estimate with $CD=1$ and $C\ge1$ gives $B\le(C^{m+1})^{2k}A^2$, which is the desired conclusion after substituting the definition of $C$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hc_pow`, `BooleanAnalysis.ThresholdFunctions.interp_pow`, `BooleanAnalysis.ThresholdFunctions.abstract_cancel`.
