<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.fourThirdTwoHypercontractivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# (4/3, 2)-hypercontractivity

**Claim.** For every real-valued function on the sign cube, the $L^2$ norm of its noise-operator image at parameter $1/\sqrt{3}$ is at most its $L^{4/3}$ norm.

**Proof.** Write $T$ for the noise operator at parameter $1/\sqrt{3}$, $a=\|Tf\|_2$, and $b=\|f\|_{4/3}$. Both norms are nonnegative. The square of the $L^2$ norm is the uniform inner product of $Tf$ with itself (`uniformLpNorm_two_sq_eq_uniformInner`). By self-adjointness of the noise operator (`uniformInner_noiseOperator_left`), this is the inner product of $f$ with $T(Tf)$. Hölder's inequality bounds that inner product by $b\|T(Tf)\|_4$ (`uniformInner_le_uniformLpNorm_fourThird_mul_four`). Applying the $(2,4)$ hypercontractive inequality to $Tf$ bounds the latter $L^4$ norm by $a$ (`twoFourHypercontractivity`). Consequently $a^2\le ba$. If $a=0$, then $a\le b$ follows from $b\ge0$; if $a>0$, divide by $a$ to obtain the same conclusion.

**Key facts.** `FABL.uniformLpNorm_nonneg`, `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.uniformInner_noiseOperator_left`, `FABL.uniformInner_le_uniformLpNorm_fourThird_mul_four`, `FABL.twoFourHypercontractivity`.
