<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.norm_interpolation_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpolation between product norms

**Claim.** If $q>2$ and $\|f\|_{q,P}\le e^c\|f\|_{2,P}$, then $\|f\|_{2,P}\le e^{cq/(q-2)}\|f\|_{1,P}$.

**Proof.** All moments and norms involved are nonnegative, since product masses are nonnegative. If $\|f\|_{2,P}=0$, the conclusion follows immediately. Otherwise put $M=\|f\|_{2,P}>0$, $u=(q-2)/(q-1)>0$, and $v=q/(q-1)\ge0$; then $u+v=2$. Hölder's inequality in weighted $L^p$ form, applied to $|f|$ and $|f|^{q-1}$, gives $\mathbb E_P|f|^2\le(\mathbb E_P|f|)^u(\mathbb E_P|f|^q)^{1/(q-1)}$. Rewriting moments as powers of the corresponding norms turns this into $M^2\le A^u\|f\|_{q,P}^v$, where $A=\|f\|_{1,P}$. The assumed bound gives $M^2\le A^u(e^cM)^v$. The interpolation cancellation inequality ($\texttt{lp\_interpolation\_cancel}$), with $A\ge0$, $M>0$, $u>0$, and $u+v=2$, now implies $M\le e^{cv/u}A$. Finally, $v/u=q/(q-2)$, yielding the claimed estimate.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lp_interpolation_cancel`.
