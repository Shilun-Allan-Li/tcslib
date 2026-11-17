<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.cube_norm_interpolation_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Norm Comparison by Interpolation

**Claim.** If $0<p<2<q$ and $\|f\|_q\le e^c\|f\|_2$, then $\|f\|_2\le\exp\!\left(\frac{cq(2-p)}{p(q-2)}\right)\|f\|_p$.

**Proof.** Write $A=\|f\|_p$ and $M=\|f\|_2$. If $M=0$, the claim follows from $A\ge0$ and positivity of the exponential. Otherwise $M>0$. Put $u=p(q-2)/(q-p)$ and $v=q(2-p)/(q-p)$. These satisfy $u>0$, $v\ge0$, and $u+v=2$. The moment interpolation inequality gives $\mathbb E f^2\le(\mathbb E|f|^p)^{(q-2)/(q-p)}(\mathbb E|f|^q)^{(2-p)/(q-p)}$. Using $\|f\|_p^p=\mathbb E|f|^p$, $\|f\|_q^q=\mathbb E|f|^q$, and $M^2=\mathbb E f^2$, this becomes $M^2\le A^u\|f\|_q^v$. The assumed bound and nonnegativity of the norms allow replacing $\|f\|_q$ by $e^cM$, giving $M^2\le A^u(e^cM)^v$. The interpolation cancellation inequality then yields $M\le e^{cv/u}A$ (\texttt{BooleanAnalysis.Hypercontractivity.lp_interpolation_cancel}). Finally, $cv/u=cq(2-p)/(p(q-2))$, which is the claimed exponent. The moment interpolation step is supplied by \texttt{BooleanAnalysis.Hypercontractivity.cube_moment_interpolation}; converting power means to moments uses \texttt{BooleanAnalysis.Hypercontractivity.cubeLpNorm_rpow}.

**Key facts.** `BooleanAnalysis.Hypercontractivity.cube_moment_interpolation`, `BooleanAnalysis.Hypercontractivity.cubeLpNorm_rpow`, `BooleanAnalysis.Hypercontractivity.lp_interpolation_cancel`.
