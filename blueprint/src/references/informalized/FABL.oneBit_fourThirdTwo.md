<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.oneBit_fourThirdTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-bit $(4/3,2)$ hypercontractivity

**Claim.** For real $a,b$, the $2$-norm of the noisy affine function $a+3^{-1/2}b x$ on a uniform sign is at most the $4/3$-norm of $a+bx$.

**Proof.** Let $f(x)=a+bx$, let $u(x)=a+3^{-1/2}bx$, and let $v(x)=a+\frac13 bx$. Denote the two norms in the claim by $A=\|u\|_2$ and $B=\|f\|_{4/3}$. The squared $2$-norm identity expresses $A^2$ as the average of $u^2$. Expanding over the two signs shows this average equals the uniform inner product of $f$ and $v$: $A^2=\langle f,v\rangle$. Hölder's inequality for this inner product gives $\langle f,v\rangle\le \|f\|_{4/3}\|v\|_4$. The one-bit $(2,4)$ inequality (\texttt{oneBit\_twoFour}), applied to $v$ with noise parameter $1/\sqrt3$, gives $\|v\|_4\le A$, since its square is $1/3$ and its input coefficient is $3^{-1/2}b$. Therefore $A^2\le BA$. Both norms are nonnegative. If $A=0$, then $A\le B$ immediately; otherwise division by $A$ yields the desired bound.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`, `FABL.uniformInner_le_uniformLpNorm_fourThird_mul_four`, `FABL.oneBit_twoFour`.
