<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.uniformLpNorm_two_interpolation_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpolation Inequality for the Uniform Norm

**Claim.** For a finite nonempty set $\Omega$, positive $p,q$, and $0<\theta<1$ satisfying $\frac12=\frac{\theta}{p}+\frac{1-\theta}{q}$, every $f:\Omega\to\mathbb R$ satisfies $\|f\|_2^2\le \|f\|_p^{2\theta}\|f\|_q^{2(1-\theta)}$.

**Proof.** Set $a=p/(2\theta)$ and $b=q/(2(1-\theta))$. The hypotheses imply $a>1$, and the relation among $p,q,\theta$ gives $1/a+1/b=1$; thus $a,b$ are Hölder conjugates. Define $u(x)=|f(x)|^{2\theta}$ and $v(x)=|f(x)|^{2(1-\theta)}$. Their pointwise product is $f(x)^2$: when $f(x)\ne0$, combine the exponents, and when $f(x)=0$, both positive powers vanish. Consequently the uniform inner product of $u$ and $v$ is the second moment of $f$, which equals $\|f\|_2^2$ by `uniformLpNorm_two_sq_eq_expect_sq`. Hölder's inequality for the uniform inner product (`uniformInner_le_uniformLpNorm_mul`) bounds it by $\|u\|_a\|v\|_b$. Finally, the norm scaling identity `uniformLpNorm_abs_rpow` gives $\|u\|_a=\|f\|_p^{2\theta}$ and $\|v\|_b=\|f\|_q^{2(1-\theta)}$, proving the inequality.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`, `FABL.uniformInner_le_uniformLpNorm_mul`, `FABL.uniformLpNorm_abs_rpow`.
