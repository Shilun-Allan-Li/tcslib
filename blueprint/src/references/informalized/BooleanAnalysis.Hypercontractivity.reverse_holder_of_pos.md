<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Holder.lean :: BooleanAnalysis.Hypercontractivity.reverse_holder_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-exponent reverse Hölder inequality

**Claim.** For $0<r<1$ and nonnegative functions $u,v$ on the Boolean cube, $\langle u,v\rangle\ge M_r(u)M_{r/(r-1)}(v)$.

**Proof.** Put $s=r/(r-1)<0$. If $u$ is positive somewhere and $v$ vanishes somewhere, then $M_s(v)=0$ by the definition of the extended mean, and the inequality follows because the inner product is nonnegative. Otherwise, when $u$ is positive somewhere, $v$ is positive everywhere. The normalized $r$-moment and $s$-moment of $u$ and $v$ are strictly positive (positivity of power moments, `ReverseMoments.expect_rpow_pos`). Let $A=M_r(u)$ and $B=M_s(v)$; in this case the positive-exponent formula for the mean and its negative-exponent counterpart identify these with the corresponding power means. Normalization gives $\mathbb E[(u/A)^r]=1$ and $\mathbb E[(v/B)^s]=1$ (`ReverseMoments.expect_normalized_rpow_eq_one`).

Apply the pointwise reverse Young inequality to $u(x)/A\ge0$ and $v(x)/B>0$, then average over the cube. The two normalized moment identities show that the average of the right-hand side is $1$, hence $\mathbb E[(u/A)(v/B)]\ge1$. Rescaling yields $\langle u,v\rangle\ge AB$; the identity expressing the inner product as $AB$ times this normalized expectation is `innerProduct_eq_mul_expect_div`. If $u$ is not positive anywhere, nonnegativity forces $u$ to vanish identically, and both sides are zero.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ReverseMoments.expect_rpow_pos`, `BooleanAnalysis.Hypercontractivity.ReverseMoments.expect_normalized_rpow_eq_one`, `BooleanAnalysis.Hypercontractivity.reverse_young`, `BooleanAnalysis.Hypercontractivity.innerProduct_eq_mul_expect_div`, `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.expect_eq_fintypeExpect`.
