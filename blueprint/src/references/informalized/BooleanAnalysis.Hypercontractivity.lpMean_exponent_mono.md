<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoFunction.lean :: BooleanAnalysis.Hypercontractivity.lpMean_exponent_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Extended Power Means

**Claim.** For $a\le b\le1$ and a nonnegative function $f$ on the Boolean cube, $M_a(f)\le M_b(f)$.

**Proof.** First, the proof establishes three comparison principles for the different exponent ranges. For positive exponents $0<a\le b$, set $t=b/a\ge1$. Jensen's inequality for the convex power function gives $(\mathbb E f^a)^t\le\mathbb E(f^a)^t=\mathbb E f^b$. Applying the increasing power $1/b$ to these nonnegative moments, and using the real-power product law, yields $M_a(f)\le M_b(f)$; the positive-exponent formula for the extended mean is `lpMean_of_pos`. For negative exponents $a\le b<0$, first handle a zero of $f$: by the definition of the extended mean, both means are zero. Otherwise $f$ is strictly positive everywhere. Now $t=a/b\ge1$, and Jensen applied to $f^b$ gives $(\mathbb E f^b)^t\le\mathbb E f^a$. Since taking the power $1/a$ reverses order for negative $a$, this yields the desired comparison. The same positive Jensen comparison also shows $M_a(f)\le M_0(f)$ when $a<0$: apply concavity of logarithm to the positive function $f^a$ to obtain $a\,\mathbb E\log f\le\log\mathbb E f^a$, then divide by the negative number $a$ and exponentiate. In the reverse crossing, logarithmic Jensen applied to $f^b$ gives $\mathbb E\log f\le (\log\mathbb E f^b)/b$ when $b>0$, hence $M_0(f)\le M_b(f)$. If $f$ has a zero, the latter follows directly because $M_0(f)=0$ and positive-exponent means are nonnegative. Finally, order $b$ relative to zero. If $b<0$, then $a\le b<0$ and the negative-exponent comparison applies. If $b=0$, use the negative-to-zero comparison (or equality when $a=0$). If $b>0$, split according as $a<0$, $a=0$, or $a>0$: use the relevant crossing comparison, equality, or the positive-exponent comparison, respectively. These cases cover all $a\le b\le1$; the upper bound $b\le1$ is permitted throughout and is used in the stated Jensen comparisons.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.expect_eq_fintypeExpect`.
