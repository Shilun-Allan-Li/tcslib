<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.scalar_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine scalar contraction

**Claim.** Assuming the scalar inequality and $q>0$, $0\le c\le1$, one has $|a-cx|^q\le |a+x|^q-[q(1+c)|a|^q/a]x$ for all real $a,x$, with the quotient term interpreted as zero at $a=0$.

**Proof.** If $a=0$, the inequality reduces to $|cx|^q\le|x|^q$. This follows from $0\le c\le1$ and monotonicity of the $q$th power on nonnegative reals. Otherwise, factor $a$ from each affine expression: $a-cx=a(1-cx/a)$ and $a+x=a(1+x/a)$. Taking absolute values and using multiplicativity of positive real powers, apply the assumed scalar inequality at $z=x/a$, multiplying it by the nonnegative factor $|a|^q$. Recombining the factors gives the asserted inequality and its linear correction term.
