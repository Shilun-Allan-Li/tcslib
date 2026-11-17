<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/FourierFourthMoment.lean :: FABL.expect_convolution_mul_self_eq_additiveEnergy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convolution and additive energy

**Claim.** The average square of the normalized self-convolution equals the average of $f(x)f(y)f(z)f(x+y+z)$ over three independent uniform cube elements.

**Proof.** Expand each convolution factor using its averaging formula: $(f*f)(t)=\mathbb E_a f(a)f(t+a)$ (`convolution_apply_add`). The product of the two averages is the joint average over $a,b$ of the product of their integrands, so the original expression becomes the average over $t,a,b$ of $f(a)f(t+a)f(b)f(t+b)$. Swap the finite averages to put $a$ first. For each fixed $a$, change variables from $t$ to $y=t+a$, a bijective translation of the cube. Because every element of the binary cube satisfies $a+a=0$, this also gives $t=y+a$, hence $t+b=a+y+b$. The integrand becomes $f(a)f(y)f(b)f(a+y+b)$. Renaming the three averaging variables as $x,y,z$ proves the identity.

**Key facts.** `FABL.convolution_apply_add`.
