<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Interpolation.lean :: FABL.f₂PointIndicator_eq_ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Point indicator formula

**Claim.** For $a,x\in\mathbb F_2^n$, the product defining the point indicator equals $1$ if $x=a$ and $0$ otherwise.

**Proof.** If $x=a$, each coordinate factor is $1$: when $a_i=1$ the factor is $x_i=1$, and when $a_i=0$ it is $1-x_i=1$. Their product is therefore $1$. If $x\ne a$, some coordinate $i$ differs. When $a_i=1$, the differing bit must be $x_i=0$, so the factor $x_i$ vanishes. When $a_i=0$, the differing bit must be $x_i=1$, so the factor $1-x_i$ vanishes. In either case the whole product is zero. These are exactly the two values of the stated indicator.
