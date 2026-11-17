<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.hypercontractiveMomentGapDeriv_hasDerivAt_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the moment gap at zero

**Claim.** For a mean-zero function $X$ on a finite nonempty set, the hypercontractive moment gap is differentiable at zero with derivative $pq((p-1)-(q-1)\rho^2)\mathbb E X^2$.

**Proof.** At $t=0$, both affine moments equal $1$ (FABL.affineMoment_zero), and their first derivatives are their respective coefficients times $\mathbb E X$ (FABL.affineMomentDeriv_zero). Their second derivative contributions are given by the affine-moment derivative formula at zero (FABL.affineMomentDeriv2_zero). The chain rule for the powered affine moments, together with the product rule for their derivatives, therefore computes the derivative of the moment-gap derivative expression at zero. Substituting $\mathbb E X=0$ removes the first-derivative terms, and the two second-derivative contributions combine to $pq((p-1)-(q-1)\rho^2)\mathbb E X^2$.

**Key facts.** `FABL.affineMoment_hasDerivAt`, `FABL.affineMomentDeriv_hasDerivAt`, `FABL.affineMoment_zero`, `FABL.affineMomentDeriv_zero`, `FABL.affineMomentDeriv2_zero`.
