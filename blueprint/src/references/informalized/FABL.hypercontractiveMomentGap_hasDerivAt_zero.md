<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.hypercontractiveMomentGap_hasDerivAt_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the moment gap at zero

**Claim.** For a finite nonempty set and any real-valued $X$, the hypercontractive moment gap is differentiable at zero with derivative $pq(1-\rho)\mathbb E X$.

**Proof.** Apply the differentiability result for the moment gap at a general parameter (FABL.hypercontractiveMomentGap_hasDerivAt) at $t=0$; both required positivity conditions hold there. At zero, each affine moment equals $1$ (FABL.affineMoment_zero), and each affine-moment derivative is its coefficient times $\mathbb E X$ (FABL.affineMomentDeriv_zero). Substitution into the moment-gap derivative gives $q(p\mathbb E X)-p(q\rho\mathbb E X)=pq(1-\rho)\mathbb E X$, as claimed.

**Key facts.** `FABL.hypercontractiveMomentGap_hasDerivAt`, `FABL.affineMomentDeriv_zero`, `FABL.affineMoment_zero`.
