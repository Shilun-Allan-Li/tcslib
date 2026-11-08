<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.uniformExtendedNoiseMass_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal noise mass

**Claim.** For $m=|\Omega|\ge2$, the extended noise mass at $(x,x)$ is $\rho+(1-\rho)/m$.

**Proof.** On the diagonal the defining formula gives $\bigl(1+(m-1)\rho\bigr)/m$. The cardinality identity $m=(m-1)+1$ (`card_cast_eq_sub_one_add_one`) rewrites this numerator as $m\rho+(1-\rho)$, so division by $m$ gives the asserted expression. Division is valid because $m>0$, as follows from $m\ge2$ (`card_cast_pos`).

**Key facts.** `FABL.card_cast_pos`, `FABL.card_cast_eq_sub_one_add_one`.
