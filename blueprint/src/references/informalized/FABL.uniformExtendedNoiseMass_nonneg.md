<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.uniformExtendedNoiseMass_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of extended noise mass

**Claim.** When $m=|\Omega|\ge 2$ and $-1/(m-1)\le\rho\le 1$, the extended noise mass at every pair $(x,y)$ is nonnegative.

**Proof.** Split according to whether $y=x$. If they are equal, the mass is $\bigl(1+(m-1)\rho\bigr)/m$. The lower bound on $\rho$, multiplied by the positive number $m-1$, gives $1+(m-1)\rho\ge0$; also $m>0$, so the quotient is nonnegative. The positivity facts for $m$ and $m-1$ follow from $m\ge2$ (`card_cast_pos`, `card_sub_one_cast_pos`). If $y\ne x$, the mass is $(1-\rho)/m$. Here $1-\rho\ge0$ by the upper bound on $\rho$, and $m>0$, so this quotient is nonnegative as well.

**Key facts.** `FABL.card_sub_one_cast_pos`, `FABL.card_cast_pos`.
