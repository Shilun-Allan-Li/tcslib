<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.exists_two_div_pi_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The two-over-pi theorem

**Claim.** A single positive constant can be chosen so that the level-one Fourier weight has the stated upper bound and, when it is near $2/\pi$, the function is close to the sign of its level-one part.

**Proof.** Choose positive constants $C_u$ and $C_n$ from the level-one upper-bound theorem (`exists_two_div_pi_upper_constant`) and the near-extremizer theorem (`exists_two_div_pi_near_constant`), respectively. Set $C=C_u+C_n$, which is positive. The upper bound with error term $C_u\varepsilon$ implies the desired bound with $C\varepsilon$, since $C_n\varepsilon\ge0$. Under the near-extremality hypothesis, the second theorem gives distance at most $C_n\sqrt{\varepsilon}$. This is at most $C\sqrt{\varepsilon}$ because $\sqrt{\varepsilon}\ge0$ and $C_u\ge0$.

**Key facts.** `FABL.exists_two_div_pi_upper_constant`, `FABL.exists_two_div_pi_near_constant`.
