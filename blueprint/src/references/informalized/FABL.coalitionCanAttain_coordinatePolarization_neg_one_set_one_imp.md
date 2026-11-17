<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_coordinatePolarization_neg_one_set_one_imp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainability from both settings of a coordinate

**Claim.** If the polarized function attains $-1$ at an input agreeing with the input obtained from $x$ by setting coordinate $i$ to $1$, outside $J$, where $i\notin J$, then the original function attains $-1$ with coordinate $i$ set to either $1$ or $-1$, with the required agreement outside $J$ in each case.

**Proof.** Let $y$ witness the assumption. Since $i\notin J$, the agreement condition gives $y_i=1$. The polarized value at $y$ is therefore the maximum of the two values of the original function obtained by setting coordinate $i$ to $1$ and to $-1$. This maximum is $-1$, so each of the two values is at most $-1$. Every sign is at least $-1$ (\texttt{neg\_one\_le\_sign}), hence both values equal $-1$. For each setting, use the corresponding endpoint of $y$ as a witness. It agrees at coordinate $i$ with the input obtained from $x$ using that setting, and at every other coordinate outside $J$ it agrees because setting coordinate $i$ leaves those coordinates unchanged and $y$ already agrees with the input set to $1$ (\texttt{setCoordinate\_apply\_of\_ne}).

**Key facts.** `FABL.neg_one_le_sign`, `FABL.setCoordinate_apply_of_ne`.
