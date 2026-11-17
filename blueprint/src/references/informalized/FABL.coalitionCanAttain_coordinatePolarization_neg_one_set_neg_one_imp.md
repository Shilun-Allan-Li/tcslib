<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_coordinatePolarization_neg_one_set_neg_one_imp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainability after setting a coordinate to minus one

**Claim.** If the polarized function attains $-1$ at an input agreeing with the input obtained from $x$ by setting coordinate $i$ to $-1$, outside $J$, and $i\notin J$, then the original function attains $-1$ at an input agreeing with $x$ with coordinate $i$ set to $1$, or with coordinate $i$ set to $-1$, outside $J$.

**Proof.** Let $y$ witness the assumed attainability. Because $i\notin J$, the agreement condition forces $y_i=-1$. Thus the polarized value at $y$ is the minimum of the two values of the original function obtained by setting coordinate $i$ to $1$ and to $-1$. Since this minimum is $-1$, one of the two values is $-1$. Use that endpoint of $y$ as a witness for the corresponding conclusion. At coordinate $i$ it agrees with the input obtained from $x$ by the same setting; at every other coordinate outside $J$, changing coordinate $i$ has no effect, and $y$ already agrees with that input. This uses the fact that setting a coordinate leaves all other coordinates unchanged (\texttt{setCoordinate\_apply\_of\_ne}).

**Key facts.** `FABL.setCoordinate_apply_of_ne`.
