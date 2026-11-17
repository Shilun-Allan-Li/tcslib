<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_coordinatePolarization_one_set_neg_one_imp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainability after Polarization at Minus One

**Claim.** If the polarized function can attain $1$ from an input with coordinate $i$ set to $-1$, then the original function can attain $1$ from inputs with coordinate $i$ set to either $1$ or $-1$, changing only coordinates in $J$.

**Proof.** Choose a witness $y$ for attainability by the polarized function. Since $i\notin J$, the witness agrees with the starting input at coordinate $i$, so $y_i=-1$. At this coordinate setting, polarization takes the minimum of the two values $f(y^{i\gets 1})$ and $f(y^{i\gets -1})$. Their minimum is $1$, so each is at least $1$. Every value of $f$ is a sign and hence is at most $1$ (the sign bound `sign_le_one`); therefore both values equal $1$. For each $s\in\{1,-1\}$, use $y^{i\gets s}$ as a witness from the corresponding starting input $x^{i\gets s}$. Outside $J$, the two inputs agree: at coordinate $i$ they both equal $s$, and at every other coordinate the coordinate update leaves $y$ unchanged (`setCoordinate_apply_of_ne`).

**Key facts.** `FABL.sign_le_one`, `FABL.setCoordinate_apply_of_ne`.
