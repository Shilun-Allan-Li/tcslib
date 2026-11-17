<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_coordinatePolarization_one_set_one_imp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainability after Polarization at Plus One

**Claim.** If the polarized function can attain $1$ from an input with coordinate $i$ set to $1$, then the original function can attain $1$ from at least one of the two corresponding inputs with coordinate $i$ set to $1$ or $-1$, changing only coordinates in $J$.

**Proof.** Choose a witness $y$ for attainability by the polarized function. Since $i\notin J$, its coordinate $i$ agrees with the starting input, so $y_i=1$. At this coordinate setting, polarization is the maximum of $f(y^{i\gets 1})$ and $f(y^{i\gets -1})$. If this maximum is $1$, one of the two values is $1$. For that choice $s\in\{1,-1\}$, take $y^{i\gets s}$ as the witness from $x^{i\gets s}$. These inputs agree outside $J$: at coordinate $i$ both have value $s$, while at every other coordinate the update leaves $y$ unchanged (`setCoordinate_apply_of_ne`).

**Key facts.** `FABL.setCoordinate_apply_of_ne`.
