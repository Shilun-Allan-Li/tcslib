<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_singleton_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainment by a Singleton Coalition

**Claim.** A coalition consisting only of coordinate $i$ can make $f$ equal $b$ from $x$ if and only if at least one of the two inputs obtained by setting coordinate $i$ to $1$ or $-1$ has function value $b$.

**Proof.** Given a witness $y$ that agrees with $x$ outside the singleton $\{i\}$, the inputs $y$ and $x^{i\gets y_i}$ agree at every coordinate: at $i$ they both have value $y_i$, and elsewhere the update leaves $x$ unchanged (`setCoordinate_apply_of_ne`). Every sign $y_i$ is either $1$ or $-1$. Hence $f(y)=b$ gives one of the two stated coordinate-fixed inputs with value $b$. Conversely, if either coordinate-fixed input has value $b$, use that input as the witness. It agrees with $x$ outside $\{i\}$ because the coordinate update changes no other coordinates (`setCoordinate_apply_of_ne`).

**Key facts.** `FABL.setCoordinate_apply_of_ne`.
