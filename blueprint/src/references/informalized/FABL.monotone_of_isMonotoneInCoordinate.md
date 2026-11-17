<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.monotone_of_isMonotoneInCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise Monotonicity

**Claim.** If changing any one coordinate from $-1$ to $1$ never decreases $f$, then $f$ is monotone on the sign cube.

**Proof.** Take inputs $x\le y$ coordinatewise, and let $J$ be the set of coordinates where they differ. The one-sided sign order implies that on each coordinate in $J$, $x_i=-1$ and $y_i=1$: indeed, if $y_i=-1$, then $x_i\le -1$, forcing $x_i=-1$ as well, contrary to the definition of $J$. Thus changing precisely the coordinates in $J$ of $x$ to $1$ produces $y$. The coordinatewise monotonicity hypothesis, applied successively over those coordinates, says that this change cannot decrease $f$. Hence $f(x)\le f(y)$, as required.

**Key facts.** `FABL.le_bribeInput_one_of_isMonotoneInCoordinate`, `FABL.neg_one_le_sign`.
