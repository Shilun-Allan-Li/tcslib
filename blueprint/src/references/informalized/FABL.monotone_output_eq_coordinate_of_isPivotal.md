<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.monotone_output_eq_coordinate_of_isPivotal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output at a Pivotal Coordinate

**Claim.** If $f$ is monotone and flipping coordinate $i$ changes its value at $x$, then $f(x)=x_i$.

**Proof.** Write $x^+$ and $x^-$ for the inputs obtained from $x$ by setting coordinate $i$ to $1$ and $-1$, respectively. Since $x^-\le x^+$ coordinatewise, monotonicity gives $f(x^-)\le f(x^+)$. Pivotality says these two outputs differ. The sign values are only $-1$ and $1$, so the ordered pair must therefore be $f(x^-)=-1$ and $f(x^+)=1$. If $x_i=1$, then $x=x^+$ and consequently $f(x)=1=x_i$. If $x_i=-1$, then $x=x^-$ and consequently $f(x)=-1=x_i$.

**Key facts.** `FABL.isPivotal_iff_setCoordinate_ne`, `FABL.neg_one_le_sign`, `FABL.setCoordinate_apply_of_ne`, `FABL.setCoordinate_apply_self`, `FABL.setCoordinate_eq_self`, `FABL.sign_eq_neg_one_of_le_neg_one`, `FABL.sign_eq_one_of_one_le`.
