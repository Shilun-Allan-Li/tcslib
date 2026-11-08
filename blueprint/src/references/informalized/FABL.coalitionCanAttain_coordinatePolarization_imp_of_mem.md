<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_coordinatePolarization_imp_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainability under coordinate polarization

**Claim.** If the coordinate-polarized function attains $b$ at an input agreeing with $x$ outside $J$, where the polarized coordinate lies in $J$, then the original function also attains $b$ at some input agreeing with $x$ outside $J$.

**Proof.** Choose a witness $y$ where the polarized function attains $b$ and which agrees with $x$ outside $J$. Depending on whether $y_i=1$ or $y_i=-1$, the polarization at $y$ is respectively the maximum or minimum of the two values of $f$ obtained by setting coordinate $i$ to $1$ and to $-1$. Since that maximum or minimum equals $b$, one of those two endpoint values equals $b$. Use the corresponding endpoint as a witness for the original function. It agrees with $x$ at every coordinate outside $J$: at coordinates other than $i$, setting coordinate $i$ does not change the value, and the original witness already agrees with $x$ there; coordinate $i$ itself belongs to $J$, so no agreement is required there.

**Key facts.** `FABL.setCoordinate_apply_of_ne`.
