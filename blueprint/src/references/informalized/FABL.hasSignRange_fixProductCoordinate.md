<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.hasSignRange_fixProductCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Range After Fixing a Coordinate

**Claim.** If a product function takes values only in $\{-1,1\}$, then fixing any one input coordinate to any chosen value produces a function that still takes values only in $\{-1,1\}$.

**Proof.** Take any input $x$. The coordinate-fixed function evaluates the original function at the input obtained by replacing coordinate $j$ of $x$ with $\omega$. By the assumed sign-range property of the original function, its value at that replaced input is either $-1$ or $1$. This holds for every $x$, proving the claim.
