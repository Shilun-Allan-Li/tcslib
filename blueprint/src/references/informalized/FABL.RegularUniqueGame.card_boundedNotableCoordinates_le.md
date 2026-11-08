<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.card_boundedNotableCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Notable Coordinate Bound

**Claim.** For a regular unique game and a table of functions on the Boolean cube taking values in $[-1,1]$, if $0<\varepsilon\le 1$, then at every vertex the number of coordinates whose stable influence is at least $\varepsilon/2$ is at most $2/\varepsilon^2$.

**Proof.** The table function at the chosen vertex has variance at most one (`boundedCubeFunction_variance_le_one`). Since $0<\varepsilon\le1$, the threshold $\varepsilon/2$ also lies in $(0,1]$. The stable-influence counting bound (`card_stableInfluence_ge_le`) applied with noise parameter $\delta=\varepsilon$ and influence threshold $\varepsilon/2$ bounds the number of coordinates with influence at least $\varepsilon/2$ by $1/(\varepsilon(\varepsilon/2))$. Simplifying gives $2/\varepsilon^2$.

**Key facts.** `FABL.RegularUniqueGame.boundedCubeFunction_variance_le_one`, `FABL.card_stableInfluence_ge_le`.
