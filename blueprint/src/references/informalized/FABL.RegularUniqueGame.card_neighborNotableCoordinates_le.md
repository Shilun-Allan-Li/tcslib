<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.card_neighborNotableCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Notable Neighbor Coordinates

**Claim.** For a regular unique game and a table of Boolean functions, if $0<\varepsilon\le1$, then at any vertex the number of coordinates whose stable influence at parameter $1-\varepsilon$ in the averaged permutation-adjusted neighbor function is strictly greater than $\varepsilon$ is at most $1/\varepsilon^2$.

**Proof.** Enlarge the set of coordinates with stable influence strictly greater than $\varepsilon$ to the set with influence at least $\varepsilon$. The averaged neighbor function has variance at most one (`boundedCubeFunction_variance_le_one`). The stable-influence counting bound (`card_stableInfluence_ge_le`) shows that, for variance at most one, the number of coordinates with influence at least a threshold $\eta$ is at most $1/(\delta\eta)$ when the noise parameter $\delta$ and threshold both lie in $(0,1]$. Taking both parameters to be $\varepsilon$ gives $1/\varepsilon^2$. The original strict-threshold set is no larger.

**Key facts.** `FABL.RegularUniqueGame.boundedCubeFunction_variance_le_one`, `FABL.card_stableInfluence_ge_le`.
