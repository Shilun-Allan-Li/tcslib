<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.card_boundedNeighborNotableCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Neighbor Notable Coordinate Bound

**Claim.** For a regular unique game and a table of functions on the Boolean cube taking values in $[-1,1]$, if $0<\varepsilon\le 1$, then at every vertex the number of coordinates whose stable influence in the averaged neighbor function exceeds $\varepsilon$ is at most $1/\varepsilon^2$.

**Proof.** Consider the set of coordinates whose stable influence at parameter $1-\varepsilon$ is at least $\varepsilon$. Every coordinate counted as neighbor notable has influence strictly greater than $\varepsilon$, so it belongs to this larger set. The averaged neighbor function has variance at most one (`boundedCubeFunction_variance_le_one`). The stable-influence counting bound says that for a function of variance at most one, the number of coordinates with influence at least the threshold is at most $1/(\delta\varepsilon)$ (`card_stableInfluence_ge_le`). Apply it with both parameters equal to $\varepsilon$ to obtain $1/\varepsilon^2$; the strict threshold set is no larger.

**Key facts.** `FABL.RegularUniqueGame.boundedCubeFunction_variance_le_one`, `FABL.card_stableInfluence_ge_le`.
