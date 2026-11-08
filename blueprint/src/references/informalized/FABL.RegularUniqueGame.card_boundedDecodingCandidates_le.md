<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.card_boundedDecodingCandidates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Decoding Candidate Count

**Claim.** For a regular unique game and a table of functions on the Boolean cube taking values in $[-1,1]$, if $0<\varepsilon\le 1$, then at every vertex the number of bounded decoding candidates is at most $3/\varepsilon^2$.

**Proof.** The bounded decoding candidates are the union of the notable coordinates and the notable coordinates of the averaged neighbor function. The size of a union is at most the sum of the two sizes. The notable-coordinate bound gives at most $2/\varepsilon^2$ for the first set (`card_boundedNotableCoordinates_le`), and the neighbor notable-coordinate bound gives at most $1/\varepsilon^2$ for the second (`card_boundedNeighborNotableCoordinates_le`). Adding these bounds yields $3/\varepsilon^2$.

**Key facts.** `FABL.RegularUniqueGame.card_boundedNotableCoordinates_le`, `FABL.RegularUniqueGame.card_boundedNeighborNotableCoordinates_le`.
