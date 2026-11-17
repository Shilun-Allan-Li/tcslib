<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.card_decodingCandidates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding Candidate Count Bound

**Claim.** For a regular unique game and a table of Boolean-valued functions on the Boolean cube, if $0<\varepsilon\le1$, then at every vertex the number of decoding candidates is at most $3/\varepsilon^2$.

**Proof.** The decoding candidates form the union of the notable coordinates and the notable coordinates of the averaged neighbor function. A union has size at most the sum of the sizes of its two sets. The notable-coordinate bound gives at most $2/\varepsilon^2$ (`card_notableCoordinates_le`), and the neighbor notable-coordinate bound gives at most $1/\varepsilon^2$ (`card_neighborNotableCoordinates_le`). Their sum is $3/\varepsilon^2$.

**Key facts.** `FABL.RegularUniqueGame.card_notableCoordinates_le`, `FABL.RegularUniqueGame.card_neighborNotableCoordinates_le`.
