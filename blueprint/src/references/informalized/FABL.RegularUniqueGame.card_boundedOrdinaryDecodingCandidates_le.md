<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.card_boundedOrdinaryDecodingCandidates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordinary Decoding Candidate Count

**Claim.** For a regular unique game with alphabet size $q$ and a table of functions on the Boolean cube taking values in $[-1,1]$, at every vertex the number of ordinary decoding candidates is at most $2q$.

**Proof.** The ordinary decoding candidates are the union of the influential coordinates of the vertex’s function and those of its averaged neighbor function. Each set is a subset of the $q$ coordinates, so each has size at most $q$. The union has size at most the sum of these sizes, hence at most $q+q=2q$.
