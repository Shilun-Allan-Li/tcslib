<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_partitePerfectMatching_four_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Four Singleton Parts

**Claim.** Among perfect matchings on four vertices divided into four singleton parts, exactly three have every matched pair in different parts.

**Proof.** The finite matching codes encode all pairings of the four vertices. For each code, the defining condition checks whether each of its two edges joins vertices in different parts. Exhaustively evaluating this finite condition leaves three valid codes, so the subtype of valid codes has cardinality three.

**Caveat.** The supplied proof is a kernel-checked finite computation; it does not expose a hand enumeration of the codes.
