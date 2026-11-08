<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_partitePerfectMatching_four_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Four Parts of Size Two

**Claim.** Among perfect matchings on eight vertices divided into four parts of size two, exactly sixty have every matched pair in different parts.

**Proof.** The finite matching codes encode all pairings of the eight vertices. The defining condition retains precisely those codes for which every edge joins vertices in different parts. Evaluating this finite predicate over the codes gives sixty valid matchings.

**Caveat.** The supplied proof is a kernel-checked finite computation; it does not expose a hand enumeration of the codes.
