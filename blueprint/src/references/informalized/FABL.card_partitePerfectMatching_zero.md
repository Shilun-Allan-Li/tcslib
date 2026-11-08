<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_partitePerfectMatching_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matchings on Empty Parts

**Claim.** For every natural number $r$, there is exactly one perfect matching on zero vertices divided into $2r$ parts of size zero, with every matched pair in different parts.

**Proof.** When the part size is zero, the total number of vertices is zero, so the matching code has depth zero and is equivalent to the one-element type. The condition that every decoded edge joins different parts is vacuous, since there are no edges. Thus the valid matching codes are also equivalent to a one-element type, whose cardinality is one.
