<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.sum_finset_finTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum over two-element subsets

**Claim.** The sum of a real-valued function over all subsets of a two-element set is the sum of its values at the empty set, the two singleton sets, and the full set.

**Proof.** The subsets of the two-element set are exactly the empty set, the singleton containing the first element, the singleton containing the second element, and the full set (`univ_finset_finset_finTwo`). Listing these four terms in the finite sum gives the stated expression; rearranging their addition does not change the result.

**Key facts.** `FABL.univ_finset_finset_finTwo`.
