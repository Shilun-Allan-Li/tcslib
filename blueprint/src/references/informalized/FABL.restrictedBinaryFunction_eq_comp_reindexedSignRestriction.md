<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrictedBinaryFunction_eq_comp_reindexedSignRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary restriction by reindexing

**Claim.** Evaluating the restricted binary function on a full binary input agrees with evaluating the reindexed sign restriction after converting the selected coordinates to signs.

**Proof.** Fix a binary input and compare the two outputs. Both are obtained by applying $f$ to sign assignments with the same fixed values outside $J$. On a coordinate in $J$, the first construction reads the converted sign at that coordinate; the second reads the converted sign at its position under the enumeration of $J$. These coordinates agree by the definition of the free-coordinate embedding. Hence the sign assignments, and therefore their images under $f$, agree.
