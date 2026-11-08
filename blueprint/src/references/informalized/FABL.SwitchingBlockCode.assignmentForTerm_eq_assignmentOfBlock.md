<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.assignmentForTerm_eq_assignmentOfBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Term assignment descriptions agree

**Claim.** For a term of width at most $w$, the assignment defined directly from the term and a width-$w$ switching block code agrees with the assignment obtained through the term-position construction.

**Proof.** Compare the assignments at each variable index $i$. If $i$ is outside the term’s support, both definitions assign zero. If $i$ is in the support, both use the code bit at the position associated with that literal and add the bit encoding its required sign. The width bound ensures that this position is among the $w$ available code positions, so the direct definition’s range condition holds. The two coordinate values are therefore identical in either case, proving equality of assignments.
