<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.lowDegreeFrequencies_eq_erase_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subsets Below Full Degree

**Claim.** For every $k$, the subsets of a set with $k+1$ elements having size at most $k$ are exactly all subsets except the full set.

**Proof.** Take any subset $S$ of the $(k+1)$-element set. If $|S|\le k$, then $S$ cannot be the full set, so it is among all subsets with the full set erased. Conversely, if $S$ is not the full set, then it has strictly fewer than $k+1$ elements. Since its size is an integer, $|S|\le k$. Thus the two families agree.
