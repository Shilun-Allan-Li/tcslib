<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.guideTape_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Origin Marker Location

**Claim.** For every natural number $R$ and integer $z$, the guide tape of radius $R$ carries the origin marker at coordinate $z$ exactly when $z=0$.

**Proof.** Unfold the definition of the guide tape and consider its successive conditional cases. If an earlier edge-marker condition holds, its symbol differs from the origin marker, so the desired equality cannot hold; the same is true when the coordinate is in the interior interval. In the remaining case, the tape value is the origin marker precisely when the condition $z=0$ holds. The integer inequalities and equalities in these cases ensure that no other branch can produce the origin marker.
