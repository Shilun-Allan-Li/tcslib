<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.guideTape_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Edge Marker Location

**Claim.** For every natural number $R$ and integer $z$, the guide tape of radius $R$ carries the right edge marker at coordinate $z$ exactly when $z=R+1$.

**Proof.** Unfold the guide tape definition and inspect its conditional cases. The left-edge condition produces the left edge marker, while the origin and interior conditions produce different symbols; none can equal the right edge marker. Thus the only possible branch is the right-edge branch, whose condition is exactly $z=R+1$. Conversely, when this equality holds, the corresponding branch supplies the right edge marker; the integer inequalities rule out any conflicting earlier branch.
