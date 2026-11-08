<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateAliceCondBits_fiber_eq_iInter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice’s conditioning fiber

**Claim.** The fiber where Alice’s conditioning bit-string equals a target string $b$ is exactly the intersection, over all coordinates, of the fibers where the individual conditioning bit equals the corresponding bit of $b$.

**Proof.** Fix a coordinate assignment. It belongs to the fiber on the left precisely when its conditioning bit-string equals $b$. Equality of two functions is equivalent to equality at every coordinate, so this holds exactly when, for every coordinate $k$, the conditioning bit at $k$ equals $b_k$. Those are precisely the membership conditions defining the intersection on the right.
