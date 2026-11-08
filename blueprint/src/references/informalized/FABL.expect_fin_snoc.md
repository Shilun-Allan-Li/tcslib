<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.expect_fin_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average by the Last Coordinate

**Claim.** For a finite nonempty set $\Omega$, the uniform average of a function on $\Omega^{m+1}$ equals the average over the first $m$ entries of its average over the last entry.

**Proof.** Reparametrize each $(m+1)$-tuple uniquely as a pair consisting of its first $m$ entries and its last entry. This bijection preserves uniform averages. The average over the resulting product of finite sets is the iterated average over the first block and the last coordinate, by the product rule for uniform finite averages. This is exactly the asserted identity.
