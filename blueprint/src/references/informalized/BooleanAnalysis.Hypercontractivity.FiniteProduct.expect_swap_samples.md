<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_swap_samples -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exchange of Product Samples

**Claim.** For any function $F$ of two product outcomes, exchanging the two samples coordinatewise across $S$ and its complement preserves its iterated product expectation.

**Proof.** Define a map on pairs of outcomes that swaps the samples on coordinates outside $S$ and keeps their order on coordinates in $S$. Applying this map twice returns the original pair, so it is a bijection. At each coordinate, the two weights are merely exchanged or left in place; hence the product of the two outcome masses is unchanged. The iterated expectation is a finite sum over pairs, so reindexing that sum by this mass-preserving bijection leaves it unchanged, giving the identity.
