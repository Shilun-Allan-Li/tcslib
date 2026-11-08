<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecCnfCost_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of Concatenated CNFs

**Claim.** For any two CNFs over the same variable type, the cost of their concatenation is the sum of their costs.

**Proof.** The cost is obtained by mapping each clause to its length plus one and summing over the resulting list. Mapping over concatenated lists concatenates the two mapped lists, and the sum over a concatenation is the sum of the two sums. Therefore the concatenated CNF has cost equal to the sum of the individual costs.
