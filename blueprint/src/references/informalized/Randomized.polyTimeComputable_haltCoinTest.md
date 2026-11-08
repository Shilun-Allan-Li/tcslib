<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.polyTimeComputable_haltCoinTest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Halt-Coin Test

**Claim.** The function sending each bit string $z$ to the singleton list containing the halt-coin test result is polynomial-time computable.

**Proof.** For the first length comparison, the constructions $hcLin(12,z)$ and $hcCD3(z)$ are polynomial-time computable, as is pairing their outputs. The test that checks whether the second component's length is at most the first component's length is polynomial-time computable, so composing it with this pair gives the first comparison. The same reasoning, using $hcCD(z)$ and $hcLin(4,z)$, gives the second comparison. Negating each comparison and conjoining the results preserves polynomial-time computability. This produces exactly the two strict/non-strict length conditions in the halt-coin test.

**Key facts.** `Randomized.polyTimeComputable_hcLin`, `Randomized.polyTimeComputable_hcCD3`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_lenLe`, `Complexity.BinArith.polyTimeComputable_test_app`, `Randomized.polyTimeComputable_hcCD`, `Complexity.polyTimeComputable_and`, `Complexity.polyTimeComputable_not`.
