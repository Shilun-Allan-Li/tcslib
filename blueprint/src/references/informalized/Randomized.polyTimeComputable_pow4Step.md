<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.polyTimeComputable_pow4Step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Fourth-Power String Map

**Claim.** The function that pairs the decoded first component with four copies of the decoded second component when that repeated word has length at most the first component's length, and otherwise with the original second component, is polynomial-time computable.

**Proof.** Both decoded components are polynomial-time computable. Repeatedly concatenate the second component with itself to obtain four copies; closure under concatenation shows this function is polynomial-time computable. Pair the first component with that repeated word and apply the polynomial-time length comparison, which decides whether the repeated word fits within the first component. The conditional closure theorem then gives polynomial-time computability of the selected second component: the fourfold word when the test succeeds, and the original decoded second component otherwise. Pairing this selection with the decoded first component completes the construction.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.append`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_lenLe`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_ite`.
