<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.haltCoinTest_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-Encoded Coin Test Identity

**Claim.** For any two finite bit strings $x$ and $r$, applying the halting-coin test to their pair encoding gives the same Boolean value as the verifier applied to $x$ and $r$.

**Proof.** Decode the pair encoding: its first and second components are respectively $x$ and $r$ (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). The test's arithmetic is performed using lengths of constructed words. The multiplication routine has output length equal to the product of the two input lengths (`Complexity.BinArith.length_mulU`); the word representing the halting degree has length $\mathrm{hlD}(x)$ (`Randomized.length_hlDWord`), and the word counting the ones in $r$ has length $r.\mathrm{count}(\mathrm{true})$ (`Randomized.length_onesW`). Substituting these lengths into the two length comparisons in the test gives precisely the two inequalities defining the verifier. Thus both Boolean comparisons, and hence their conjunction, have the same value.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.length_mulU`, `Randomized.length_onesW`, `Randomized.length_hlDWord`.
