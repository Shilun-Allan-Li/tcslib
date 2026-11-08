<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.pairFanin_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair fanin recursion

**Claim.** For every natural number $n$, pair fanin of a list whose first pair is $p$ is the maximum of the maximum fanin of the two circuits in $p$ and the pair fanin of the remaining list.

**Proof.** By definition, pair fanin is a right fold over the list, starting at $0$, whose step takes the maximum of the two circuits' fanins and the accumulated value. Evaluating this fold on a list with head $p$ gives exactly the stated maximum.
