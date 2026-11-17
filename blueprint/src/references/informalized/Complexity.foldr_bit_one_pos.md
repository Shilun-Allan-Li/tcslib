<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.foldr_bit_one_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of a Boolean bit fold

**Claim.** For every finite Boolean list, folding the natural-number bit operation from right to left with initial value $1$ gives a positive natural number.

**Proof.** Induct on the list. The empty list folds to $1$, which is positive. For a head bit $b$ and a tail whose fold is positive by induction, the whole fold is the bit operation applied to $b$ and that positive tail value. If $b$ is false, this operation returns the positive value; if $b$ is true, it returns an odd number at least as large as that value. In either case the result remains positive.
