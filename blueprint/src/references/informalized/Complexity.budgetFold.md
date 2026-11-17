<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.budgetFold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Pass as a Left-to-Right Fold

**Claim.** For every incoming carry bit and finite bit word, folding the one-bit borrow rule from left to right returns the same final state and rewritten word as the borrow pass.

**Proof.** Induct on the word, with the incoming carry arbitrary. On the empty word, both procedures return the carry and the empty word. For $b::bs$, the fold applies the one-bit rule to $b$, producing next carry $c\mathbin{\&\&}\neg b$ and output bit $b\mathbin{\mathrm{xor}}c$. It then processes the tail from that next carry. By induction, this tail computation agrees with the borrow pass on $bs$ from the same carry. Both procedures therefore return the same final carry and the same output word.
