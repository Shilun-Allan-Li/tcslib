<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.budgetBorrow_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Subtracts One from Positive Values

**Claim.** For every finite bit word $bs$ with positive little-endian value, the value of the word produced by a borrow pass started with borrow bit $1$, plus $1$, equals the value of $bs$.

**Proof.** Induct on the word. The empty word cannot satisfy the positive-value hypothesis. If the word is $0::bs$, its value is twice the tail value, so positivity implies that the tail value is positive. Apply induction to the tail: its borrowed output has value one less than the tail value. The leading zero propagates the borrow, so the full output value is twice that tail output value plus one. Adding one gives twice the tail value, which is exactly the input value. If the word is $1::bs$, the next carry is false. A pass with false carry leaves the tail unchanged and returns false (\texttt{Complexity.budgetBorrow\_false}). The resulting word has value twice the tail value plus one, the same as the input value, and the claimed equation follows.

**Key facts.** `Complexity.budgetBorrow_false`.
