<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.budgetBorrow_underflow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Underflow Occurs Exactly at Zero

**Claim.** For every finite bit word $bs$, the borrow pass started with borrow bit $1$ ends with borrow bit $1$ exactly when the little-endian value of $bs$ is zero.

**Proof.** Induct on the word. For the empty word, the pass retains the incoming borrow, and the word has value zero, so both sides hold. For a word $b::bs$, split on its first bit. If $b=0$, the recursive pass is still entered with borrow $1$; the output borrow is therefore governed by the induction hypothesis on the tail. The value of the word is twice the tail value, so it is zero exactly when the tail value is zero. If $b=1$, the next carry is false, and a pass started with false carry returns false and leaves the tail unchanged (\texttt{Complexity.budgetBorrow\_false}). Thus the final borrow is false; meanwhile the word value is twice the tail value plus one and cannot be zero. These two cases establish the equivalence.

**Key facts.** `Complexity.budgetBorrow_false`.
