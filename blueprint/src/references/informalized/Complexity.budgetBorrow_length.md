<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.budgetBorrow_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Pass Preserves Length

**Claim.** For every incoming borrow bit and every finite bit word, the word produced by the borrow pass has the same length as the input word.

**Proof.** Induct on the word, allowing the incoming carry to be arbitrary. The empty word produces the empty word. For a word $b::bs$, the pass outputs one bit followed by the recursively processed tail. By induction, that tail has the same length as $bs$. Therefore the output length is $1+|bs|=|b::bs|$.
