<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Tail_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Header Tails Remove Packed Fields

**Claim.** For a finite list $ws$ of finite binary words and a finite binary word $tail$, applying $|ws|$ iterated header tails to the packed encoding of $ws$ followed by $tail$ yields exactly $tail$.

**Proof.** Induct on the list $ws$. For the empty list, its packed encoding and its length are both empty or zero, so the result is $tail$. For a nonempty list $w::ws$, the packed encoding consists of the pair encoding of $w$ with the remaining packed fields and $tail$. One header tail removes the header $w$ and returns the remainder, by the decoding law for a pair encoding (`pairDecode_pairEncode`) and the compatibility of pair encoding with appended tails (`clPair_append`). The composition law for iterated header tails (`clA5Tail_add`) lets us separate this first removal from the subsequent $|ws|$ removals. The induction hypothesis then removes the packed fields from $ws$, leaving $tail$.

**Key facts.** `Complexity.clA5Tail_add`, `Complexity.clPair_append`, `Turing.pairDecode_pairEncode`.
