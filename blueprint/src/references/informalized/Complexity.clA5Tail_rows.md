<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Tail_rows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Header Tails Remove Packed Rows

**Claim.** For $l,n\in\mathbb{N}$, a row assignment of finite binary words, and a finite binary word $tail$, applying $nl$ iterated header tails to the first $n$ packed rows followed by $tail$ yields exactly $tail$.

**Proof.** Induct on the number $n$ of rows, keeping $tail$ arbitrary. With zero rows, there are no packed fields to remove, so zero header tails leave $tail$ unchanged. For the successor step, the packed rows consist of the first $n$ rows followed by the fields of row $n$. The identity $(n+1)l=l+nl$ and the composition law for header tails (`clA5Tail_add`) first remove the $nl$ fields from the earlier rows, by induction, then remove the fields of the final row. Those fields form the list of words indexed by the $l$ positions; the fields lemma (`clA5Tail_fields`) removes them and leaves $tail$.

**Key facts.** `Complexity.clA5Tail_add`, `Complexity.clA5Tail_fields`.
