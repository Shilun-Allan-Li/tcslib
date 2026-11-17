<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoad_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Row Load

**Claim.** The row loader reaches a configuration with all fields equal to their new words, the field index at $l$, and the stream cursor immediately after the packed new fields, within the stated time bound.

**Proof.** First, every coordinate of the mixed bank `clLoadWords old new l` is new: for each $i<l$, the condition $i<l$ selects `new i`. Apply the prefix-loading result (`Complexity.clLoad_prefix`) with $j=l$. It supplies a time at most $l(2U+3W+7)$ at which the loader has field index $l$, the bank `clLoadWords old new l`, and a stream cursor after the packed encoding of the first $l$ new words. Since `List.ofFn new` has length $l$, those first $l$ words are the whole list. Replacing the mixed bank by `new` and the encoded prefix by the full packed list yields precisely the claimed configuration and time bound.

**Key facts.** `Complexity.clLoad_prefix`.
