<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPath.lean :: Complexity.dblAt_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of the Doubled Encoding

**Claim.** If two words both have doubled encodings beginning at the same position in $x$, each followed by the delimiter $01$, then the two words are equal.

**Proof.** Proceed by cases on whether each word is empty. If both are empty, they are equal. If one is empty and the other begins with a bit, decompose the nonempty word using the initial-bit decomposition lemma (`dblAt_cons`). The two delimiter bits for the empty encoding must then equal the two initial repeated bits of the nonempty encoding. Its first repeated bit is therefore false, while the next one must be both the empty encoding’s true delimiter bit and the nonempty encoding’s repeated bit, a contradiction. If both words are nonempty, decompose each encoding at its first bit (`dblAt_cons`). The first-position conditions show their initial bits agree. Their remaining words are both doubled encodings starting at position $q+2$, so induction gives equality of the tails. Equal heads and equal tails give equality of the words.

**Key facts.** `Complexity.dblAt_cons`.
