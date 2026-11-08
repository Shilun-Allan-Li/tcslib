<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.length_maskSelect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Masked Selection

**Claim.** For Boolean lists of equal length, selecting the entries of the word whose corresponding mask entries are true produces a list whose length is the number of true entries in the mask.

**Proof.** Induct on the mask, allowing the word to vary. If the mask is empty, the length hypothesis forces the word to be empty, and both lengths are zero. For a nonempty mask, the length hypothesis rules out an empty word, so write the lists as `emit :: mask` and `b :: w`. Their tails have equal length. If `emit` is false, the selected output contributes no entry; if it is true, it contributes exactly one. In either case, the induction hypothesis identifies the length of the selection from the tails with the number of true entries there, and the leading mask bit contributes the same amount to both sides.
