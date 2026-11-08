<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadVec_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vector decoding after encoding

**Claim.** If reading an encoded value followed by any suffix returns that value and suffix, then reading the concatenation of the encodings of a vector’s entries followed by a bit string succeeds and returns the vector and that bit string.

**Proof.** Proceed by induction on the vector length. At length zero, the concatenation of encoded entries is empty, and the vector reader returns the unique function on the empty index type together with the unchanged suffix. For the successor step, the list of indices splits into its first index followed by the indices for the remaining entries. Thus the input begins with the encoding of the first value, followed by the encodings of the remaining entries and the suffix. The assumed reader property decodes that first value and leaves precisely the rest of this list; the induction hypothesis then decodes the remaining vector and preserves the suffix. The reader’s assembled vector agrees with the original one at the first index and at every later index, so the returned vector is the given vector.
