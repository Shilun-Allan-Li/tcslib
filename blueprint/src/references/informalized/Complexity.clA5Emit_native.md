<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Emit_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Chunk Emission

**Claim.** For every finite Boolean Turing machine $M$ and every binary code for its state alphabet, the function sending a body word to the chunk emitted at that word is polynomial-time computable.

**Proof.** The emitted chunk is formed by a case distinction on whether the cursor is at most the stored round. The cursor and stored round have polynomial-time unary encodings, so their comparison is polynomial-time computable (`clA5Le_native`). If the comparison succeeds, append the fragment emitted at the current word to a final delimiter exactly when the cursor equals the stored round. That equality test is polynomial-time computable from the unary cursor and round (`clA5Eq_native`, using `clA5Cursor_native` and `clA5StoredRound_native`). The fragment itself is polynomial-time computable (`clA5Fragment_native`), and appending polynomial-time outputs preserves polynomial-time computability (`clNative_append`). The delimiter and empty word are constant outputs (`clA5_pt_const`). Thus both branches and the conditional choice between them are polynomial-time computable (`clA5_pt_cond`), giving the claimed result.

**Key facts.** `Complexity.clA5Cursor_native`, `Complexity.clA5StoredRound_native`, `Complexity.clA5Eq_native`, `Complexity.clA5_pt_const`, `Complexity.clA5_pt_cond`, `Complexity.clA5Le_native`, `Complexity.clA5Fragment_native`, `Complexity.clNative_append`.
