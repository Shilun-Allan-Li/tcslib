<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Next_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Cursor Update

**Claim.** For every finite Turing machine $M$, the cursor-update function defined using $M$ is polynomial-time computable.

**Proof.** First extract the header field $u$; this is polynomial-time computable (`clHeaderField_native`). The stored round bound is polynomial-time computable in unary (`clA5StoredRound_native`). Compose the unary filler that produces a word of true bits of length $|u|$ with the field extractor to obtain the unary encoding of $|u|$ (`clNative_fill` and `PolyTimeComputable.comp`). Comparing these unary lengths computes the bit recording whether $|u|$ is at most the stored round bound (`clA5Le_native`). Use that bit to choose between appending one true bit to $u$ and leaving $u$ unchanged; both branches are polynomial-time computable, by closure under append and constant functions, and conditional selection preserves polynomial-time computability (`clNative_append`, `clA5_pt_const`, `clA5_pt_cond`). Finally pair-encode the updated field together with the unchanged header tail. Pair encoding preserves polynomial-time computability (`clNative_pair`), yielding exactly the cursor update.

**Key facts.** `Complexity.clHeaderField_native`, `Complexity.clA5StoredRound_native`, `Complexity.clNative_fill`, `Complexity.PolyTimeComputable.comp`, `Complexity.clA5Le_native`, `Complexity.clNative_append`, `Complexity.clA5_pt_const`, `Complexity.clA5_pt_cond`, `Complexity.clHeaderTail_native`, `Complexity.clNative_pair`.
