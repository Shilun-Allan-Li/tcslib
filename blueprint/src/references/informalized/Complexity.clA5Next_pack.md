<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Next_pack -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cursor Update on Packed Words

**Claim.** For a cursor $i$ no larger than one more than the last round, the cursor update of the packed encoding preserves its data and replaces its unary cursor by $\min(i+1,R+1)$, where $R$ is the last round.

**Proof.** The exactness lemma for packed records identifies the instance stored in the packed word as $x$ and its stored round bound as $R$ (`clA5Stored_exact`). Unpacking the outer pair encoding then shows that the update compares the cursor length $i$ with $R$ and leaves the packed data unchanged. If $i\le R$, the update appends one true bit to the unary cursor; since $i\le R$, this new length is $i+1=\min(i+1,R+1)$. If $i\not\le R$, the hypothesis $i\le R+1$ forces $i=R+1$. The update therefore leaves the cursor at $R+1$, which is also $\min(i+1,R+1)$. Re-encoding the cursor and unchanged data gives the asserted packed word. The decoding identity for pair encodings justifies unpacking the encoded fields (`pairDecode_pairEncode`).

**Key facts.** `Complexity.clA5Stored_exact`, `Turing.pairDecode_pairEncode`.
