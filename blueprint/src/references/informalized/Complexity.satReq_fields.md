<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satReq_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of Request Fields

**Claim.** For every Boolean word $x$ and streaming seam state $s$ with fresh cursor $f$, consumed length $c$, and phase $q$, form the round request by pairing the encoded seam word of $s$ with $x$. Its fresh, consumed, and phase fields are respectively $1^f$, $1^c$, and $1^q$, and its unread input is $x$ with its first $c$ bits dropped.

**Proof.** The round request is the pair encoding of the encoded seam word and $x$. The pair-decoding theorem (`Turing.pairDecode_pairEncode`) says that decoding any pair encoding recovers its two components exactly. Apply it first to the outer pair to recover the seam word and the input. Applying it again to the nested pair encodings in the seam word recovers the fresh, consumed, and phase unary fields. Thus the request-field extractors return $1^f$, $1^c$, and $1^q$; the remainder extractor drops the consumed field's length, namely $c$, from $x$, as claimed.

**Key facts.** `Turing.pairDecode_pairEncode`.
