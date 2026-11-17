<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitStep_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Producer-Step State Update

**Claim.** Applying the producer step to the retained encoding of $x$, time $t$, and stored rows $r$ yields the retained encoding of $x$, time $t+1$, and $r$ followed by the visit row for $M,C,e,x$ at time $t$.

**Proof.** Decode the nested pair encoding of the retained state, time, and rows. The pair-encoding inverse law says that decoding a pair encoding recovers its two original words (`Turing.pairDecode_pairEncode`). Thus the producer step reads back the header fields $x$ and the time word, and its tail operation recovers the stored rows. Appending one true bit changes the time word from the encoding of $t$ to that of $t+1$; the replicate-list identities identify this extended word with the encoding of the successor time. The step appends the visit row computed from the original pair encoding of $x$ and time $t$. Reassembling the nested pair encodings gives exactly the stated retained state and updated rows.

**Key facts.** `Turing.pairDecode_pairEncode`.
