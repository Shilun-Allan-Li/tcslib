<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satDrop_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Counter Extension

**Claim.** Applying the action that moves both heads right, writes true, emits nothing, and enters state $0$ to the stated canonical configuration produces state $0$ at offset $i+1$, with a unary counter of length $n+1$ headed at $n+1$ and empty output.

**Proof.** The clamped-position successor law moves the input head from offset $i$ to $i+1$ (`satStreamPos_succ`). On the counter tape, writing true at the current head position $n$ extends the unary block from length $n$ to length $\max(n,n+1)=n+1$; this is the unary-counter write law (`satRedCounter_write`). The action moves the counter head from $n$ to $n+1$, sets the state to $0$, and emits no output. These componentwise facts give the claimed canonical configuration.

**Key facts.** `Complexity.satStreamPos_succ`, `Complexity.satRedCounter_write`.
