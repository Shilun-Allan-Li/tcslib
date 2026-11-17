<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_clear_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing machine trace

**Claim.** Under the stated tape-content hypothesis, the clearing machine follows the forward sweep through time $|w|$, rewinds through time $2|w|+1$, and then remains in its completed configuration, with the indicated interval blanked.

**Proof.** Set $L=|w|$, and let $F(r)$, $R(r)$, and $D$ be the forward, rewind, and completed configurations in the claim. At progress zero, $F(0)=d$: the state agrees by hypothesis, head positions are unchanged, and the tape modification is restricted to an interval of length zero. For each $r<L$, the head in $F(r)$ is at offset $r$ in the word, so the tape hypothesis says it reads $w[r]$. The clearing machine therefore advances one cell in the sweep state, giving $F(r+1)$. At $r=L$, the head reads blank, so it moves left into the rewind phase, giving $R(L)$. During rewind, at each positive index $r+1$, the head is at offset $r$ and reads $w[r]$; the machine moves left, producing $R(r)$. At rewind index zero, the head is at offset $-1$, which is blank by hypothesis, so the machine moves right into the done phase and reaches $D$. In the done phase the machine leaves the configuration fixed. These transition identities are exactly the hypotheses of the general piecewise-run theorem (Turing.catalog_trace_run), which gives the asserted trace for every time.

**Key facts.** `Turing.catalog_trace_run`.
