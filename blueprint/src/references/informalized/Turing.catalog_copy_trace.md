<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_copy_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying machine trace

**Claim.** If the source tape contains $w$ around its head as specified, the copying machine follows its forward trace through time $|w|$, rewinds through time $2|w|+1$, and then remains in the completed configuration, whose destination tape contains the copied word.

**Proof.** Write $L=|w|$, and denote the prescribed forward configurations by $F(r)$, rewind configurations by $R(r)$, and the completed configuration by $D$. The initial forward configuration $F(0)$ is the given configuration: the copied prefix has length zero, and the state is the sweep state. For each $r<L$, the forward-step result (Turing.catalog_copy_forward) gives one transition from $F(r)$ to $F(r+1)$. At $F(L)$ the source head reads blank, so the machine turns around and moves both heads left, reaching $R(L)$. At each positive rewind index $r+1$, the source head reads $w[r]$, so the machine continues left to $R(r)$. At rewind index zero the source head reads blank, causing the machine to move right into the done phase and reach $D$. The done phase fixes its configuration, including the destination tape already specified by $F(L)$. These initial, forward, turning, rewind, entry, and fixed-point identities are the hypotheses of the piecewise trace theorem (Turing.catalog_trace_run), which proves the assertion for every time.

**Key facts.** `Turing.catalog_copy_forward`, `Turing.catalog_trace_run`.
