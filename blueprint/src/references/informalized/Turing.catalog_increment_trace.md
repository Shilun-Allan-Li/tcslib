<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_increment_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment machine trace

**Claim.** For a word consisting of $p$ true bits, optionally followed by a false separator and a remaining word, the increment machine follows the specified forward, rewind, and completed trace; its rewind and completed phases carry the verdict recording whether the remaining word is present.

**Proof.** Let $F(r)$ and $R(r)$ be the prescribed forward and rewind configurations, with $0\le r\le p$, and let $D$ be the prescribed completed configuration. The given decomposition and tape hypothesis show that $F(0)$ is the initial configuration. For each $r<p$, the head reads a true bit: the machine changes it to false, moves right, and remains in the run phase. The tape update extends the false prefix by one cell while leaving the remaining true suffix and optional separator in place; the identity expressing this replacement is (Turing.catalog_write_middle). Thus the next configuration is $F(r+1)$. At progress $p$, there are two cases. If the optional tail is absent, the head reads blank, and the machine turns into rewind carrying the false verdict. If it is present, the head reads the separator, changes it to true, moves left, and enters rewind carrying the true verdict; the same write identity accounts for the updated tape. During rewind, at each positive index $r+1$, the head reads a false bit and moves left, giving $R(r)$. At index zero it reads blank, moves right, and enters the done phase with the same verdict, giving $D$. The done state is fixed. Applying the piecewise trace theorem (Turing.catalog_trace_run) to these transitions gives the claim at every time.

**Key facts.** `Turing.catalog_write_middle`, `Turing.catalog_trace_run`.
