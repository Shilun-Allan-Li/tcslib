<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_compare_trace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Word-comparison machine trace

**Claim.** Given the matching-prefix and stopping-index hypotheses, the comparison machine follows the forward trace through time $\delta$, rewinds with the verdict that $u=v$ through time $2\delta+1$, and then remains in the corresponding completed configuration.

**Proof.** Let $F(r)$ and $R(r)$ denote the specified forward and rewind configurations, and let $D$ be the completed configuration with verdict $u=v$. At progress zero, $F(0)=d$. For each $r<\delta$, the two heads in $F(r)$ read the same symbol by the matching-prefix hypothesis. The machine therefore advances both heads and enters $F(r+1)$. At index $\delta$, the hypotheses say the two read values cannot both be symbols, and that the optional values agree exactly when $u=v$. Thus the comparison machine turns into rewind, carrying precisely the verdict that $u=v$, and its leftward moves give $R(\delta)$. At each positive rewind index $r+1$, the first tape head is at offset $r$ and reads the common symbol guaranteed by the prefix hypothesis; the machine moves left on both tapes, giving $R(r)$. At rewind index zero, the first head reads blank at offset $-1$, so the machine moves right into the done state with the same verdict, reaching $D$. The done configuration is fixed by subsequent steps. Applying the general trace theorem (Turing.catalog_trace_run) to these transition identities yields the claimed formula at every time.

**Key facts.** `Turing.catalog_trace_run`.
