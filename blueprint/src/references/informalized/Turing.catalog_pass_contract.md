<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_pass_contract -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Pass Contract

**Claim.** After $L+1$ steps from $F(0)$ the machine is at $D$; predicate $P$ holds at every time $t<L+1$, and $Q$ holds at every time $t\le L+1$.

**Proof.** The run is first identified at every time $t$ with the configuration that equals $F(t)$ when $t\le L$ and $D$ otherwise. This follows by applying the prescribed-trace theorem (`Turing.catalog_trace_run`) with a constant return sequence equal to $D$: the exit step enters that sequence, and every subsequent step remains at $D$. At time $L+1$, the run is therefore $D$. For $t<L+1$, we have $t\le L$, so the run is $F(t)$ and the hypothesis on $P$ gives the claim. For $t\le L+1$, if $t\le L$ the run is $F(t)$ and the hypothesis on $Q$ applies; otherwise it is $D$, where $Q$ holds by assumption.

**Key facts.** `Turing.catalog_trace_run`.
