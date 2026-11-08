<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_trace_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Follows a Prescribed Trace

**Claim.** At every time $t$, the run from $F(0)$ is $F(t)$ for $t\le L$, is $R(2L+1-t)$ for $L<t\le 2L+1$, and is $D$ for $t>2L+1$.

**Proof.** Proceed by induction on time. At time zero the run is $F(0)$, as required. For the successor step, the run at time $t+1$ is one machine step from its configuration at time $t$ (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). If $t<L$, the forward-step hypothesis sends $F(t)$ to $F(t+1)$. If $t=L$, the turn hypothesis sends $F(L)$ to $R(L)$, which is the return-trace entry at time $L+1$. If $L<t<2L+1$, write the current return index as $2L+1-t$; it is positive, and the return-step hypothesis sends that configuration to the one with index reduced by one, exactly the index prescribed at time $t+1$. At the boundary $t=2L+1$, the entry hypothesis sends $R(0)$ to $D$. For $t>2L+1$, the induction hypothesis gives $D$, and the fixed-point hypothesis keeps the run at $D$. These cases establish the formula at every time.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
