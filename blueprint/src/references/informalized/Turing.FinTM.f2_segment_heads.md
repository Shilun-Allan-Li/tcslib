<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_segment_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Positions Within Segments

**Claim.** If each of the first $N$ configurations has heads within $[-H,H]$, each segment takes at most $B$ steps to reach the next configuration or halt, and the terminal configuration's heads are within $[-(H+B),H+B]$, then every head in the run from $c_0$ remains within that larger interval at every time.

**Proof.** Induct on the number $N$ of segments, generalizing the configuration sequence. If $N=0$, the starting configuration is already the halted terminal configuration; a halted run remains fixed (Turing.MultiTapeTM.runFrom_of_halt), so its heads satisfy the terminal bound at every time. For the induction step, use the first segment's witness: there is a duration $u≤B$ at which the run from $c_0$ either halts or reaches $c_1$. At any time $v≤u$, the initial heads lie within $[-H,H]$, and the head-displacement bound (Turing.FinTM.f2_head_steps) shows that moving for at most $B$ steps keeps them within $[-(H+B),H+B]$. If the first segment halts, the run is fixed after time $u$, and the same bound at time $u$ covers every later time. If it reaches $c_1$, split any later time as $u$ plus the remaining duration. The run-addition identity (Turing.MultiTapeTM.runFrom_add) identifies this tail with the run from $c_1$. Apply the induction hypothesis to the shifted sequence $c_1,c_2,[0m\ldots,c_N$: its seam bounds, terminal condition, and segment witnesses are inherited from the original hypotheses. This proves the bound for every time and tape.

**Key facts.** `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.FinTM.f2_head_steps`, `Turing.MultiTapeTM.runFrom_add`.
