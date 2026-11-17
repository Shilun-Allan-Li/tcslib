<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPoly_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial copy and setup phases

**Claim.** From the initial configuration on $x$, after $2(|x|+1)$ steps the machine is in $\mathrm{loop}(c)$ with all work heads at zero, each tape containing true exactly at positions $0$ through $|x|$, input-head position $|x|+1$, and empty output.

**Proof.** First use the copy-phase invariant (`f2_catalogPoly_copy`) at time $|x|$. The input head is then at the right end of the input, where the input symbol is blank. The copy transition writes true at the current cell on every tape, moves each work head one cell left, leaves the input head at the right-end position, and enters setup. The tape update extends the filled interval through position $|x|$ by `f2_catalogPolyTape_write`; the neutral input-head move is `moveInputPos_zero`. This gives the setup configuration with every work head at $|x|-1$. The time decomposition `runFrom_succ_eq_step'` and `runFrom_add` now combine the first $|x|+1$ steps with the setup phase. Applying `f2_catalogPoly_setup` for $j=|x|+1$ resets all heads to zero and enters $\mathrm{loop}(c)$; the two phase lengths sum to $2(|x|+1)$.

**Key facts.** `Turing.FinTM.f2_catalogPolyTape_write`, `Turing.FinTM.f2_catalogPoly_copy`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_catalogPoly_setup`.
