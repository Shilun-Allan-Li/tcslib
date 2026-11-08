<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPoly_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setup phase initializes the loop

**Claim.** Starting in setup with all work heads at $j-1$, after $j+1$ steps the machine is in $\mathrm{loop}(c)$ with all work heads at zero and empty output.

**Proof.** Induct on $j$. At $j=0$, the heads are at $-1$, so tape 0 is blank; the setup transition moves every head one cell right and enters $\mathrm{loop}(c)$, leaving all heads at zero. For the successor case, the heads start at $j$. When $j<q$, each head reads a true cell because the tape contents are true on positions from zero through $q-1$. The setup transition moves every head one cell left and stays in setup, placing them at $j-1$; the induction hypothesis finishes the run. The iteration step identity `runFrom_succ_eq_step` and the zero-step identity `runFrom_zero` connect these transition calculations with the stated run lengths.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
