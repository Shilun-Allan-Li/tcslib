<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_incFixed_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Increment in Constant Space

**Claim.** A finite Turing machine computes fixed-width binary increment, using the empty word on overflow, in linear time and with a constant bound on work-tape cells at every time.

**Proof.** Choose `f2_incFixedTM` and $c=3$. Its computation theorem `f2_incFixed_computes` gives the required output and halting time $3(|x|+1)$ on each input. This machine has zero work tapes. The zero-tape space theorem `spaceUsed_zero_tapes_eq_zero` therefore says that its space usage is $0$ at every time, which is at most $3$.

**Key facts.** `Turing.FinTM.f2_incFixed_computes`, `Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`.
