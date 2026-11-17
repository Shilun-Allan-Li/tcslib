<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.sel_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selector Phase of the Tabulation

**Claim.** For each $m$ below the selector length and no larger than the input length, after $m$ steps the tabulated machine is in selector state $m$, with precisely the first $m$ input bits recorded; its head and all tapes have the stated positions and contents.

**Proof.** Proceed by induction on $m$. At $m=0$, the run is the initial configuration: the machine is in selector state zero, the selector bits are all false, the input head is at its initial position, the tapes are blank at the origin, and the output is empty (`Complexity.Meyer.init_eq`, together with the zero-step run identity). For the successor step, assume the description at $m$. Since $m<|y|$, the input symbol at the current head position is $y_m$ (`Complexity.Meyer.inputSymbol_fpos`). The selector transition records this bit at coordinate $m$, advances to coordinate $m+1$ (with the bound $m+1<\mathrm{nbits}(M)$), and moves the input head forward. The update identity for successive selector prefixes (`Complexity.Meyer.selPart_succ`) identifies the new bit vector with the first $m+1$ input bits and false values thereafter. The transition leaves work tapes idle, emits nothing, and does not move the auxiliary heads, so their blank contents, origin positions, and empty output persist (`Complexity.Meyer.tact_idle_apply`). This proves the induction step.

**Key facts.** `Complexity.Meyer.init_eq`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.Meyer.sel_run`, `Complexity.Meyer.acfg_step`, `Complexity.Meyer.inputSymbol_fpos`, `Complexity.Meyer.selPart_succ`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.moveInputPos_fpos`.
