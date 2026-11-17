<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.sel_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Selector Scan

**Claim.** When the input has at least $\mathrm{nbits}(M)$ symbols, after $\mathrm{nbits}(M)$ steps the tabulating machine is in state $\mathrm{fA}$ with the scanned selector bits, and all other configuration data have the stated initial or blank values.

**Proof.** Positivity of the selector length lets us write $m=\mathrm{nbits}(M)-1$, so $m+1=\mathrm{nbits}(M)$. The selector-phase description (`Complexity.Meyer.sel_run`) gives the configuration after $m$ steps: the machine is at selector coordinate $m$, the first $m$ bits have been recorded, the input head is at the corresponding position, and the auxiliary tapes and output are still blank. One more step reads the input symbol at position $m+1$, which is $y_m$ because $m<|y|$. The selector transition has reached its final coordinate, so it changes to state $\mathrm{fA}$ and updates that last selector bit. The successive-prefix identity (`Complexity.Meyer.selPart_succ`) identifies the updated bits with the full selector prefix. The transition advances the input head once; its tapes are idle, so they remain blank with heads at zero, and it emits no output. This gives the claimed configuration.

**Key facts.** `Complexity.Meyer.nbitsOf_pos`, `Complexity.Meyer.sel_run`, `Complexity.Meyer.acfg_step`, `Complexity.Meyer.inputSymbol_fpos`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.moveInputPos_fpos`, `Complexity.Meyer.idle_apply`, `Complexity.Meyer.wr_none`, `Complexity.Meyer.selPart_succ`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
