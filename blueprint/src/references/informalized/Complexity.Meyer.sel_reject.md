<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.sel_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection on a Short Selector String

**Claim.** If the input length is less than the number of selector symbols, then after $|y|+1$ steps the tabulated machine is halted and its output is the single bit $0$.

**Proof.** The selector-phase description (`Complexity.Meyer.sel_run`) applies at $m=|y|$, since this is strictly below the selector length. Thus after $|y|$ steps the machine is still in a selector state, with its input head at the position just beyond the input and its auxiliary tapes blank. The next input symbol is therefore blank (`Complexity.Meyer.inputSymbol_fpos`). In a selector state, a blank input invokes the reject transition, which halts and emits false. The configuration update for this idle-tape transition (`Complexity.Meyer.tact_idle_apply`) leaves the auxiliary tapes unchanged and appends that one false bit to the empty output. Hence the state is absent and the output is $[\mathrm{false}]$.

**Key facts.** `Complexity.Meyer.sel_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.Meyer.acfg_step`, `Complexity.Meyer.inputSymbol_fpos`, `Complexity.Meyer.tact_idle_apply`.
