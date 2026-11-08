<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.ret_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting return step

**Claim.** From either return state, one step halts, outputs the one-symbol word $[b]$, and leaves the work-tape head at $0$.

**Proof.** A single run step is the machine's transition step (`rrun_one`), and because the program has no call at any state, this is an ordinary machine step (`rstep_noncall`). If $b$ is true, the transition from yes is the return action outputting true; if $b$ is false, the transition from no outputs false. In either case the action has no work-tape write or movement, sets the successor state to none, and appends the output symbol to the initially empty output. Thus the resulting state is halting, the output is $[b]$, and the work-tape head remains at $0$.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`.
