<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.rrun_one_x -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Ordinary Transition from an Input Configuration

**Claim.** If there is no oracle call at $s$, then one step of the run from the configuration with state $s$, input-head position $ip$, and register $r$'s head at $p$ equals applying the machine transition prescribed for state $s$, the input symbol at $ip$, and the scanned work-tape symbols.

**Proof.** The run of length one is the one-step transition (\texttt{Complexity.LogProg.rrun_one}). Because the configuration has state $s$ and there is no oracle call there, its one-step transition is the underlying machine step (\texttt{Complexity.LogProg.rstep_noncall}). The input symbol of this modified configuration is the symbol specified by $\mathrm{inSym}(x,ip)$ (\texttt{Complexity.LogProg.xCfg_inSym}). Unfolding the machine step at state $s$ now gives the claimed application of the prescribed transition to the scanned symbols.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`, `Complexity.LogProg.xCfg_inSym`.
