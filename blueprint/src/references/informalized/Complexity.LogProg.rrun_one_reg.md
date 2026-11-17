<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.rrun_one_reg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Ordinary Transition from a Register Configuration

**Claim.** If there is no oracle call at $s$, then one step of the run from the configuration with state $s$, register $r$'s tape replaced by $f$, and its head at $p$ equals applying the machine transition prescribed for state $s$ and the scanned symbols.

**Proof.** The modified configuration has state $s$ (\texttt{Complexity.LogProg.regCfg_state}). A run of length one is the one-step transition (\texttt{Complexity.LogProg.rrun_one}); since there is no oracle call at $s$, this transition is the underlying machine step (\texttt{Complexity.LogProg.rstep_noncall}). Unfolding that machine step at state $s$ gives the prescribed transition applied to the modified configuration, with its input and work-tape symbols read there.

**Key facts.** `Complexity.LogProg.regCfg_state`, `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`.
