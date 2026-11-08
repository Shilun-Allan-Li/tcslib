<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.rrun_one_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Ordinary Transition from an Encoded Configuration

**Claim.** If there is no oracle call at $s$, then one step of the run from the configuration with state $s$ and both specified register heads at $k$ equals applying the machine transition prescribed for state $s$, the scanned input symbol, and the scanned work-tape symbols.

**Proof.** The configuration $\mathrm{eqCfg}(c,s,r_1,r_2,k)$ has state $s$. A run of length one is one application of the program's step, and the no-call hypothesis makes that step the underlying machine step (\texttt{Complexity.LogProg.rstep_noncall}), using the state's equality to identify the active state. Unfolding the machine step at state $s$ yields precisely the transition prescribed by $P$ for the scanned symbols, applied to this configuration.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`.
