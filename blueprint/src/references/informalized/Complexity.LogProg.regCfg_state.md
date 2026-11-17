<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.regCfg_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State of a register configuration

**Claim.** The configuration obtained by replacing register $r$’s tape by $f$, placing its head at $p$, and setting the state to $s$ has state $s$.

**Proof.** The state component of the constructed configuration is set to $s$ (stored as an active state), so its state is exactly $\mathrm{some}\,s$.
