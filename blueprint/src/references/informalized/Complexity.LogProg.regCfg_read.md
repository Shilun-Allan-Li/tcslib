<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.regCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a replaced register

**Claim.** In the configuration obtained from $c$ by setting the state to $s$, replacing register $r$’s tape by $f$, and placing its head at $p$, the symbol scanned by register $r$ is $f(p)$.

**Proof.** The scanned symbol is the tape content at the register’s head position. The update assigns tape $f$ to register $r$ and assigns head position $p$ there, so the scanned symbol is $f(p)$.
