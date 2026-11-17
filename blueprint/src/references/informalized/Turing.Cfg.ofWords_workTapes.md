<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Convention.lean :: Turing.Cfg.ofWords_workTapes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Contents of a Word Configuration

**Claim.** For each tape index $i$, the work-tape content function in the configuration determined by $q$ and $w$ is the buffer tape storing $w_i$.

**Proof.** By definition, the configuration determined by $q$ and $w$ has work-tape function sending each index $i$ to the buffer tape of $w_i$. Evaluating that function at the chosen index gives the stated equality.
