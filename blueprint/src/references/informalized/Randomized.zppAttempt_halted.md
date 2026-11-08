<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.zppAttempt_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting of the Selected Branch

**Claim.** For a machine family $N$, input $x$, bit $b$, and choice word $u$, the randomized branch machine halts on choice word $b::u$ exactly when $N(b)$ halts on choice word $u$.

**Proof.** The branch-run identity (`Turing.FinNDTM.coinBranch_runWith`) says that the first choice selects one of the two branch configurations: the false branch when $b$ is false and the true branch when $b$ is true. Consider these two cases. In either case, the selected configuration is the run of the corresponding machine after the remaining choices $u$, with its output mapping applied. The initialization and run identities for output-mapped machines (`Turing.NDTM.mapOutput_initCfg` and `Turing.NDTM.mapOutput_runWith`) identify this with the mapped configuration obtained from the original run of $N(b)$. Output mapping changes only the output tape, not the state, so this configuration has state none exactly when the original run of $N(b)$ has state none.

**Key facts.** `Turing.FinNDTM.coinBranch_runWith`, `Turing.NDTM.mapOutput_initCfg`, `Turing.NDTM.mapOutput_runWith`.
