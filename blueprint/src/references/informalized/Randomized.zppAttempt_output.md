<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.zppAttempt_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of a Randomized Attempt

**Claim.** The output of the randomized attempt on input $x$ with choice word $b::u$ is the output of $N(b)$ on $x$ with choice word $u$, after filtering its symbols by `keepAs b`.

**Proof.** By the branch-run identity (`Turing.FinNDTM.coinBranch_runWith`), the first choice selects the branch for $N(b)$, leaving the run with choice word $u$. In the false and true cases separately, the selected branch uses the corresponding output-mapped machine. The initialization and run identities for output-mapped machines (`Turing.NDTM.mapOutput_initCfg` and `Turing.NDTM.mapOutput_runWith`) identify this run with the original run of $N(b)$ after mapping each step's output through `keepAs b`. By definition, that map retains a true output symbol and replaces it with $b$, while discarding a false output symbol. Therefore the accumulated output is the original output filtered through `keepAs b`, as claimed.

**Key facts.** `Turing.FinNDTM.coinBranch_runWith`, `Turing.NDTM.mapOutput_initCfg`, `Turing.NDTM.mapOutput_runWith`.
