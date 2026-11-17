<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.setup_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Setup Run

**Claim.** Under the stated oracle condition and length bound, the machine has a finite guarded run from the initial scan configuration to the first radius-copy phase, with all registers zero except that the logarithm register is $1+\mathrm{hv}(|x|)$; memory and head position are unchanged.

**Proof.** The input-length loop (`inputLength_loop`) uses the oracle answers to count the length of $x$ in the length register, leaving the machine at the logarithm setup label. The register bounds needed for this run follow from the zero state and the assumption $|x|+2\le B$. The register-only run is lifted to a memory-machine run by `of_areach`; the memory tape and head are unchanged, and the live endpoint permits this lifting. One deterministic step initializes the logarithm register to $1$. Then `lg_run` performs the halving loop, adding one to that register for each halving until the length register reaches zero; it ends at the first radius-copy phase with logarithm value $1+\mathrm{hv}(|x|)$. The bound $\mathrm{hv}(|x|)\le |x|$ ensures the register bound throughout this final loop. The runs are concatenated, and `reach_cf` identifies the endpoint with the stated register record.

**Key facts.** `Complexity.LogProg.inputLength_loop`, `Complexity.LogProg.ExpBFS.of_areach`, `Complexity.LogProg.ExpBFS.step_of`, `Complexity.LogProg.ExpBFS.lg_run`, `Complexity.LogProg.ExpBFS.reach_cf`, `Complexity.LogProg.MReach.trans`.
