<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.haltRun_flipOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output flipping preserves halting

**Claim.** Flipping the machine's output changes its halting-run result by negating every output bit, while a nonhalting result remains absent.

**Proof.** First, the flipped machine reaches the same state as the original machine after the same choices. Indeed, its initial configuration is obtained by flipping the original initial configuration, and the run correspondence says that running the flipped machine from this configuration gives the flipped original run; flipping a configuration leaves its state unchanged. The output correspondence says that the flipped run's output is the original output with each bit negated. In the definition of the halting-run result, the state test is therefore the same for both machines. If the run is halted, the two outputs are related by the stated bitwise negation; if it is not halted, both results are absent. These are exactly the two cases of mapping the original option by the list-negation function.

**Key facts.** `Turing.NDTM.flipOutput_initCfg`, `Turing.NDTM.flipOutput_runWith`, `Turing.FinNDTM.flipOutput_outputWith`.
