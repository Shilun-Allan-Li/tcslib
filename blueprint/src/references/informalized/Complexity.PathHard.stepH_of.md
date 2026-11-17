<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.stepH_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Removing an Initial Halting Step

**Claim.** If the configuration obtained after one step from instruction $l$ and state $st$ has a finite guarded run halting with answer $r$, then the run can be extended backward to start from instruction $l$ and state $st$, with the same answer.

**Proof.** The register bounds on $st$ imply that the initial configuration at instruction $l$ satisfies the guard: `gb_of` supplies both the program's required precondition and the coordinate bounds. The one-step run hypothesis begins at exactly the successor configuration produced by executing the first instruction from this initial configuration. Applying the initial-step extension property for halting runs (`Complexity.LogProg.AHalt.step`) prepends that step to the given run. It therefore yields a finite guarded run from the original configuration with the same halting answer.

**Key facts.** `Complexity.PathHard.gb_of`, `Complexity.LogProg.AHalt.step`.
