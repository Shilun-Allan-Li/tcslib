<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.step_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Removing an Initial Run Step

**Claim.** If there is a finite guarded run from the configuration obtained by taking one step of the specified program from instruction $l$ and state $st$ to a configuration $c$, then there is a finite guarded run from instruction $l$ and state $st$ to $c$.

**Proof.** The register bounds on $st$ imply that the initial configuration at instruction $l$ satisfies the guard, by `gb_of`. The hypothesis gives a finite guarded run from the configuration after one program step. The initial-step extension property for runs (`Complexity.LogProg.AReach.step`) prepends that step, producing the claimed run from the original configuration to $c$.

**Key facts.** `Complexity.PathHard.gb_of`, `Complexity.LogProg.AReach.step`.
