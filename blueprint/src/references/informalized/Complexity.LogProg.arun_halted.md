<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean :: Complexity.LogProg.arun_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Persistence of Halted Configurations

**Claim.** A configuration with no active control label, register assignment $v$, and stored answer $res$ remains unchanged after any number of abstract steps.

**Proof.** Induct on the number of steps. At zero steps, the run is the initial configuration. For the successor case, the successor-run identity (`arun_succ`) expresses the run as first taking one abstract step and then running for the remaining number of steps. By the definition of the abstract transition, a configuration with no active label is fixed by that first step. The induction hypothesis therefore gives the original configuration after the remaining steps as well.

**Key facts.** `Complexity.LogProg.arun_succ`.
