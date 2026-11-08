<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.runFrom_of_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Persistence after halting

**Claim.** If a configuration is halted, then running any multi-tape machine from it for any number of steps leaves the configuration unchanged.

**Proof.** Induct on the number of steps. At zero steps the run is the initial configuration. For the successor case, split off the first $t$ steps using the run-addition law (`Turing.MultiTapeTM.runFrom_add`). By induction, those steps leave the halted configuration unchanged. A single step from a halted configuration is itself the identity (`Turing.MultiTapeTM.step_of_halt`), so the additional step also changes nothing.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.step_of_halt`.
