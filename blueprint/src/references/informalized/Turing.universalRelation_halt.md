<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universalRelation_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Checkpoint Relation Preserves Halting

**Claim.** If the checkpoint relation holds between a decoded machine configuration and the corresponding universal-machine configuration, then one is halted exactly when the other is halted.

**Proof.** Unpack the checkpoint relation: the universal configuration is a right-extended configuration built from the simulation configuration. Its state is obtained by mapping the source state into the right summand of a sum type. A mapped optional value is `none` exactly when its original value is `none`. Therefore the universal configuration is halted precisely when the source configuration is halted.
