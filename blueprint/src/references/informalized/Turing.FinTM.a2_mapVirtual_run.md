<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_mapVirtual_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a mapped computation

**Claim.** Starting from a virtual configuration with a correctly marked input-head boundary, each simulated step can be matched by a step of the constructed machine, preserving the fixed input position, buffers, and output prefix; consequently this matching holds for every number of steps.

**Proof.** Induct on $t$. At time zero, choose the original tag: the boundary condition holds by hypothesis, and the two configurations are identical by the definition of the virtual configuration. For the successor step, apply the induction hypothesis to obtain a tag and matching virtual configuration at time $t$. The one-step simulation lemma (`Turing.FinTM.a2_mapVirtual_step`) then supplies a tag correctly marking the simulated machine's next input-head position and identifies the constructed machine's next configuration with the corresponding virtual configuration. Rewriting both runs at successor time as one step from time $t$ (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) completes the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.a2_mapVirtual_step`.
