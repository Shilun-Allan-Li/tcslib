<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.acceptTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recognizer Run Correspondence

**Claim.** After $t$ steps from its initial configuration on $x$, the halting recognizer has the configuration corresponding to the configuration reached by $M$ after $t$ steps on $x$.

**Proof.** The recognizer's initial configuration is exactly the configuration assigned by the correspondence map to $M$'s initial configuration. The step-commutation fact (`Complexity.acceptCfg_step`) says that taking one recognizer step after applying this map gives the same configuration as first taking one step of $M$ and then applying the map. Iterating this equality gives the corresponding equality after any number $t$ of steps, by the run-commutation theorem (`Turing.MultiTapeTM.runFrom_comm_of_step`).

**Key facts.** `Complexity.acceptCfg_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
