<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.leftCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep run under left-block embedding

**Claim.** Under the stated transition compatibility, running the extended machine for any number of steps from the embedded configuration yields the embedding of the original machine's run.

**Proof.** Let the embedding send each configuration to its left-block embedding, with the chosen additional tape contents and head positions fixed. The one-step simulation lemma says that one step of the extended machine after embedding equals embedding after one step of the original machine (`Turing.FinTM.leftCfg_step`). Iterating this commuting relation for $t$ steps gives the result, by the general fact that a map commuting with one-step evolution also commutes with every finite iterate (`Turing.MultiTapeTM.runFrom_comm_of_step`).

**Key facts.** `Turing.FinTM.leftCfg_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
