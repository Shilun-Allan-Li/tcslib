<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitEmbed_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State renaming preserves computation

**Claim.** If the host transition at every embedded state is the state-renaming of the source transition, then the host run from the renamed initial configuration agrees at every time with the renamed source run.

**Proof.** First verify that one step commutes with state renaming. If a configuration is halted, both machines leave it unchanged, and renaming preserves that halted configuration. If its state is $q$, the transition-agreement hypothesis says the host action at $emb(q)$ is the source action with its successor state renamed. The actions therefore update the tape contents, head positions, and output in the same way, while their successor states correspond under $emb$. Hence one host step from the renamed configuration is the renaming of one source step. The run-commutation theorem (`runFrom_comm_of_step`) iterates this one-step equality and gives the claimed equality for every number of steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`.
