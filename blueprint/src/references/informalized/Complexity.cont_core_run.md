<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_core_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Core Run Correspondence

**Claim.** Running the pair-loader machine from the embedding of a core configuration for $t$ steps yields the embedding of the core machine’s configuration after $t$ steps.

**Proof.** The proof uses the general principle that a map commuting with one-step transitions also commutes with every finite run (`Turing.MultiTapeTM.runFrom_comm_of_step`). Verify that the embedding of core configurations commutes with one step. If the core configuration is halted, both machines remain in the corresponding halted configurations. If its state is active, the pair-loader machine uses exactly the core transition, with its state mapped into the right-hand summand; applying this mapped action to the embedded configuration gives the embedding of the core successor. The run correspondence follows for every $t$.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`.
