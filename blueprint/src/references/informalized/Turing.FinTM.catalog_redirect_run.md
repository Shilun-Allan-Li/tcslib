<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.catalog_redirect_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Redirected Run Correspondence

**Claim.** After $t$ steps from the redirected machine’s initial configuration on $x$, its state corresponds to the original machine’s state and last output bit at time $t$, its input-head position and work tapes match those of the original machine, and its output tape is empty.

**Proof.** The redirected machine’s initial configuration is the redirected configuration of the original machine’s initial configuration. At every step, the redirected step-correspondence lemma states that stepping a redirected configuration gives the redirection of the original machine’s next configuration (`catalog_redirect_step`). Iterating this one-step equality yields the equality of runs for every time $t$ (`MultiTapeTM.runFrom_comm_of_step`). Applying it to the initial configuration gives the asserted correspondence.

**Key facts.** `Turing.FinTM.catalog_redirect_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
