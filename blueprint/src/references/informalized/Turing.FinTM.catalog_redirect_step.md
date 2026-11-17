<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.catalog_redirect_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Redirected Step Correspondence

**Claim.** Taking one step from the redirected configuration of any configuration $c$ of $M$ yields the redirected configuration of the result of taking one step from $c$ in $M$.

**Proof.** Split according to whether $c$ is already halted. If its state is absent and its last output is the designated bit, its redirected state is also halted, so both machines leave the configuration unchanged. If its last output is not that bit, the redirected configuration is in the added loop state; the loop-invariance lemma says that one step leaves it unchanged, which agrees with redirecting the halted original configuration (`catalog_redirect_loop`). If instead $c$ has an active state $q$, redirection preserves the scanned input symbol and work-tape symbols. The redirected transition therefore uses exactly the original transition from $q$. It records the newly emitted bit when there is one, or retains the previous last bit when there is not, and handles the resulting successor or halting state according to the redirection rule. The redirected-action correspondence then identifies the resulting configuration with the redirection of the original next configuration (`catalog_redirect_apply`).

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.FinTM.catalog_redirect_loop`, `Turing.FinTM.catalog_redirect_apply`.
