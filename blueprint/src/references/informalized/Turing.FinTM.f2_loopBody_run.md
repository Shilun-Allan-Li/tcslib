<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBody_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Loop-Body Machine

**Claim.** Under the stated activity and anchor-state hypotheses, the augmented machine's configuration after $t$ steps is the lift of the base machine's configuration, with the release flag and extra-tape marker specified in the claim.

**Proof.** Proceed by induction on $t$. At $t=0$, the run has not moved, and the initial lifted configuration already has the original release flag and a blank extra-tape cell; the assumption that the base configuration has a present state supplies the required initial-state case. For the successor step, use the induction hypothesis to identify the augmented configuration after $t$ steps. The base computation is still live at time $t$, so its state is some $q$. The anchor hypothesis says either that $t=0$ with release true, or that the base state is not the anchor. In the first case the release flag is true; in the second case the state is not the anchor. Hence the augmented machine does not trigger its special stopping transition at the anchor with release false. Its ordinary transition therefore simulates one base step, resets the release flag to false, and sets the extra-tape flag to true precisely if the resulting base configuration is halted (`f2_loopBody_step`). The successor-run identity (`runFrom_succ_eq_step'`) identifies this step with the run at time $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_loopBody_step`.
