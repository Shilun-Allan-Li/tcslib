<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPad_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding commutes with machine runs

**Claim.** For a machine with $k$ work tapes and any $K\ge k$, running its padded machine for $t$ steps from a padded configuration gives the padding of the original machine's $t$-step run.

**Proof.** It suffices to check that one step commutes with padding, then iterate this identity over the $t$ steps (Turing.MultiTapeTM.runFrom_comm_of_step). If the configuration is halted, both machines leave it unchanged. Otherwise, the padded configuration presents the original machine with exactly the same symbols under the heads of its first $k$ tapes; the extra tapes are ignored when its transition is evaluated. The resulting action is the padding of the original action, and padding commutes with applying an action (Complexity.satPad_apply). Therefore one step commutes with padding, proving the run identity.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`, `Complexity.satPad_apply`.
