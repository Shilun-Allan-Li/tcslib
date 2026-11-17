<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecAcceptance_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Formula Evaluation

**Claim.** The acceptance CNF evaluates to true on the Boolean encoding of a row exactly when the row is halted and its output summary is accepting.

**Proof.** The acceptance CNF consists of two unit clauses: one requires the bit representing the halted state, and the other requires the summary bit representing acceptance. By the definition of clause evaluation, each unit clause evaluates to true exactly when its literal does. The row encoding sets the halted-state bit to true exactly when the row's state is none, and sets the accepting-summary bit to true exactly when the summary is `.accept`. Thus the conjunction of the two clauses is true precisely when both stated conditions hold.
