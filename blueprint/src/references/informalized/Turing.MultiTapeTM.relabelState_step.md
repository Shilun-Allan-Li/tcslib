<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/StateRenaming.lean :: Turing.MultiTapeTM.relabelState_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relabelling Commutes with One Step

**Claim.** Taking one step after relabelling a configuration gives the same result as taking a step first and then relabelling the resulting state.

**Proof.** Consider the two possible forms of the configuration’s state. If it is halted, the machine leaves the configuration unchanged, so both sides are the relabelled configuration. If its state is $q$, the relabelled configuration has state $e(q)$. The relabelled transition at $e(q)$ uses the original transition at $e^{-1}(e(q))=q$, so it has the same head movements, tape actions, and output as the original transition, with its successor state relabelled. Applying this transition to the relabelled configuration agrees with applying the original transition and then relabelling the result; this is the compatibility of action application with state mapping (`Cfg.mapState_apply`).

**Key facts.** `Turing.Cfg.mapState_apply`.
