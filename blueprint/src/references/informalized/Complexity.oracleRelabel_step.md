<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.oracleRelabel_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relabeling commutes with one oracle step

**Claim.** For an oracle Turing machine whose states are relabeled by a bijection, one step from a relabeled configuration equals the relabeling of the configuration reached by one original step.

**Proof.** If the configuration is halted, both machines leave it unchanged, so the claimed equality follows. Otherwise write its state as $q$. The relabeled machine tests whether the relabeled state $e(q)$ is its query state $e(q_{\mathrm{Query}})$. Injectivity of $e$ makes this equivalent to $q=q_{\mathrm{Query}}$. In the query-state case, both machines consult the same query string and oracle; the chosen answer state is then relabeled by $e$, giving the same resulting configuration. In the other case, both use the corresponding transition: the relabeled transition is the original transition at $e^{-1}(e(q))=q$, with its successor state relabeled. Relabeling this transition's action on the relabeled configuration agrees with relabeling the result of applying the original action (Turing.Cfg.mapState_apply).

**Key facts.** `Turing.Cfg.mapState_apply`.
