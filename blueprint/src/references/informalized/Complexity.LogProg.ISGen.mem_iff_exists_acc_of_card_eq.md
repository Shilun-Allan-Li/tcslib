<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean :: Complexity.LogProg.ISGen.mem_iff_exists_acc_of_card_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language Membership from Stable Reachability Counts

**Claim.** If the reachable-code sets for the windows of radii $s-1$ and $s$ have equal cardinality, then $x\in L$ exactly when some code reachable within the radius-$s$ window encodes an accepting configuration.

**Proof.** For the forward implication, choose the halting computation witnessing acceptance of $x$ under the decision hypothesis. Equality of the reachable-set cardinalities, after rewriting $s-1+1=s$, implies that every choice sequence stays within the radius-$(s-1)$ window (`Complexity.ExpBFS.winRun_of_card_eq`). Since $s-1\le s$, monotonicity of window-bounded runs gives a run within radius $s$ (`Complexity.ExpBFS.WinRun.mono`). The run's final configuration is also in that window (`Complexity.ExpBFS.WinRun.last`), and its code is reachable by the run-to-code characterization (`Complexity.ExpBFS.rcode_iff`). Halting and output $[\text{true}]$ make this final code an accepting code, by the acceptance-code characterization (`Complexity.Codec.mem_acceptLang`).

For the reverse implication, a reachable accepting code implies $x\in L$ by the decision-to-language principle for code paths (`Complexity.LogProg.ISGen.mem_of_exists_acc`).

**Key facts.** `Complexity.ExpBFS.winRun_of_card_eq`, `Complexity.ExpBFS.WinRun.mono`, `Complexity.ExpBFS.WinRun.last`, `Complexity.ExpBFS.rcode_iff`, `Complexity.Codec.mem_acceptLang`, `Complexity.LogProg.ISGen.mem_of_exists_acc`.
