<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.mem_iff_of_card_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance from Equal Reachability Counts

**Claim.** Under the deciding-space hypothesis, if the reachable-code sets for windows $s$ and $s+1$ have equal cardinality, then $x$ is in the language exactly when some code reachable by zero or more encoded $s$-window steps represents a halted accepting configuration.

**Proof.** Suppose first that $x$ is in the language. The deciding hypothesis supplies a choice word whose run halts with output $[\mathrm{true}]$. Equal reachable-set cardinalities ensure that every finite choice word remains within window $s$ (`Complexity.ExpBFS.winRun_of_card_eq`); in particular, this run does. The characterization of encoded reachability by window-bounded runs (`Complexity.ExpBFS.rcode_iff`) therefore gives a reachable code for its final configuration. The characterization of membership in the acceptance language (`Complexity.Codec.mem_acceptLang`), using the final configuration’s window bound, code, halted state, and output, proves that this code encodes acceptance.

Conversely, suppose a code is reachable from the initial code and its paired input belongs to the acceptance language. The initial-code characterization (`Complexity.Codec.mem_initLang`) identifies the starting code with the initial configuration code. The acceptance-language characterization supplies a window-bounded halted configuration with output $[\mathrm{true}]$ at the endpoint. The general result that such a code path witnesses acceptance (`Complexity.Codec.mem_of_codePath`) then implies $x\in L$.

**Key facts.** `Complexity.ExpBFS.winRun_of_card_eq`, `Complexity.ExpBFS.rcode_iff`, `Complexity.Codec.mem_acceptLang`, `Complexity.Codec.mem_initLang`, `Complexity.Codec.mem_of_codePath`.
