<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.minterm_eval_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minterm Characterizes an Assignment

**Claim.** The minterm specified by an assignment $v$ evaluates to true on an assignment $x$ exactly when $x=v$.

**Proof.** The minterm is an AND of one literal for each variable. An AND tree evaluates to true exactly when every child does (`TreeCircuit.eval_node_true_iff`). If the minterm is true, then for each index $i$ the list contains the literal specified by $v(i)$, and that literal's truth forces $x(i)=v(i)$ (`TreeCircuit.eval_lit`, `lit_eval_iff`). Agreement at every index gives $x=v$. Conversely, if $x=v$, every literal in the minterm is true by the same literal-evaluation criterion. Hence all children of the AND are true, so the minterm evaluates to true.

**Key facts.** `BoolCircuit.TreeCircuit.eval_node_true_iff`, `BoolCircuit.TreeCircuit.eval_lit`, `BoolCircuit.lit_eval_iff`.
