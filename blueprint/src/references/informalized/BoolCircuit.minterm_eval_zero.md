<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.minterm_eval_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the zero-variable minterm

**Claim.** For the unique Boolean assignments $v$ and $x$ on zero variables, the minterm specified by $v$ evaluates to true on $x.

**Proof.** The characterization of minterm evaluation says that the minterm specified by $v$ evaluates to true on $x$ exactly when $x=v$ (`minterm_eval_iff`). On the empty set of variables, any two assignments agree at every coordinate, since there are no coordinates; hence function extensionality gives $x=v$. The characterization therefore yields the result.

**Key facts.** `BoolCircuit.minterm_eval_iff`.
