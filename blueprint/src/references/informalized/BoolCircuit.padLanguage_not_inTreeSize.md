<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.padLanguage_not_inTreeSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure of Bounded Tree-Size Representation

**Claim.** If every circuit on $\ell(n_0)$ inputs of size at most $T(n_0)$ disagrees with $F_{n_0}$ somewhere, then the padded language has no exact tree-circuit representation with size bounded by $T$.

**Proof.** Suppose, for contradiction, that a representing family $D$ exists, with the stated size bound and exact language recognition. At length $n_0$, exact recognition implies that $D_{n_0}$ and the padded circuit have the same Boolean evaluation on every assignment: the language equivalence on Boolean lists transfers to assignments via `BoolCircuit.eval_eq_of_iff`. The padded-family evaluation theorem identifies this common value with $F_{n_0}$ applied to the first $\ell(n_0)$ coordinates (`BoolCircuit.padFamily_eval`). Restrict $D_{n_0}$ to those coordinates, padding the other inputs by false. Restriction preserves circuit size (`BoolCircuit.restrictCircuit_size`), so the restricted circuit has size at most $T(n_0)$. Its evaluation is exactly $F_{n_0}$ on every assignment, by the restriction evaluation theorem for circuits computing a function of the first inputs (`BoolCircuit.restrictCircuit_eval_of_onFirst`). This contradicts the hypothesis that every such small circuit disagrees somewhere.

**Key facts.** `BoolCircuit.eval_eq_of_iff`, `BoolCircuit.padFamily_eval`, `BoolCircuit.restrictCircuit_size`, `BoolCircuit.restrictCircuit_eval_of_onFirst`.
