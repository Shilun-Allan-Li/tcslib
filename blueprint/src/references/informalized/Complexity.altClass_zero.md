<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.altClass_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Round Alternating Class

**Claim.** For either initial quantifier, the zero-round alternating class is exactly the class of polynomial-time decidable binary languages $\mathsf{P}$.

**Proof.** At zero rounds, the alternating quantifier construction simply tests whether the input belongs to its underlying language $V$; the initial quantifier has no effect. Thus, if a language $L$ belongs to the zero-round class, its defining equivalence at every input says precisely that membership in $L$ agrees with membership in $V$. Hence $L=V$, and since $V\in\mathsf P$, also $L\in\mathsf P$. Conversely, for any $L\in\mathsf P$, choose $V=L$ and take the two numerical parameters in the definition to be zero. The zero-round predicate is then just membership in $L$, so the required equivalence holds and $L$ belongs to the alternating class.
