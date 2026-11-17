<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.PiP_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Zeroth Pi Level

**Claim.** The zeroth level of the polynomial hierarchy, $\Pi_0^P$, is exactly the class $P$.

**Proof.** The Pi class at level $i$ equals the alternating class with universal first quantifier (\texttt{PiP\_eq\_altClass}). At level zero there are no quantifiers, so the alternating class is $P$ (\texttt{altClass\_zero}). Substituting $i=0$ gives $\Pi_0^P=P$.

**Key facts.** `Complexity.PiP_eq_altClass`, `Complexity.altClass_zero`.
