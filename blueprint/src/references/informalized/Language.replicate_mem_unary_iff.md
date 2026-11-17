<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: Language.replicate_mem_unary_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of unary strings

**Claim.** For every set \(S\subseteq\mathbb N\) and every natural number \(n\), the all-true Boolean list of length \(n\) belongs to the unary language determined by \(S\) exactly when \(n\in S\).

**Proof.** By the membership characterization of the unary language (`Language.mem_unary_iff`), membership of the replicated list says both that all its entries are true and that its length lies in \(S\). Its length is \(n\). Every entry of a list produced by replicating `true` is true, so the first condition always holds; the remaining condition is exactly \(n\in S\).

**Key facts.** `Language.mem_unary_iff`.
