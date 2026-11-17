<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.mem_PiP_of_forall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Closure Under Universal Polynomial Witnesses

**Claim.** For nonzero $i$, the stated universal polynomial-witness condition for membership in $L'$ implies that $L$ belongs to $\Pi_i^P$.

**Proof.** The supplied proof attempts to apply the closure theorem for existential polynomial witnesses to the complement of $L$. Negating the assumed equivalence turns the universal condition over length-bounded strings into the existence of a length-bounded string whose paired encoding is outside $L'$. That is the existential-witness form needed to transfer membership to the complement, after which complement duality gives the desired $\Pi_i^P$ conclusion. However, as supplied, the proof passes $hL' : L'\in\Pi_i^P$ to `Complexity.mem_SigmaP_of_exists`, whose stated hypothesis requires $L'\in\Sigma_i^P$; the payload gives no conversion that resolves this mismatch.

**Key facts.** `Complexity.mem_SigmaP_of_exists`.

**Caveat.** The supplied proof source appears to have a type mismatch: the closure lemma requires its auxiliary language in $\Sigma_i^P$, but the theorem hypothesis provides membership in $\Pi_i^P$. The remaining proof route is therefore not justified by the provided statements.
