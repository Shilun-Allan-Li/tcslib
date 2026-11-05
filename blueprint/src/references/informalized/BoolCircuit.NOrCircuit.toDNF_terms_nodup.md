<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.NOrCircuit.toDNF_terms_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Terms of a clause-OR DNF have no repeated literals

**Claim.** Consider an OR-node whose children are all clauses: a list $cs$ of $\mathrm{NAnd}$-circuits, each of which is literally a clause $\mathrm{clause}(\mathit{lits}, h)$ — a conjunction of literals whose variable indices are pairwise distinct (that is, the list obtained by projecting each literal onto its variable index, $\mathit{lits}.\mathrm{map}\,\mathrm{idx}$, has no duplicates). Reading this OR-node as a DNF formula, the claim is that every term of that DNF is itself free of repeated literals: for each term $t$ appearing in $(\mathrm{node}\;cs).\mathrm{toDNF}.\mathrm{terms}$, the list $t$ has no duplicates.

**Proof.** An OR-node ORs its children together; when each child is a clause (a conjunction of literals), the node denotes a disjunction of conjunctions, i.e. a DNF, and its term list is obtained by turning each child clause into the list of literals it conjoins. Concretely, $(\mathrm{node}\;cs).\mathrm{toDNF}.\mathrm{terms}$ is exactly $cs.\mathrm{map}\,(\mathrm{clauseToTerm})$: one term per child, produced by the map $c \mapsto c.\mathrm{clauseToTerm}$. The proof unwinds this and defers to a single upstream fact.

1. **Locate the term.** Fix an arbitrary $t$ lying in $(\mathrm{node}\;cs).\mathrm{terms}$. Since this list is $cs.\mathrm{map}\,\mathrm{clauseToTerm}$, membership in a mapped list ($\mathtt{List.mem\_map}$) hands us a child circuit $c \in cs$ with $t = c.\mathrm{clauseToTerm}$. We may now replace $t$ by this image throughout.

2. **Expose the child as a clause.** The hypothesis on $cs$ says every child is literally a clause with distinct indices: applied to $c \in cs$ it yields literals $\mathit{lits}$, a proof $h$ that $\mathit{lits}.\mathrm{map}\,\mathrm{idx}$ has no duplicates, and the identity $c = \mathrm{clause}(\mathit{lits}, h)$. Substituting, the goal becomes that $\mathrm{clause}(\mathit{lits}, h).\mathrm{clauseToTerm}$ has no duplicate literals.

3. **Invoke the per-clause lemma.** This is precisely the statement that a clause with pairwise-distinct variable indices yields a term with no repeated literals ($\mathtt{NAndCircuit.clauseToTerm\_nodup}$): distinctness of the underlying indices $\mathit{lits}.\mathrm{map}\,\mathrm{idx}$ forces the resulting literals to be distinct as well (two equal literals would share an index). Feeding this lemma the data $\mathit{lits}$ and $h$ closes the goal.

Since $t$ was an arbitrary term of the DNF, every term is duplicate-free.

**Key facts.** `BoolCircuit.NAndCircuit.clauseToTerm_nodup`.
