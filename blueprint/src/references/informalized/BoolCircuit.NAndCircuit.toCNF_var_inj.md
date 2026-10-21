<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.NAndCircuit.toCNF_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Variable-injectivity within an AND-node's CNF clauses

**Claim.** Let $cs$ be a list of normal-form OR circuits on $n$ variables, and suppose each $c \in cs$ is a base OR-clause: there is a list $lits$ of circuit literals whose variable indices are pairwise distinct, with $c = \mathrm{clause}\,lits$. Form the CNF of the AND-node over $cs$ by converting each member of $cs$ into a clause. Then within any single clause of this CNF, any two literals with the same variable index are equal — in particular they carry the same negation flag.

**Proof.** The result is a one-step reduction: it transports the corresponding property of a *single* OR-clause (established separately as `clauseToClause_var_inj`) across the trivial clause structure of an AND-node's CNF.

1. **Set-up.** Fix a clause $t$ occurring in the CNF of the AND-node over $cs$, and fix two literals $l_1, l_2 \in t$ with the same variable index, $\mathrm{var}(l_1) = \mathrm{var}(l_2)$. We must show $l_1 = l_2$.

2. **Identify the clause.** The CNF of an AND-node is assembled by converting each OR circuit in $cs$ into a clause and taking the resulting list; an AND introduces no clauses of its own and does no merging. Unfolding this definition, the clauses of the CNF are exactly the conversions $\mathrm{clauseToClause}(c)$ for $c \in cs$. Hence there is some $c \in cs$ with $t = \mathrm{clauseToClause}(c)$.

3. **Expose the base form of that OR-clause.** By hypothesis every member of $cs$ is a base OR-clause, so applying the hypothesis to this particular $c$ yields a literal list $lits$ whose variable indices are pairwise distinct and for which $c = \mathrm{clause}\,lits$. Substituting, our clause is $t = \mathrm{clauseToClause}(\mathrm{clause}\,lits)$, and $l_1, l_2$ are members of it.

4. **Invoke the single-clause lemma.** The per-clause injectivity fact (`NOrCircuit.clauseToClause_var_inj`) states precisely that in the clause obtained by converting a base OR-clause $\mathrm{clause}\,lits$ with distinct literal indices, any two members sharing a variable index are equal. Applying it to $l_1, l_2$ together with $\mathrm{var}(l_1) = \mathrm{var}(l_2)$ gives $l_1 = l_2$, as required.

The two membership facts needed in step 4 — that $l_1$ and $l_2$ lie in $\mathrm{clauseToClause}(\mathrm{clause}\,lits)$ — are just the original hypotheses $l_1, l_2 \in t$ rewritten along the identification of $t$ from steps 2–3, and require no real argument.

**Key facts.** `BoolCircuit.NOrCircuit.clauseToClause_var_inj`.
