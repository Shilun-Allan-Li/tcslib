<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.NOrCircuit.toDNF_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Variable-injectivity of literals in the DNF of an OR of clauses

**Claim.** Fix $n\in\mathbb{N}$ and a list $c_1,\dots,c_m$ of normal-form AND circuits on $n$ variables, and assume each $c_i$ is a *base clause* — that is, $c_i=\mathrm{clause}(\ell_1,\dots,\ell_{k_i})$ for some list of circuit literals whose variable indices are pairwise distinct. Let $F$ be the DNF formula produced from the OR circuit $\mathrm{node}(c_1,\dots,c_m)$ by turning each clause $c_i$ into the term built from its literals. Then $F$ is *variable-injective term by term*: in any single term of $F$, any two literals that share the same variable must be one and the same literal.

**Proof.** The statement looks like it ranges over the whole formula $F$, but the argument is a one-step reduction to a fact about a *single* clause: every term of $F$ is literally the term of one of the clauses $c_i$, and for a single base clause the claim is already known.

1. **Unfold the goal.** Fix a term $t$ of $F=\mathrm{node}(c_1,\dots,c_m).\mathrm{toDNF}$, and fix two literals $\ell_1,\ell_2\in t$ with $\ell_1.\mathrm{var}=\ell_2.\mathrm{var}$. We must show $\ell_1=\ell_2$. Here a literal carries a variable index in $\mathrm{Fin}\,n$ together with a sign, and $\ell.\mathrm{var}$ is its variable; so the hypothesis says the two literals name the same propositional variable, and the conclusion forces them to agree on the sign as well (and on everything else).

2. **Identify where $t$ comes from.** By construction, converting the OR circuit $\mathrm{node}(c_1,\dots,c_m)$ to DNF simply disjoins the clauses: the terms of $F$ are exactly the clause-terms $c.\mathrm{clauseToTerm}$ as $c$ ranges over the list $c_1,\dots,c_m$ (this is what unfolding $\mathrm{toDNF}$ on a $\mathrm{node}$ yields). Hence there is some clause $c$ in the list with
\[ t = c.\mathrm{clauseToTerm}. \]

3. **Use that $c$ is a base clause.** By hypothesis every clause in the list is a base clause, so for this particular $c$ there is a list of literals $\ell'_1,\dots,\ell'_k$ with pairwise-distinct variable indices — i.e. the map sending each literal to its index is duplicate-free — such that $c=\mathrm{clause}(\ell'_1,\dots,\ell'_k)$. Thus $t$ is the clause-term of an honest base clause whose literals occupy distinct variables.

4. **Apply the single-clause lemma.** The variable-injectivity of a lone base clause is exactly the content of the upstream fact *variable-injectivity within one clause-term* (`NAndCircuit.clauseToTerm_var_inj`): in $\mathrm{clause}(\ell'_1,\dots,\ell'_k).\mathrm{clauseToTerm}$, any two member literals sharing a variable are equal. Feeding it $\ell_1,\ell_2$ and the hypothesis $\ell_1.\mathrm{var}=\ell_2.\mathrm{var}$ gives $\ell_1=\ell_2$, which is the goal. (Morally this holds because the distinctness of the variable indices means no variable is used twice in the clause, so a shared variable can only come from a literal paired with itself.) $\blacksquare$

**Key facts.** `BoolCircuit.NAndCircuit.clauseToTerm_var_inj`.
