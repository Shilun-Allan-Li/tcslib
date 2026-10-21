<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.NOrCircuit.node_eval_eq_toDNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Agreement of an OR-circuit with its DNF translation

**Claim.** Let $cs$ be a list of normal-form AND circuits on $n$ variables, and suppose each member of $cs$ is a base AND-clause — a conjunction of literals with distinct variable indices — rather than an AND-node assembled from OR-subcircuits. Let $C = \mathrm{node}(cs)$ be the normal-form OR circuit with children exactly the entries of $cs$, so that $C$ computes their disjunction. Then for every assignment $x : \mathrm{Fin}\,n \to \mathrm{Bool}$, the value $C(x)$ equals the value at $x$ of the DNF formula $\mathrm{toDNF}(C)$, obtained from $C$ by turning each child clause into a term.

**Proof.** Write $C = \mathrm{node}(cs)$. Both sides of the claimed identity are disjunctions indexed by the same list $cs$:

- The circuit evaluates by folding disjunction over the children,
\[
C(x) \;=\; \bigvee_{c \in cs} c(x),
\]
implemented as a right fold of $\lor$ over $cs$ with seed $\mathrm{false}$.
- The translation $\mathrm{toDNF}(C)$ is the DNF whose term list is $cs$ with each child replaced by its clause-term $\mathrm{clauseToTerm}(c)$; a DNF evaluates as the disjunction (an `any`) of its terms, so
\[
\mathrm{toDNF}(C)(x) \;=\; \bigvee_{c \in cs} \mathrm{Term.eval}\big(\mathrm{clauseToTerm}(c),\,x\big).
\]

The proof is by induction on the list $cs$, which is what aligns the right fold on the left with the `any` on the right term by term.

1. **Empty list.** If $cs = [\,]$, the circuit's fold returns its seed $\mathrm{false}$, and the DNF has no terms, so its disjunction is also $\mathrm{false}$. The two sides agree by unfolding the definitions.

2. **Cons step.** Suppose $cs = c :: cs'$. Peeling off the head on each side gives
\[
C(x) = c(x) \;\lor\; \Big(\bigvee_{d \in cs'} d(x)\Big),
\qquad
\mathrm{toDNF}(C)(x) = \mathrm{Term.eval}\big(\mathrm{clauseToTerm}(c),\,x\big) \;\lor\; \Big(\bigvee_{d \in cs'} \mathrm{Term.eval}(\mathrm{clauseToTerm}(d),x)\Big).
\]
The induction hypothesis — available because the clause-hypothesis is inherited by the tail $cs'$ — identifies the two bracketed tails. It therefore remains to match the two heads, i.e. to show $c(x) = \mathrm{Term.eval}(\mathrm{clauseToTerm}(c),\,x)$.

3. **The head is a clause.** By hypothesis the head $c$ is a base clause, say $c = \mathrm{clause}(\mathit{lits}, h)$ for some list of literals $\mathit{lits}$ (with distinct indices, recorded by $h$). For such a $c$: its circuit value is the conjunction of its literals, $c(x) = \mathit{lits}.\mathrm{foldr}(\lambda\, l\, a.\; l(x) \land a)\ \mathrm{true}$; and $\mathrm{clauseToTerm}(c) = \mathit{lits}.\mathrm{map}\,\mathrm{toLiteral}$ is the term got by reinterpreting each literal (a literal with sign flag $s$ becomes one with negation flag $\lnot s$, so the two literal evaluations coincide). The required head identity is then exactly
\[
\mathit{lits}.\mathrm{foldr}(\lambda\, l\, a.\; l(x) \land a)\ \mathrm{true}
\;=\;
\mathrm{Term.eval}\big(\mathit{lits}.\mathrm{map}\,\mathrm{toLiteral},\,x\big),
\]
which is the upstream fact that folding $\land$ over a literal list matches evaluating the corresponding term (`BoolCircuit.foldr_and_lits_eq_term_eval`). This closes the step and the induction.

The clause-hypothesis is genuinely needed and not mere scaffolding: for an AND-*node* $c$, the translation $\mathrm{clauseToTerm}(c)$ is the empty term, whose evaluation is the empty conjunction $\mathrm{true}$, whereas $c(x)$ is a conjunction of OR-subcircuit values and need not be true. Restricting to clauses is exactly what makes the per-child correspondence in Step 3 hold.

**Key facts.** `BoolCircuit.foldr_and_lits_eq_term_eval`.
