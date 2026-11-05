<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: BoolCircuit.foldr_or_lits_eq_clause_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Folding ORs over literals computes the clause's value

**Claim.** Let $\ell_1,\dots,\ell_k$ be a list of circuit literals on $n$ variables and let $x:\mathrm{Fin}\,n\to\mathrm{Bool}$ be an assignment. Right-folding disjunction over the literal evaluations $\ell_i.\mathrm{eval}\,x$, starting from $\mathrm{false}$, yields the same Boolean as evaluating, on $x$, the clause obtained by converting each circuit literal $\ell_i$ into its switching-lemma literal $\ell_i.\mathrm{toLiteral}$. Both are $\mathrm{true}$ exactly when at least one literal in the list is satisfied by $x$.

**Proof.** The clause evaluation $\mathrm{Clause.eval}\,c\,x$ is by definition $c.\mathrm{any}\,(\lambda\,l.\;l.\mathrm{eval}\,x)$, i.e. the disjunction of the literal values over the list $c$. After unfolding this, the claim is a statement about the list $\ell_1,\dots,\ell_k$, and we prove it by induction on that list.

1. **Empty list.** The right fold over the empty list returns its seed $\mathrm{false}$. On the other side, mapping $\mathrm{toLiteral}$ over the empty list gives the empty list, whose $\mathrm{any}$ is also $\mathrm{false}$. The two sides agree.

2. **Cons step.** Write the list as $\ell::\mathit{rest}$. The fold peels off the head, giving
\[
\ell.\mathrm{eval}\,x \;\lor\; \bigl(\text{fold over } \mathit{rest}\bigr),
\]
while mapping and taking $\mathrm{any}$ likewise peels off the head, giving
\[
(\ell.\mathrm{toLiteral}).\mathrm{eval}\,x \;\lor\; \bigl(\mathrm{any} \text{ over } \mathit{rest}.\mathrm{map}\,\mathrm{toLiteral}\bigr).
\]
The induction hypothesis identifies the two tails, so it remains only to check that the two heads agree, i.e. that converting a circuit literal to a switching-lemma literal preserves its value: $\ell.\mathrm{eval}\,x = (\ell.\mathrm{toLiteral}).\mathrm{eval}\,x$.

3. **The conversion preserves value.** Unfolding $\mathrm{toLiteral}$, the circuit literal $\ell=(\mathrm{idx},\mathrm{sign})$ becomes the literal with variable $\mathrm{idx}$ and negation flag $!\,\mathrm{sign}$. We split on the Boolean $\mathrm{sign}$. If $\mathrm{sign}=\mathrm{true}$, then $\ell.\mathrm{eval}\,x = x\,\mathrm{idx}$; the converted literal has negation flag $\mathrm{false}$, so its evaluation is also $x\,\mathrm{idx}$. If $\mathrm{sign}=\mathrm{false}$, then $\ell.\mathrm{eval}\,x = !\,x\,\mathrm{idx}$; the converted literal has negation flag $\mathrm{true}$, so its evaluation is likewise $!\,x\,\mathrm{idx}$. In both cases the values coincide, completing the induction. (The two conventions are complementary — a circuit literal's $\mathrm{sign}$ records which polarity is *asserted*, whereas a switching-lemma literal's $\mathrm{neg}$ records whether the variable is *negated* — which is exactly why the conversion flips the flag while preserving the value.)
