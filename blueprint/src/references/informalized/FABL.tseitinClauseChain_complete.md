<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.tseitinClauseChain_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiability of the clause chain

**Claim.** Under the stated distinctness and disjointness assumptions, if the initial assignment satisfies a literal in the original list, then the recursively filled assignment satisfies at least one literal in every clause of the constructed chain.

**Proof.** Proceed by induction on the length of the original literal list, splitting according to the recursive definition of the chain. In the recursive case, write the first four original literals as $a,b,c,d$, the auxiliary literal as $u$, and let $A'$ be the assignment after this step. The step-invariant lemma shows that the next original list, beginning with $\neg u,c,d$, and the remaining auxiliary list still have distinct indices and disjoint index sets (`tseitinStep_invariants`).

If the original assignment satisfies $a$ or $b$, the rule sets the new coordinate to the sign opposite the one required by $u$. Since the first two literals’ indices are disjoint from all auxiliary indices, and the remaining auxiliary steps do not change those coordinates, the satisfied original literal remains satisfied in the final assignment. Thus the first clause $[a,b,u]$ is satisfied. If instead neither $a$ nor $b$ is satisfied, the initial witness to satisfaction must lie in the tail beginning with $c,d$. Its index differs from $u$ by disjointness, so updating the auxiliary coordinate preserves that witness in $A'$. The rule sets the coordinate to the sign required by $u$, so the first clause is satisfied as well. In either case, the next original list $[\neg u,c,d,\ldots]$ has a satisfied literal under $A'$: in the first case it is $\neg u$, and in the second it is the preserved tail witness. The induction hypothesis therefore says that all clauses in the recursively remaining chain are satisfied after the remaining auxiliary coordinates are filled. Together with satisfaction of the first clause, this proves the recursive case.

When there are fewer than four original literals, or no auxiliary literal remains, the recursive definitions produce just the terminal clause consisting of the current original list, and no further update occurs. The assumed witness in that list directly satisfies this sole clause.

**Key facts.** `FABL.tseitinStep_invariants`, `FABL.literalListHoldsDecision_eq_true`, `FABL.fillTseitinClauseAux_eq_of_not_mem`.
