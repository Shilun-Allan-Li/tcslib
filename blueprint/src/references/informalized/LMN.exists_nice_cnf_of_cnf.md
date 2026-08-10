<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: exists_nice_cnf_of_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every CNF has an equivalent "nice" CNF

**Claim.** For any `ψ : CNF n` there is `ψ' : CNF n` with
`CNF.width ψ' ≤ CNF.width ψ`, `CNF.eval ψ' x = CNF.eval ψ x` for all `x`, every
clause of `ψ'` duplicate-free (`c.Nodup`), and every clause variable-injective
(`l₁, l₂ ∈ c` with `l₁.var = l₂.var` implies `l₁ = l₂`) — exactly the four side
conditions the Bernoulli switching lemma for CNFs requires.

**Proof.** A single anonymous-constructor term; the witness is
`cleanCNF_D3 ψ = (ψ.filter (fun c => ¬clauseIsTaut c)).map dedupClauseVars`,
and the four components are the already-proved facts about it:

1. width: `cleanCNF_D3_width_le ψ`;
2. evaluation: `fun x => cleanCNF_D3_eval ψ x`;
3. no duplicate literals: `cleanCNF_D3_nodup ψ`;
4. variable-injectivity: `cleanCNF_D3_var_inj ψ`. ∎

**Note.** Dropping tautological clauses is sound because such a clause is
always satisfied (`clauseIsTaut_eval_true`); deduplication is sound only for
non-tautological clauses, which is where `dedupClauseVars_eval_of_not_taut`
enters — that lemma is currently `sorry` in this file, so component (2), and
hence this theorem, is not yet sorry-free.

**Used in.** `dtDepth_le_implies_nice_cnf` and `and_of_gates_has_cnf`.
