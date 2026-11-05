<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.toCNF_terms_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every clause of a converted CNF is duplicate-free

**Claim.** Let `cs : List (NOrCircuit n)` with every child a clause,
`h_clauses : ∀ c ∈ cs, ∃ lits h, c = NOrCircuit.clause lits h`. Then every
`t ∈ (NAndCircuit.node cs).toCNF` satisfies `t.Nodup`. This is the clause-level
`Nodup` side condition the switching lemma requires, stated for the whole
formula rather than one clause.

**Proof.** Three steps, no induction (the work is already in the per-clause
lemma).

1. `intros t ht`, then `List.mem_map.mp ht` — `toCNF` on a node is
   `cs.map NOrCircuit.clauseToTerm` — produces the source child `c ∈ cs` with
   `t = c.clauseToTerm` (substituted by `rfl`).
2. `h_clauses c hc` rewrites `c` as `NOrCircuit.clause lits h`.
3. `exact NOrCircuit.clauseToTerm_nodup lits h`.

**Used in.** Nothing yet — the mirror of `NOrCircuit.toDNF_terms_nodup`, which
serves the DNF direction actually consumed by the switching-lemma files.
