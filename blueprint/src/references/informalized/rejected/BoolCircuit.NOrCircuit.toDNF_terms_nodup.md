<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.toDNF_terms_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every term of the converted DNF is duplicate-free

**Claim.** Let `cs : List (NAndCircuit n)` be such that every `c ∈ cs` is a
clause `NAndCircuit.clause lits h` (with `(lits.map Lit.idx).Nodup`). Then
every term `t ∈ (NOrCircuit.node cs).toDNF` satisfies `t.Nodup`.

**Proof.** A three-step chain, no induction.

1. `intro t ht`, then `List.mem_map.mp ht` produces the child circuit `c ∈ cs`
   with `t = c.clauseToTerm` — this uses only that `toDNF` on a `node` is
   `cs.map NAndCircuit.clauseToTerm`.
2. `h_clauses c hc` (destructured with `obtain`) replaces `c` by
   `NAndCircuit.clause lits h`.
3. Conclude with `NAndCircuit.clauseToTerm_nodup lits h`.

**Used in.** Supplies the `Nodup`-of-terms side condition that the switching
lemma's DNF interface requires of a DNF produced from a depth-2 normal-form
circuit; `NAndCircuit.toCNF_terms_nodup` is the dual.
