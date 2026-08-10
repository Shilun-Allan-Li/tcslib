<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.toDNF_width_bounded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width bound for the DNF of a depth-2 OR-circuit

**Claim.** Let `cs : List (NAndCircuit n)` and `w : ℕ`, and suppose every
`c ∈ cs` is a clause `NAndCircuit.clause lits h` with `lits.length ≤ w`. Then
`DNF.width (NOrCircuit.node cs).toDNF ≤ w`.

**Proof.**

1. `simp [NOrCircuit.toDNF]` rewrites the DNF as `cs.map NAndCircuit.clauseToTerm`.
2. Induct on `cs`. The empty case is closed by
   `simp_all +decide [DNF.width]` (`DNF.width [] = 0`).
3. In the cons case `DNF.width` is the `foldr max 0` of the term widths, so
   `simp_all` reduces the goal to bounding the head term's width by `w`, the
   tail being handled by the induction hypothesis.
4. For the head, `rcases h_clauses.1` extracts `lits`, the `Nodup` proof `h`
   and `hl : lits.length ≤ w`; then
   `NAndCircuit.clauseToTerm_width lits h ▸ hl` rewrites `lits.length` into
   `Term.width …` and supplies the bound.

**Remark.** `DNF.width` is the maximum term width, so the bound is uniform
over clauses; no clause-count hypothesis is needed.
