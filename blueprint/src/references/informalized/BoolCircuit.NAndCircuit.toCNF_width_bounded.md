<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.toCNF_width_bounded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width of a converted CNF is bounded by the clause size bound

**Claim.** Let `cs : List (NOrCircuit n)` and `w : ℕ` be such that every
`c ∈ cs` is a clause `NOrCircuit.clause lits h` with `lits.length ≤ w`. Then
`CNF.width (NAndCircuit.node cs).toCNF ≤ w`, where `CNF.width` is the maximum of
the clause widths (`(c.map Term.width).foldr max 0`).

**Proof.** `induction' cs with c cs ih generalizing w`.

1. Empty list: `toCNF` is `[]` and the fold is `0`, so `exact Nat.zero_le _`.
2. Cons: `obtain ⟨lits, h, hc, hw⟩ := h_clauses c (by simp)` gives the head in
   clause form together with `lits.length ≤ w`; `simp_all [NAndCircuit.toCNF]`
   turns the goal into a `max` of the head width and the tail's fold.
3. Head: `unfold CNF.width` and `simp [*, NOrCircuit.clauseToTerm_width]`
   discharge it — the head clause's width is `lits.length`, which is `≤ w` by
   `hw`.
4. Tail: `convert ih w h_clauses using 1`, followed by `unfold CNF.width; simp`
   to match the tail fold with the induction hypothesis's `CNF.width` form.

**Used in.** Nothing yet — the CNF counterpart of
`NOrCircuit.toDNF_width_bounded`, which is what the switching lemma's width
hypothesis consumes.
