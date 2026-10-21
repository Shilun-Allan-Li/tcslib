<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.toDNF_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Variable-injectivity inside every term of the converted DNF

**Claim.** Let `cs : List (NAndCircuit n)` be such that every `c ∈ cs` is a
clause `NAndCircuit.clause lits h`. Then for every term
`t ∈ (NOrCircuit.node cs).toDNF` and all `l₁, l₂ ∈ t`, `l₁.var = l₂.var`
implies `l₁ = l₂`.

**Proof.**

1. `intro t ht l₁ hl₁ l₂ hl₂ hvar`.
2. Exhibit the originating child: `∃ c ∈ cs, t = c.clauseToTerm`, obtained by
   `unfold NOrCircuit.toDNF at ht; aesop` (the `node` branch of `toDNF` is
   `cs.map NAndCircuit.clauseToTerm`), and substitute with `rfl`.
3. `h_clauses c hc` replaces `c` by `NAndCircuit.clause lits h`, and
   `NAndCircuit.clauseToTerm_var_inj lits h l₁ hl₁ l₂ hl₂ hvar` closes the
   goal.

**Used in.** Together with `NOrCircuit.toDNF_terms_nodup` and
`NOrCircuit.toDNF_width_bounded`, this discharges the well-formedness side
conditions the switching lemma imposes on a DNF; the per-clause content lives
in `NAndCircuit.clauseToTerm_var_inj`, which in turn rests on the constructor's
`Nodup` invariant.
