<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: dedupClauseVars_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deduplication does not lengthen a clause

**Claim.** For any clause `c : List (Literal n)`,
`(dedupClauseVars c).length ≤ c.length`.

**Proof.**

1. `dedupClauseVars c = c.pwFilter …` is a sublist of `c`
   (`List.pwFilter_sublist`), recorded as membership in `c.sublists`
   (`h_sublist`, via `simp +decide [dedupClauseVars]`).
2. Convert membership back to the sublist relation with
   `List.mem_sublists.mp` and conclude by `List.Sublist.length_le`.

**Used in.** `cleanCNF_D3_width_le` — since `Term.width` is just `length`, this
is the per-clause half of "cleaning never increases CNF width".
