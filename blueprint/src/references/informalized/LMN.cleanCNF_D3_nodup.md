<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: cleanCNF_D3_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every clause of a cleaned CNF is duplicate-free

**Claim.** For every `ψ : CNF n` and every clause `c ∈ cleanCNF_D3 ψ`, `c.Nodup`.

**Proof.** One line. Every clause of `cleanCNF_D3 ψ` is in the image of
`dedupClauseVars` (`List.mem_map.mp hc` gives `c = dedupClauseVars c'` for some
`c'` in the filtered list), and `dedupClauseVars_nodup c'` gives `Nodup`.

**Used in.** `exists_nice_cnf_of_cnf` — a granular repackaging of
`dedupClauseVars_nodup` at the CNF level, in the exact shape the switching lemma
hypotheses want.
