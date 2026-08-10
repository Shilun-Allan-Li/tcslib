<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: cnfToDualDNF_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The De Morgan dual has the same width

**Claim.** For any `ψ : CNF n`, the dual DNF has the same width as `ψ`:
`(cnfToDualDNF ψ).width = ψ.width`. Here width is the maximum clause/term length
(`DNF.width`, `CNF.width` are both `(·.map Term.width).foldr max 0`), and
`cnfToDualDNF ψ = ψ.map (fun c => c.map Literal.flipNeg)`.

**Proof.**

1. Unfold `cnfToDualDNF`, `DNF.width`, `CNF.width`, `Term.width` and collapse the
   two maps with `List.map_map`, `Function.comp_def`, `List.length_map`
   (a single `simp only`). Mapping `Literal.flipNeg` over a clause does not change
   its length, so both sides become the same `foldr max 0` over the same list of
   lengths.
2. `congr 1` closes the remaining syntactic difference. ∎

**Used in.** `switching_lemma_cnf`, to carry the width bound `ψ.width ≤ w` across
to `(cnfToDualDNF ψ).width ≤ w` before applying the DNF `switching_lemma`.
