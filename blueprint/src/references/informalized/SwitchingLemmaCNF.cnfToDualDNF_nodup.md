<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: cnfToDualDNF_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Duplicate-freeness transfers to the De Morgan dual

**Claim.** If every clause `c` of a CNF `ψ : CNF n` is duplicate-free (`c.Nodup`),
then every term `t` of the dual DNF `cnfToDualDNF ψ` is duplicate-free. Since
`cnfToDualDNF ψ = ψ.map (fun c => c.map Literal.flipNeg)`, this is the statement
that mapping `Literal.flipNeg` over a clause preserves `Nodup`.

**Proof.**

1. Fix `t ∈ cnfToDualDNF ψ`. Unfolding `cnfToDualDNF` and using
   `List.mem_map` gives a clause `c ∈ ψ` with `t = c.map Literal.flipNeg`
   (`obtain ⟨c, hc_mem, rfl⟩`).
2. `h c hc_mem : c.Nodup`, and `Literal.flipNeg` is injective
   (`Literal.flipNeg_injective`), so `List.Nodup.map` yields
   `(c.map Literal.flipNeg).Nodup`. ∎

**Used in.** `switching_lemma_cnf`, to convert the CNF's `hnodup` hypothesis into
the `Nodup` side condition required by the DNF-side `switching_lemma`.
