<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: cnfToDualDNF_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Variable-injectivity of clauses transfers to the De Morgan dual

**Claim.** Let `ψ : CNF n` be such that within every clause, two literals with
the same variable are equal (`∀ c ∈ ψ, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂`).
Then the same holds for every term of the dual DNF
`cnfToDualDNF ψ = ψ.map (fun c => c.map Literal.flipNeg)`.

**Proof.** Transport along the polarity flip.

1. Introduce `t ∈ cnfToDualDNF ψ` and `l₁, l₂ ∈ t` with `l₁.var = l₂.var`;
   `simp only [cnfToDualDNF, List.mem_map]` and `obtain ⟨c, hc_mem, rfl⟩` present
   `t` as `c.map Literal.flipNeg` for some clause `c ∈ ψ`.
2. Likewise `l₁ = l₁'.flipNeg` and `l₂ = l₂'.flipNeg` for literals
   `l₁', l₂' ∈ c` (`List.mem_map`, twice).
3. `Literal.flipNeg_var` says flipping polarity preserves the variable, so the
   hypothesis becomes `l₁'.var = l₂'.var`; applying `h c hc_mem` gives
   `l₁' = l₂'`, and `rw [this]` closes the goal since `flipNeg` is a function.

**Used in.** `switching_lemma_cnf`, which discharges the DNF switching lemma's
per-clause hypotheses via `cnfToDualDNF_inj ψ hnd` and `cnfToDualDNF_nodup`; also
in `TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli.lean` (line 200).
