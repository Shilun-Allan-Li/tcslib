<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_rho_ne_none_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A member literal's variable gets fixed, given enough path

**Claim.** If some `p ∈ lits` has `p.1.var = v`, and there are at least as many
path steps as literals (`lits.length ≤ path.length`), then
`(processClauseLits lits path ρ₀ σ).2.1 v ≠ none` — the encoder's simulated
restriction fixes `v`. The length hypothesis is essential: without it
`processClauseLits` can stop before reaching `p`.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

1. `lits = []`: `hp` is impossible — `simp at hp`.
2. `lits = hd :: tl`, `path = []`: `hlen` reads `_ + 1 ≤ 0` — `simp at hlen`.
3. `lits = hd :: tl`, `path = step :: rest`: `simp only [processClauseLits]`, then
   `rcases List.mem_cons.mp hp`.
   - `p = hd`: the recursive call starts from
     `Function.update ρ₀ p.1.var (some step.2)`, which is `some step.2` at `v` by
     `Function.update_apply`, `if_pos hpv.symm`, `Option.some_ne_none`; so
     `processClauseLits_rho_ne_none` gives the conclusion.
   - `p ∈ tl`: apply `ih` at `rest`, with the length bound shifted by
     `simp [List.length_cons] … ; omega`.

**Note.** No current consumers in the library; it is the positive counterpart of
`processClauseLits_no_target_of_rho_none`.
