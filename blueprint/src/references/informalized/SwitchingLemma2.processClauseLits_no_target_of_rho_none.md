<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_no_target_of_rho_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# If v stays free, no literal mentioned v

**Claim.** Suppose `ρ₀ v = none`, the encoder leaves it free
(`(processClauseLits lits path ρ₀ σ).2.1 v = none`), and there is at least one
path step per literal (`lits.length ≤ path.length`). Then no literal in `lits`
has variable `v`: `∀ p ∈ lits, p.1.var ≠ v`. This is the converse direction of
`processClauseLits_rho_stable`.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

1. `lits = []`: no members — `intro p hp; simp at hp`.
2. `lits = hd :: tl`, `path = []`: `hlen` is `_ + 1 ≤ 0`, killed by `simp at hlen`.
3. `lits = hd :: tl`, `path = step :: rest`: unfold `hnone` with
   `simp only [processClauseLits]` and `rcases List.mem_cons.mp hp`.
   - `p = hd` and (for contradiction) `p.1.var = v`: then
     `Function.update ρ₀ p.1.var (some step.2)` is `some step.2` at `v`
     (`Function.update_apply`, `if_pos`, `Option.some_ne_none`), so
     `processClauseLits_rho_ne_none` contradicts `hnone`.
   - `p ∈ tl`: `by_cases heq : hd.1.var = v`. If equal, the same
     `processClauseLits_rho_ne_none` contradiction applies. Otherwise the update
     leaves `ρ₀ v = none` (`if_neg (Ne.symm heq)`), and `ih` applies at `rest`
     with the length bound shifted by `omega`.

**Note.** No current consumers in the library; the length hypothesis is what
makes it non-vacuous (without it, `processClauseLits` may stop early and leave
`v` free even though some literal names it).
