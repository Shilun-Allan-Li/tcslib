<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_path_nil_of_rho_none_and_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A free member literal forces the path to be exhausted

**Claim.** Suppose `(l, idx) ∈ lits`, every literal in `lits` sharing `l`'s
variable equals `l` (`hnd`), `ρ₀ l.var = none`, and yet the encoder still leaves
`l.var` free: `(processClauseLits lits path ρ₀ σ).2.1 l.var = none`. Then the
remaining path is empty: `(processClauseLits lits path ρ₀ σ).1 = []`. Reading it
the other way: the only way `l` escaped being processed is that `path` ran out
first. A `private` helper.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

1. `lits = []`: `hl` is impossible — `absurd hl List.not_mem_nil`.
2. `lits = hd :: tl`, `path = []`: `processClauseLits` returns remaining path `[]`
   outright — `simp [processClauseLits]`.
3. `lits = hd :: tl`, `path = p :: ps`: `simp only [processClauseLits] at h ⊢`,
   then `rcases List.mem_cons.mp hl`.
   - `(l, idx) = hd`: then `hd.1.var = l.var`, so
     `Function.update ρ₀ hd.1.var (some p.2)` is `some p.2` at `l.var`, and
     `processClauseLits_rho_ne_none` contradicts `h` (`exfalso`).
   - `(l, idx) ∈ tl` with `hd.1.var = l.var`: identical
     `processClauseLits_rho_ne_none` contradiction.
   - `(l, idx) ∈ tl` with `hd.1.var ≠ l.var`: apply `ih`; freeness survives the
     update via `Function.update_apply` and `if_neg (Ne.symm heq)`.

**Note.** `hnd` is only threaded into the induction hypothesis and never actually
consumed in any branch, so it is a vestigial hypothesis of the statement.

**Used in.** `encode_go_not_kills_first_clause`.
