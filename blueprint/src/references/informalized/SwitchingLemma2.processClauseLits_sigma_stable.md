<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_sigma_stable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# processClauseLits leaves σ alone off its literal list

**Claim.** Let `lits : List (Literal n × ℕ)`, `path : List (Fin n × Bool)`,
restrictions `ρ₀ σ`, and a variable `v` with `∀ p ∈ lits, p.1.var ≠ v`. Then the
σ-component of the output, `(processClauseLits lits path ρ₀ σ).2.2.1`, agrees
with `σ` at `v`. Granular stability helper: the γ-side restriction is only
modified at variables named by the literal list.

**Proof.** `induction lits generalizing path ρ₀ σ`.

1. `lits = []` — the first defining equation returns `σ` verbatim
   (`simp [processClauseLits]`).
2. `lits = hd :: tl`, `path = []` — the second equation returns `σ` unchanged
   (`simp [processClauseLits]`).
3. `lits = hd :: tl`, `path = p :: ps` — unfold one step
   (`simp only [processClauseLits]`); the recursive call runs on
   `Function.update σ hd.1.var (some (!hd.1.neg))`. Rewrite by `ih`, its
   hypothesis re-derived via `List.mem_cons_of_mem`, leaving
   `Function.update σ hd.1.var (some (!hd.1.neg)) v = σ v`.
4. `hne : hd.1.var ≠ v` from `hv hd List.mem_cons_self` makes the update inert at
   `v` (`Function.update_apply`, `hne.symm`, `ite_false`). ∎

**Used in.** `encode_go_fst_nonfree` (same file): the encoder's γ at a variable
already fixed by `ρ₀` is untouched, since every processed literal is free and so
distinct from `v`. Mirrors `processClauseLits_rho_stable` on the ρ₀ side.
