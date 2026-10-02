<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_rho_stable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# processClauseLits leaves ρ₀ alone off its literal list

**Claim.** Let `lits : List (Literal n × ℕ)`, `path : List (Fin n × Bool)`,
restrictions `ρ₀ σ`, and a variable `v` with `∀ p ∈ lits, p.1.var ≠ v`. Then the
ρ₀-component of the output, `(processClauseLits lits path ρ₀ σ).2.1`, agrees with
`ρ₀` at `v`. A granular stability helper: `processClauseLits` only touches
variables named by its literal list.

**Proof.** `induction lits generalizing path ρ₀ σ`.

1. `lits = []` — the first defining equation returns `ρ₀` verbatim
   (`simp [processClauseLits]`).
2. `lits = hd :: tl`, `path = []` — the second equation also returns `ρ₀`
   unchanged (`simp [processClauseLits]`).
3. `lits = hd :: tl`, `path = p :: ps` — unfold one step
   (`simp only [processClauseLits]`); the recursive call runs on
   `Function.update ρ₀ hd.1.var (some p.2)`. Rewrite by `ih`, whose hypothesis is
   re-derived via `List.mem_cons_of_mem`, leaving
   `Function.update ρ₀ hd.1.var (some p.2) v = ρ₀ v`.
4. `hne : hd.1.var ≠ v` comes from `hv hd List.mem_cons_self`, so the update is
   inert at `v` (`Function.update_apply`, `hne.symm`, `ite_false`). ∎

**Used in.** `roundtrip_inv_hD'` (`Switching/RoundTrip.lean`), to show the
decoder's ρ₀ fold matches the encoder's ρ₀ at variables no clause literal names.
Its σ-side twin is `processClauseLits_sigma_stable`, with a character-identical
proof.
