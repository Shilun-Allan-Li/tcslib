<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: depth3_restricted_has_nice_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# After stage 1, the restricted depth-3 function is a nice width-`l` CNF

**Claim.** Let `f : (Fin n → Bool) → Bool` be the AND of `s₂` DNF gates
`gates : Fin s₂ → DNF n`, in the sense `∀ x, f x = true ↔ ∀ i, (gates i).eval x = true`,
and let `ρ₁ : Restriction n` be a restriction under which every gate has already
switched: `dtDepth (restrictFn (gates i).eval ρ₁) ≤ l` for all `i`. Then there is
a `Ψ : CNF n` with `CNF.width Ψ ≤ l`, all clauses `Nodup` and variable-injective,
and `∀ x, CNF.eval Ψ x = restrictFn f ρ₁ x`.

**Proof.**

1. `obtain ⟨Ψ, hΨ⟩ := and_of_gates_has_cnf s₂ gates l ρ₁ h_gates` — each
   restricted gate has a width-`l` CNF, and the AND of CNFs is again a CNF of the
   same width (concatenation of clause lists), so `Ψ` is a nice width-`l` CNF
   whose value at `x` is `List.all` of the restricted gate values over
   `Finset.univ`.
2. `use Ψ`; the width bound and the two clause conditions are literally
   `hΨ.1`, `hΨ.2.1`, `hΨ.2.2.1`, leaving only the evaluation identity
   (`refine' ⟨hΨ.2.2.1, fun x => _⟩`).
3. For that identity, `simp +decide [restrictFn]` turns `restrictFn f ρ₁ x` into
   `f (ρ₁.extend x)`, and `cases h : f (ρ₁.extend x)` splits on its value: by
   `h_f` at `ρ₁.extend x`, `f (ρ₁.extend x) = true` exactly when every
   `restrictFn (gates i).eval ρ₁ x` is `true`, which is what the `List.all` in
   step 1 computes. `simp_all +decide` and `grind` close both branches.

**Used in.** `depth3_second_stage_bound`, which feeds this CNF (after
`cleanCNF_D3`) into `switching_bernoulli_dtDepth_cnf` for the second Bernoulli
stage of `depth3_switching_bound`.
