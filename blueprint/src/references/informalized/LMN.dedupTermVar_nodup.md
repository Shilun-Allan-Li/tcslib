<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: dedupTermVar_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# De-duplicating a term by variable leaves no repeated literal

**Claim.** For every term `t : Term n`, the list `dedupTermVar t` is `Nodup`.
Here `dedupTermVar` is the `foldr` that keeps a literal only when the
already-accumulated tail contains no literal with the same `var`.

**Proof.** A one-step generalisation of the goal over the accumulator.

1. Prove the invariant
   `∀ t acc, acc.Nodup → (t.foldr (fun l acc => if acc.any (·.var = l.var) then acc else l :: acc) acc).Nodup`
   by `induction t <;> aesop` (`h_ind`): in the `cons` case either the `if`
   returns `acc` unchanged, or it prepends `l`, and the guard being false says
   no element of `acc` shares `l.var`, hence in particular `l ∉ acc`.
2. Instantiate `h_ind` at `acc = []`, whose `Nodup` is `by simp +decide`.

**Used in.** `cleanDNF_nodup` and `cleanCNF_nodup`, which supply the `Nodup`
hypothesis of the switching lemma for cleaned formulas.
