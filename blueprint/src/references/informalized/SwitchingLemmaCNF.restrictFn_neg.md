<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: restrictFn_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restriction commutes with negation

**Claim.** For `f : (Fin n → Bool) → Bool` and a restriction `ρ : Restriction n`,
restricting the pointwise negation of `f` gives the pointwise negation of the
restriction: `restrictFn (fun x => !(f x)) ρ = fun x => !(restrictFn f ρ x)`.

**Proof.** Immediate from the definition: `restrictFn f ρ = fun x => f (ρ.extend x)`,
so both sides send `x` to `!(f (ρ.extend x))`. The Lean proof is the one-liner
`ext x; simp [restrictFn]`.

**Used in.** `IsBadRestriction_neg` (together with `dtDepth_neg`), which is what
lets `switching_lemma_cnf` rewrite a bad-restriction condition for `ψ.eval` into
one for the dual DNF `(cnfToDualDNF ψ).eval`.
