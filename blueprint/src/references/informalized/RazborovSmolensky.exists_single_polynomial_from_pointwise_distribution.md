<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: exists_single_polynomial_from_pointwise_distribution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# From a seeded polynomial family to one polynomial with a global error bound

**Claim.** Let `Seed` be a nonempty finite type, `P : Seed → MvPolynomial (Fin n) (ZMod p)`
a family, `f : (Fin n → Fin 2) → ZMod p` a target, and `ℓ B : ℕ`. Suppose that at
every Boolean point `x` the number of seeds on which the family errs satisfies

`#{s | (P s).eval (boolInput p x) ≠ f x} * 2 ^ ℓ ≤ B * Fintype.card Seed`.

Then some seed `s` satisfies `badInputCount p f (P s) * 2 ^ ℓ ≤ B * 2 ^ n`.

**Proof.** Two steps.

1. Set `Fail x s := (P s).eval (boolInput p x) ≠ f x` (a `let`) and apply
   `exists_good_parameter_of_pointwise_bound` with `α := Fin n → Fin 2`,
   `β := Seed`, `C := 2 ^ ℓ`, `B := B`; the hypothesis is exactly `hpoint`. This
   returns a seed `s` with `#{x | Fail x s} * 2 ^ ℓ ≤ B * Fintype.card (Fin n → Fin 2)`.
2. `simpa [Fail, badInputCount, Fintype.card_fun]` converts the filtered
   cardinality into `badInputCount` and rewrites `Fintype.card (Fin n → Fin 2)`
   as `2 ^ n`.

**Remark.** This is the specialization of the general averaging lemma in which
the point index is the Boolean cube, so the "number of points" factor becomes the
explicit `2 ^ n`.
