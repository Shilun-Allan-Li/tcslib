<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: badInputCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Number of Boolean inputs where a polynomial misses its target

**Definition.** Fix a prime `p`, a target `f : (Fin n → Fin 2) → ZMod p`, and a
polynomial `P : MvPolynomial (Fin n) (ZMod p)`. Then `badInputCount p f P` is the
cardinality of

`Finset.univ.filter (fun x : Fin n → Fin 2 => P.eval (boolInput p x) ≠ f x)`,

i.e. the number of points of the Boolean cube `{0,1}^n` at which `P`, evaluated
on the field embedding `boolInput` of the bit vector, disagrees with `f`. The
error is counted absolutely, not as a fraction, so all downstream bounds are
stated as `badInputCount ... * 2 ^ ℓ ≤ B * 2 ^ n`.

**Remark.** The body is written in tactic mode only to insert `classical` before
the `Finset.filter`, which needs decidability of the disagreement predicate; the
definition is therefore `noncomputable` and does not reduce by `rfl`. Unfolding it
in proofs is done with `simp [badInputCount]`.

**Used in.** `LowDegreeBadCountLB`, `exists_single_polynomial_from_pointwise_distribution`,
`exists_single_poly_for_circuit_one_size`, and the two
`size_lower_bound_from_*badCountLB` theorems.
