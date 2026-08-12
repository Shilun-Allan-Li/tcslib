<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: exists_single_poly_for_circuit_one_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# One low-degree polynomial approximating an `AC⁰[p]` circuit

**Claim.** Let `F : FeedForward (Fin 2) (Fin n) out` be a circuit with finite node
types, a unique output, and only `ACp_GateOps p` gates, and let `ℓ : ℕ`. Then
there is a single polynomial `P : MvPolynomial (Fin n) (ZMod p)` with

`P.totalDegree ≤ circuitDegreeBound p ℓ F.depth`  and
`badInputCount p (fun x => ((F.eval₁ x : Fin 2) : ℕ) : ZMod p) P * 2 ^ ℓ ≤ F.size * 2 ^ n`.

That is, the pointwise/randomized approximation guarantee is upgraded to one
concrete polynomial whose total error over `{0,1}^n` is at most `F.size / 2 ^ ℓ`
of the cube.

**Proof.** Three steps.

1. `exists_poly_distribution_for_circuit_one_size p F hUses ℓ` supplies a seed
   type `Seed` with a `Fintype` instance `instF`, positive cardinality `hpos`, a
   family `P`, a uniform degree bound `hdeg`, and the pointwise error bound
   `hbad`.
2. Register the instances with `letI`: `Fintype Seed := instF` and
   `Nonempty Seed := Fintype.card_pos_iff.mp hpos`.
3. Apply `exists_single_polynomial_from_pointwise_distribution` with `B := F.size`
   and target `fun x => ((F.eval₁ x : Fin 2) : ℕ) : ZMod p` to get a seed `s`, and
   return `⟨P s, hdeg s, hs⟩`.

**Used in.** `size_lower_bound_from_badCountLB`, where it is combined with a
low-degree lower bound for `MOD q`.
