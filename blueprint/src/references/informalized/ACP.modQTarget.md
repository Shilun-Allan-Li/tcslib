<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: modQTarget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `MOD q` as a target function valued in `ZMod p`

**Definition.** For primes `p`, `q` and `x : Fin n → Fin 2`,

`modQTarget p x = (((modGateOp q n).func x : Fin 2) : Nat) : ZMod p`,

i.e. apply the unbounded `MOD q` gate to the Boolean input `x` — which returns `1`
when `∑ i, x i ≡ 0 (mod q)` and `0` otherwise — and then cast that single bit into
`ZMod p`.

**Remark.** The only content here is the change of ambient ring: `modGateOp` is
`Fin 2`-valued, while polynomial approximation happens over `ZMod p`. Note the two
primes play different roles — `q` is the modulus of the gate, `p` the characteristic
of the polynomial ring, and the lower bound is interesting precisely when `p ≠ q`.

**Used in.** The `LowDegreeBadCountLB` hypothesis of
`size_lower_bound_from_badCountLB` and `size_lower_bound_from_relative_badCountLB`
(where `unfold modQTarget` plus `hCompute` identifies it with the circuit's output),
and in `RazborovSmolensky.lean` via
`paddedResidueInput_modQTarget_eq_residueIndicator`.
