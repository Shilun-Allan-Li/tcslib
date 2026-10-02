<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: LowDegreeBadCountLB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Packaged lower bound on low-degree approximation error

**Definition.** For a prime `p`, a target `f : (Fin n → Fin 2) → ZMod p`, and naturals `d E`,
`LowDegreeBadCountLB p f d E` is the proposition

`∀ P : MvPolynomial (Fin n) (ZMod p), P.totalDegree ≤ d → E ≤ badInputCount p f P`

i.e. every polynomial over `ZMod p` of total degree at most `d` disagrees with `f` on at least
`E` of the `2 ^ n` Boolean inputs, where `badInputCount p f P` counts
`x : Fin n → Fin 2` with `P.eval (boolInput p x) ≠ f x`.

**Remark.** A `Prop`-valued abbreviation, not a theorem: it is the interface through which the
Smolensky degree lower bound is fed into the circuit-size argument. Note the direction — `E`
is a *lower* bound on the error count, so larger `E` is a stronger hypothesis.

**Used in.** `size_lower_bound_from_badCountLB` (yields `E * 2 ^ ℓ ≤ F.size * 2 ^ n` for any
`AC⁰[p]` circuit `F` computing `MOD q`) and its relative-error form
`size_lower_bound_from_relative_badCountLB` (with `E := δ * 2 ^ n`, yielding
`δ * 2 ^ ℓ ≤ F.size`).
