<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: exactMod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The exact `MOD p` polynomial

**Definition.** Given `polys : Fin width → MvPolynomial (Fin vars) (ZMod p)`,

`exactMod p polys := 1 - (∑ i, polys i) ^ (p - 1)`.

By Fermat's little theorem in `ZMod p`, this evaluates to `1` when `∑ i, polys i`
evaluates to `0` and to `0` otherwise (the lemma `one_sub_pow_card_sub_one` in the same
file). It is `noncomputable` only because `MvPolynomial` arithmetic is.

**Remark.** Unlike `approxOr` / `approxAnd`, this needs no randomness: `MOD p` is
*exactly* computed by a single polynomial, and the price is only a factor `p - 1` in
degree (`exactMod_totalDegree`). This is the reason `AC⁰[p]` circuits admit low-degree
approximations at all — only the AND/OR gates require the probabilistic step.

**Used in.** The `MOD` branch of `exists_poly_for_gate`, matched to the gate semantics by
`exactMod_on_bits`, and in `RazborovSmolensky/CircuitDegree.lean` as the `poly` field of
the `MOD` gate's approximator record.
