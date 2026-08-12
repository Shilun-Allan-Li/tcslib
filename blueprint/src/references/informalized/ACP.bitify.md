<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: bitify -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Booleanization of a field element

**Definition.** `bitify p a : Fin 2` sends `a : ZMod p` to `1` if `a = 1` and to `0`
otherwise. It is the one-sided inverse of the inclusion `Fin 2 → ZMod p`, `b ↦ (b : ℕ)`,
and is decidable because equality in `ZMod p` is.

**Remark.** The `else` branch collapses *everything* other than `1` to `0`, not just `0`.
So `bitify` is only faithful on the two-element set `{0, 1} ⊆ ZMod p`; the docstring says
as much ("Use only on values in `{0,1}`"), and every downstream lemma that inverts it
(`cast_bitify_eq`, `exactMod_on_bits`, `exactAnd_on_bits`) carries an explicit
`inputs i ∈ ({0, 1} : Set (ZMod p))` hypothesis.

**Used in.** The correctness side of the polynomial-approximation lemmas, where a gate
`op : GateOp (Fin 2)` must be fed `Fin 2`-valued arguments obtained from `ZMod p`-valued
polynomial evaluations: `op.func (fun i ↦ bitify p (inputs i))`. Also used in
`RazborovSmolensky/CircuitDegree.lean` (e.g. `bitify_boolVal`).
