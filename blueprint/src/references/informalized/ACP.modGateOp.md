<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: modGateOp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The unbounded `MOD p` gate

**Definition.** `modGateOp p width : GateOp (Fin 2)` is the gate with arity type
`ι := Fin width` and output

`func x = if (∑ i, ((x i : ℕ) : ZMod p)) = 0 then 1 else 0`.

That is: cast each Boolean input into `ZMod p`, add them up, and output `1` exactly when
the number of `1`s among `x 0, …, x (width-1)` is divisible by `p`, and `0` otherwise.

**Remark.** This is the "`= 0 mod p`" convention (output `1` on a zero residue), the
complement of the more common `MOD p` convention that accepts on a *nonzero* residue.
The polynomial that matches it exactly is `exactMod`, whose Fermat indicator
`1 - (∑ i, polys i) ^ (p - 1)` has the same `1`-on-zero-sum behaviour; the two are
identified by `exactMod_on_bits`.

**Used in.** `ACp_GateOps` (as the fourth gate family, `⋃ n, {modGateOp p n}`), the
`MOD` branch of `exists_poly_for_gate`, and downstream in
`RazborovSmolensky/CircuitDegree.lean` and `RazborovSmolensky/SmolenskyAlgebra.lean`.
