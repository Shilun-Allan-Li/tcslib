<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: ACp_GateOps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The `AC⁰[p]` gate set

**Definition.** For a prime `p`,

`ACp_GateOps p = AC_GateOps ∪ ⋃ n, {modGateOp p n}`.

That is: the `AC⁰` gates (identity, NOT, unbounded AND) together with an unbounded
`MOD p` gate for every fan-in `n`. A plain definition; no proof.

**The `MOD p` gate.** `modGateOp p width` has input type `Fin width` and computes
`if (∑ i, ((x i : ℕ) : ZMod p)) = 0 then 1 else 0` — it casts its `Fin 2` inputs
into `ZMod p`, sums them, and outputs `1` exactly when the number of `1`-inputs is
divisible by `p`. The `⋃ n` again supplies every fan-in.

**Why it matters.** This is the gate basis for which Razborov–Smolensky proves a
lower bound: every gate in the set admits a low-degree `ZMod p` polynomial
approximation (`MOD p` and NOT exactly, AND with a small failure probability), and
that is exactly what `ACp_GateOps_cases` sets up the case analysis for.

**Used in.** The `F.onlyUsesGates (ACp_GateOps p)` hypothesis throughout the
Razborov–Smolensky development — `RazborovSmolensky.lean:1210`,
`RazborovSmolensky/CircuitSize.lean` (three lemmas), and
`RazborovSmolensky/CircuitDegree.lean:330` (`exists_gate_poly_family`).
