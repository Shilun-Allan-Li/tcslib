<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Unconstrained Boolean circuit trees

**Definition.** `Circuit n` is the inductive type of Boolean circuit trees over
`n` variables, with two constructors:

- `lit : Lit n → Circuit n` — a leaf holding a single literal;
- `node : (isAnd : Bool) → List (Circuit n) → Circuit n` — an internal gate with
  an arbitrary-arity list of children, computing AND when `isAnd = true` and OR
  when `isAnd = false`.

It is a *tree*, not a DAG (no sharing), the fan-in is unbounded, and — as the
docstring says — **no alternation or deduplication constraint is imposed**: an
AND gate may sit directly under an AND gate, and a gate may repeat a child.
The type `deriving Repr` only; there is no `DecidableEq`.

One conceptual remark: because `node` recurses through `List (Circuit n)`, this
is a *nested* inductive, and Lean's `induction` tactic does not directly give the
`∀ c ∈ cs, motive c` hypothesis. The file therefore supplies `Circuit.ind`, a
hand-rolled recursor built from `Circuit.rec` with the list motive
`fun cs => ∀ c ∈ cs, motive c`; essentially every subsequent proof about
`Circuit` goes through it.

**Used in.** The whole `BoolCircuit` API: `Circuit.eval`, `Circuit.litCount`,
`Circuit.depth`, `Circuit.size`, `Circuit.maxFanin`, the normalization maps
`Circuit.toNAnd` / `Circuit.toNOr` into the alternating normal forms
`NAndCircuit` / `NOrCircuit`, and downstream the LMN and Razborov–Smolensky
files. `NAndCircuit.toCircuit` / `NOrCircuit.toCircuit` map back into it,
forgetting the normal-form constraints.
