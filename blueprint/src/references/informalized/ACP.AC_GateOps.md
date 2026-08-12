<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: AC_GateOps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The `AC⁰` gate set

**Definition.** `AC_GateOps : Set (GateOp (Fin 2))` is

`{GateOp.id (Fin 2), ⟨Fin 1, fun x => 1 - x 0⟩} ∪ ⋃ n, {⟨Fin n, fun x => ∏ i, x i⟩}`,

i.e. the identity gate, the NOT gate, and — one for each fan-in `n` — the
unbounded AND gate. A plain definition; no proof.

**Reading the encoding.** A `GateOp α` bundles its own arity: it is a pair
`(ι : Type, func : (ι → α) → α)`. So `⟨Fin 1, fun x => 1 - x 0⟩` is the arity-1
gate computing `1 - x`, and the `⋃ n` is what makes AND *unbounded* fan-in rather
than one fixed width. Gate values live in `Fin 2` with its ring structure, where
`1 - ·` is negation and `∏` is AND (a product of bits is `1` exactly when every
bit is).

**Remark.** There is deliberately no OR gate: OR is obtained by De Morgan from NOT
and AND, which is also how the polynomial approximators are built downstream
(`approxAnd = 1 - approxOr (1 - ·)`). Despite the file's ambient
`variable (p : ℕ) [Fact (Nat.Prime p)]`, this definition never mentions `p` and
so takes no prime argument.

**Used in.** `ACp_GateOps` (which adjoins the `MOD p` gates) and the unfolding
inside `ACp_GateOps_cases`, both in the same file. It has no consumers elsewhere
in the repository — downstream files always speak of `ACp_GateOps p`.
