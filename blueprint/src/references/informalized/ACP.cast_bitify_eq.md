<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: cast_bitify_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `bitify` is a section of the bit inclusion on `{0,1}`

**Claim.** For prime `p` and `a : ZMod p` with `a ∈ ({0, 1} : Set (ZMod p))`, pushing `a`
through `bitify` and back is the identity: `((bitify p a : ℕ) : ZMod p) = a`.

**Proof.**

1. `simp [bitify] at ha ⊢` unfolds the definition and turns the set membership `ha` into
   the disjunction `a = 0 ∨ a = 1`.
2. `rcases ha with rfl | rfl` substitutes each value in turn.
3. Both branches close by `simp`: for `a = 0` the `if` takes the `else` branch and
   `((0 : Fin 2) : ℕ) = 0`; for `a = 1` it takes the `then` branch and
   `((1 : Fin 2) : ℕ) = 1`.

**Remark.** A granular helper. The `have hp1 : 1 < p` extracted from
`Fact (Nat.Prime p)` at the top of the proof is not needed by either `simp` call — the
sibling lemma `bit_indicator_eq_bitify` is the one that actually uses it (via `omega`).
Nothing about `p` being prime matters for this statement.
