<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Encoding.lean :: razborovEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Razborov encoding of a restriction

**Definition.** `razborovEncode f w d ρ` maps a restriction `ρ : Restriction n`
(i.e. `Fin n → Option Bool`) to a pair `(γ, aux) : Restriction n × List (ℕ × Bool)`,
where `γ` extends `ρ` by fixing `d` further variables and `aux` is a list of
`(literal index, path direction)` entries with clause blocks separated by
termination markers `(w, false)`. It is `noncomputable` (it uses `Classical`
decidability of `Term.killedBy`).

The construction:

1. Take `path := (canonicalDTree f ρ).deepPath.take d` — the first `d` steps of
   the deepest root-to-leaf path of the canonical decision tree of `f|ρ`
   (`DecisionTree.deepPath` breaks ties toward the `true` branch).
2. Run the inner loop `razborovEncode.go f w (path.length + 1) path ρ ρ []`,
   which carries two restrictions: `ρ₀`, following the *path* directions (so it
   tracks canonical-DT branching), and `σ`, following the *satisfying*
   directions (this is the returned `γ`). Both start at `ρ`; the accumulator
   starts empty and `path.length + 1` is the fuel.
3. Each iteration picks the first clause not yet killed by `ρ₀`
   (`f.find? (fun t => decide (¬Term.killedBy t ρ₀))`), keeps the literals of
   that clause whose variable is still free in `ρ₀` (`List.zipIdx` + `filter`
   on `Restriction.freeVars`), and hands them to `processClauseLits` together
   with the remaining path. That helper consumes one path entry per free
   literal, setting `ρ₀ l.var := some dir` and `σ l.var := some (!l.neg)`, and
   emitting `(idx, dir)` for the literal's position `idx` in the clause.
4. The clause's aux entries are appended, followed by the marker `(w, false)`,
   and the loop recurses on the leftover path with the updated `ρ₀`, `σ`.
   It stops when the path is exhausted, the fuel runs out, no unkilled clause
   exists, or the chosen clause has no free literals — returning `(σ, acc)` in
   every case.

**Remark.** Since `w` is intended as an upper bound on the clause width, an
index `≥ w` cannot be a real literal position, which is what lets the decoder
`razborovDecode` read `(w, false)` as an unambiguous end-of-clause marker.

**Used in.** `razborovDecode` / `go_roundtrip_gen` (the encoding is inverted
there) and the bad-restriction counting argument in
`TCSlib/BooleanAnalysis/Switching.lean`, where injectivity of
`ρ ↦ (razborovEncode f w d ρ).2` on bad restrictions
(`razborovEncode_injective`) yields the `(4 * w) ^ d` bound.
