<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Encoding.lean :: processClauseLits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Matching one clause's free literals against the canonical DT path

**Definition.** `processClauseLits` is the inner loop of the Razborov encoding.
It is a `noncomputable` recursion of type
`List (Literal n × ℕ) → List (Fin n × Bool) → Restriction n → Restriction n →
List (Fin n × Bool) × Restriction n × Restriction n × List (ℕ × Bool)`,
consuming a list of indexed literals (one clause's free literals, paired with
their positions in the clause) against a list of path steps, while threading two
restrictions `ρ₀` and `σ`. The output is
`(remaining_path, updated ρ₀, updated σ, clause_aux)`.

Three defining equations:

1. `[], path, ρ₀, σ ↦ (path, ρ₀, σ, [])` — no literals left: the path is handed
   back untouched and no aux data is emitted.
2. `_, [], ρ₀, σ ↦ ([], ρ₀, σ, [])` — path exhausted: any literals still
   unprocessed are silently dropped, and the remaining path is `[]`.
3. `(l, idx) :: restLits, (_, dir) :: restPath, ρ₀, σ ↦` recurse on both tails
   with `ρ₀` replaced by `Function.update ρ₀ l.var (some dir)` and `σ` by
   `Function.update σ l.var (some (!l.neg))`, then return the recursive call's
   first three components with `(idx, dir)` consed onto its aux list.

Note that in the third equation the path entry's own variable is discarded
(`(_, dir)`): only its direction bit is consumed, and the variable actually
fixed is the literal's `l.var`. The two restrictions play different roles —
`ρ₀` is fixed to the *path* direction `dir`, simulating the branching of the
canonical decision tree, whereas `σ` (which becomes `γ`) is fixed to the
literal's *satisfying* direction `!l.neg`, i.e. so that `Literal.fixedBy l σ`
holds. The aux entry `(idx, dir)` is exactly the pair the decoder replays.

**Used in.** `razborovEncode.go` (same file), which calls it once per non-killed
clause and appends the returned aux block followed by a terminator `(w, false)`;
its metatheory (length bounds, ρ₀/σ stability, σ-independence) lives in
`Switching/EncodingProperties.lean`, and `razborovDecode.processEntries` is the
inverse consumer.
