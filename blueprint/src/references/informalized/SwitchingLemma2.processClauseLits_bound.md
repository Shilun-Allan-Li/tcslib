<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# processClauseLits emits at most two aux entries per path step

**Claim.** For any literal-with-index list `lits`, any decision-tree path
`path`, and any restrictions `ρ₀`, `σ`, the output of
`processClauseLits lits path ρ₀ σ` satisfies

```
aux.length + 2 * remainingPath.length ≤ 2 * path.length
```

where `aux = pcl.2.2.2` and `remainingPath = pcl.1`. A `private` bookkeeping
lemma; it is the length budget behind the encoder's `2 * d` output bound.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

1. `lits = []`: `processClauseLits` returns `(path, ρ₀, σ, [])`, so the claim is
   `2 * path.length ≤ 2 * path.length` — `simp [processClauseLits]`.
2. `lits = hd :: tl`, `path = []`: the second defining equation returns
   `([], ρ₀, σ, [])` — `simp [processClauseLits]`.
3. `lits = hd :: tl`, `path = p :: ps`: after
   `simp only [processClauseLits, List.length_cons]` the goal is about the
   recursive call on `tl`, `ps` with `ρ₀`, `σ` updated at `hd.1.var`. Instantiate
   the induction hypothesis `ih ps (Function.update ρ₀ …) (Function.update σ …)`;
   one path step is consumed (worth `2`) while `aux` grows by one entry, so
   `omega` closes the arithmetic.

**Used in.** `processClauseLits_tight`, which sharpens it by `1` for non-empty
inputs and feeds `encode_go_aux_length_bound` and hence
`razborovEncode_aux_length_le`.
