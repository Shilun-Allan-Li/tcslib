<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: triplesToAux_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `triplesToAux` distributes over append

**Claim.** For `w : ℕ` and triple lists `ts₁ ts₂ : List (Fin w × Bool × Bool)`,
`triplesToAux w (ts₁ ++ ts₂) = triplesToAux w ts₁ ++ triplesToAux w ts₂`.
`triplesToAux` is the private decoder-side serialiser sending
`(pos, dir, true)` to `(pos.val, dir) :: (w, false) :: …` (entry plus
termination marker) and `(pos, dir, false)` to `(pos.val, dir) :: …`.

**Proof.** `induction ts₁`, since `triplesToAux` recurses on its first argument.

1. `nil`: `simp [triplesToAux]`.
2. `cons`: `obtain ⟨pos, dir, mark⟩ := hd` and `cases mark`. In both the `true`
   and `false` branches a `show` restates the goal in the head-normal form that
   matches a `triplesToAux` equation, and `simp [triplesToAux, ih]` closes it —
   each head emits the same one or two entries regardless of what follows it.

**Used in.** `encode_go_wellformed` (private, same file), which decomposes the
encoder's aux output as `markLast block ++ ts_rec` and needs the serialisation
to split at that seam.
