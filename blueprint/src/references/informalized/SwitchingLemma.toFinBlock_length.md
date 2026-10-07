<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: toFinBlock_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `toFinBlock` preserves length

**Claim.** For `w : ℕ`, a list `l : List (ℕ × Bool)` and a proof `h` that every
entry of `l` has first coordinate `< w`, the cast list `toFinBlock w l h` has
`(toFinBlock w l h).length = l.length`. Here `toFinBlock` is the private
recursive cast of `l` into `List (Fin w × Bool)`, replacing each `idx` by
`⟨idx, h …⟩`.

**Proof.** Granular bookkeeping helper; `induction l`.

1. `nil`: both sides are `0` — closed by `rfl`.
2. `cons`: destructure the head with `obtain ⟨idx, dir⟩ := hd`, then
   `simp [toFinBlock, ih]` — the cast prepends exactly one element, matching
   `List.length_cons`.

**Used in.** `encode_go_wellformed` (private, same file), where the aux block
emitted by `processClauseLits` is cast into `List (Fin w × Bool)` and its length
must still be charged against the path length via `markLast_length`.
