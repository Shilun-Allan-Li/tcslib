<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: toFinBlock_ne_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `toFinBlock` of a nonempty list is nonempty

**Claim.** For `w : ℕ`, `l : List (ℕ × Bool)`, a proof `h` that every entry of
`l` has first coordinate `< w`, and `hne : l ≠ []`, the cast list
`toFinBlock w l h` is also `≠ []`.

**Proof.** One-step case analysis on `l`.

1. `nil`: contradicts `hne` — `exact absurd rfl hne`.
2. `cons`: `obtain ⟨idx, dir⟩ := hd`, then `simp [toFinBlock]`, since
   `toFinBlock` on a cons is syntactically a cons.

**Used in.** `encode_go_wellformed` (private, same file), to supply the
nonemptiness hypothesis that `triplesToAux_markLast` requires for the block
`toFinBlock w pcl.2.2.2 hpcl_idx_lt`.
