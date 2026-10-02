<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: toFinBlock_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `toFinBlock` is inverted by forgetting the `Fin` bound

**Claim.** For `w : ℕ`, `l : List (ℕ × Bool)` and a proof `h` that every entry
of `l` has first coordinate `< w`,
`(toFinBlock w l h).map (fun p => (p.1.val, p.2)) = l`. That is, casting the
numeric indices into `Fin w` and then taking `.val` again returns the original
list unchanged.

**Proof.** Granular round-trip helper; `induction l`.

1. `nil`: `rfl`.
2. `cons`: `obtain ⟨idx, dir⟩ := hd`, then `simp [toFinBlock, ih]` — the head
   becomes `(⟨idx, _⟩, dir)` whose `.val` is `idx` by definition of `Fin.val`,
   and the tail is handled by the induction hypothesis.

**Used in.** `encode_go_wellformed` (private, same file): after
`triplesToAux_markLast` rewrites the marked block into
`block.map (fun p => (p.1.val, p.2)) ++ [(w, false)]`, this lemma turns that map
back into the raw aux list produced by `processClauseLits`.
