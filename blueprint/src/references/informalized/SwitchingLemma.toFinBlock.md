<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: toFinBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Casting a bounded index list into `Fin w` positions

**Definition.** `toFinBlock w` takes a list `l : List (ℕ × Bool)` together with
a proof `h : ∀ e ∈ l, e.1 < w` and returns the corresponding
`List (Fin w × Bool)`, by recursion on `l`: the empty list gives the empty
list, and `(idx, dir) :: rest` gives `(⟨idx, h _ List.mem_cons_self⟩, dir)`
consed onto `toFinBlock w rest h'`, where `h'` is `h` weakened along
`List.mem_cons_of_mem`. The membership proof is therefore threaded through the
recursion and consumed to build each `Fin w`; the definition is a proof-carrying
cast and does nothing else to the data.

**Used in.** Its three companion lemmas record that the cast is faithful:
`toFinBlock_length` (length preserved), `toFinBlock_map` (mapping
`fun p => (p.1.val, p.2)` back recovers `l`), and `toFinBlock_ne_nil`
(nonemptiness preserved) — each by `induction l` plus
`simp [toFinBlock, ih]`. All three are consumed by `encode_go_wellformed` to
turn the raw `(ℕ × Bool)` output of `processClauseLits` into a `Fin w` block
(bounds coming from `processClauseLits_aux_idx_lt`). `toFinBlock` is `private`
to `TCSlib/BooleanAnalysis/Switching.lean`.
