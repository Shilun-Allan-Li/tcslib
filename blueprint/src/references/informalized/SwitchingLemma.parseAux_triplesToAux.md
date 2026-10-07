<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: parseAux_triplesToAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# parseAux inverts triplesToAux

**Claim.** For `0 < w` and every triple list `ts : List (Fin w × Bool × Bool)`,
`parseAux w hw_pos (triplesToAux w ts) = ts`. So flattening triples to an aux
list — writing `(pos.val, dir)` and, when `hasMarker = true`, an extra
`(w, false)` marker — is undone exactly by re-parsing.

**Proof.** Induction on `ts` (`induction ts with`), using
`hfin : (⟨pos.val, pos.isLt⟩ : Fin w) = pos` from `Fin.ext rfl` to identify the
rebuilt index with the original.

- *Nil*: `rw [triplesToAux, parseAux_nil]`.
- *Cons* `(pos, dir, mark) :: rest`, split on `mark`:
  - `mark = true`: the flattened list is `(pos.val, dir) :: (w, false) :: …`, so
    `parseAux_cons_marker` peels off one triple with marker `true`; then `ih`
    and `hfin`.
  - `mark = false`: `parseAux` needs to see the *next* entry to know there is no
    marker, so the tail is case-split as well.
    - tail `[]`: `parseAux_singleton` plus `hfin`.
    - tail headed by `(pos2, dir2, mark2)`: `parseAux_cons_nonmarker` applies
      because `pos2.val < w` (`Fin.isLt`), and the residual goal is exactly the
      induction hypothesis after folding `(pos.val, dir) …` back into
      `triplesToAux w ((pos2, dir2, mark2) :: rest2)` by `rfl` (`rw [← hexp]`),
      done for `mark2 = true` and `mark2 = false` alike.

**Used in.** `exists_aux_injection` (three rewrite sites), where the
well-formedness witness `aux = triplesToAux w ts` from `encode_go_wellformed`
is turned into a recovery of `ts` from `aux`, making the encoder's aux output
injective in `ts`.
