/-- Each coordinate of total residue decoding reads its canonical row-major bit
block and reduces that block's natural value modulo p. This is technical wire-
representation glue, valid for every word without a canonicality or width bound.

**Proof sketch.** Read decodeResidues_apply. Identify its drop/take block with the
finite list of the row's width bit coordinates, using the published list element,
length, and finite-product coordinate equations. Then transport the list equality
through listToNat and the residue cast; no range rejection is introduced. -/
theorem decodeResidues_block (p : ℕ+) (count width : ℕ)
    (word : Fin (count * width) → Bool) (i : Fin count) :
    decodeResidues p count width word i =
      (listToNat (List.ofFn (fun j : Fin width => word (finProdFinEquiv (i, j)))) :
        ZMod (p : ℕ)) := sorry
