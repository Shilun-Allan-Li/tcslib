# G4 continuation 1: the partial's helpers that unfold another file's definition

Maintainer, 2026-10-16, measured at #118's head `4ae686be` (the tip's Lean after #118 merges), in
`Build/ZoneRebalance.lean`'s home (lines 127–350). Under ground rule 10 (no unfolding of another
file's definition, the zone layer included), four of the partial's 18 `zr_` helpers must be
re-pointed to published lemmas. The others read only public lemmas or the file's own
definitions.

| Line | Helper | The step | What it unfolds | Re-point to |
|---|---|---|---|---|
| 142 | `zr_read_slot` | `rw [hcell]; rfl` | `zoneSlotOf` on `.inr` (and `Option.map`) | `Turing.zoneSlotOf_inr` |
| 146 | `zr_capacity_pos` | `Nat.mul_pos (by decide) (Nat.two_pow_pos i)` against `0 < zoneCapacity i` | `zoneCapacity`, by elaboration | `Turing.zoneCapacity_eq` (`zoneCapacity i = 2 * 2 ^ i`) |
| 213 | `zr_ruler_length` | `simp only [zoneCapacity, Nat.mul_comm]` | `zoneCapacity` | `Turing.zoneCapacity_eq` |
| 230–237 | `zr_mirror_tape` | `rfl` at home; `simp only [zonedTape, …]`; `rfl` after each side's rewrite | `zonedTape`, `zoneCellAt`, `ZoneContents.swap` | `Turing.zonedTape_zero`, `zonedTape_of_pos`/`_of_neg`, `zoneCellAt_eq`, `ZoneContents.swap_home`/`_left`/`_right` |

Not re-pointed (allowed):
- `zr_cell_step`'s two `rfl` arguments (lines 312, 315): its own table's transition equation,
  for a leaf defined in this file;
- the `rfl` patterns of `rcases` (line 344);
- `zr_extend_cell`'s `change` on `zr_zonePos`, its own definition.
