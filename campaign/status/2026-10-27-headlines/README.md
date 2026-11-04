# Chapters 3–4 headline status (maintainer, 2026-10-27)

**Tree:** the campaign tip `43fe918f` (Lean equal to #172's merged head `940671e0`), against the
replay snapshot `oleans-lhh`, one elaboration through `tools/leanelab.sh`.

- `Headlines.lean.txt`: the 26 headline theorems of [AB09] chapters 3–4 that the tree states. For
  each, `#print axioms` and a walk listing the reachable constants that use `sorryAx` directly.
  Exit 0. The output is `Headlines.out`.
- **19 of 26 are on `[propext, Classical.choice, Quot.sound]` only** (corrected 2026-10-28: the first
  version said 20 of 26 and "six", but listed seven). The other seven:
  - `ntime_hierarchy` and `NTIME_linear_ssubset_square` rest on `exists_diagonalizer`
    (`NTimeDiagonalizer`) and `exists_codeNDTM_accepts_linear` (`NDNormalForm`);
  - `savitch` (the general form), `space_universal`, `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`
    and `SPACE_linear_ne_NP` are themselves stubs.
- `sorry-census-tip.txt` (`census.py`, a textual census with `fillinputs.py`'s detection): every
  sorried declaration of the tree at the tip, 489 in all, most of them outside the campaign.
