# Chapters 3–4 headline status (maintainer, 2026-11-05)

**Tree:** the campaign after #188 (Lean `52331982`), against the replay snapshot `oleans-led4`.
The probe is the 2026-10-27 one, unchanged (`Headlines.lean.txt`), elaborated once through
`tools/leanelab.sh`, exit 0 (`Headlines.out`).

**19 of 26 are on `[propext, Classical.choice, Quot.sound]` only, as on 2026-10-27.** What changed
underneath:
- `ntime_hierarchy` and `NTIME_linear_ssubset_square` now rest on **one** admission,
  `exists_codeNDTM_accepts_linear`: the diagonalizer `exists_diagonalizer` was proved (#188, gate
  93). The normal form is proved on #191, which is stacked on #190; with both merged, 21 of 26.
- The other five are stubs:
  - `savitch` (general) has the deepening fill next. Its API, #182 and #184, has merged.
  - `space_hierarchy`, `LOGSPACE_ssubset_PSPACE` and `SPACE_linear_ne_NP` are H's fill.
  - `space_universal` (F6) waits on U2's harvest API PR.

Outside the 26: G5's interface landed (#189). `universal_TlogT`, [AB09, Theorem 1.9] at `T log T`,
is proved from the stated two-tape reduction `two_work_tapes_run`, which is G5's fill.
