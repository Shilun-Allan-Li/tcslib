Proves `SPACE_linear_ne_NP` using the general padding theorem from merged #228. The existing
private padding argument is instantiated with `S n = n² + 1`, `T m = m + 1`, `C = 1`, `d = 2`;
the language conversion uses `Set.ext` and `mem_padLang_iff`. Adds only the previously approved
Padding import; every existing declaration statement and the other proof bodies stay unchanged.

Validation so far: Hierarchy elaborates with only the unrelated `space_universal` admission.
Source census stays 4 public / 43 private declarations. Unfiltered compiled census 137 → 138
(4 → 5 non-private): one internal proof auxiliary, no source API addition. The target uses only
the standard three axioms. The four-definition seal passes with default-simp unfoldings removed;
all eight positive/negative controls have the exact expected results. Existing lint findings are
unchanged. Independent internal review found no required fix.

The current-campaign merged-tree replay passes **2 modules, zero failures/static mismatches**,
leaving only F6's existing admission. The complete eleven-file screen has 31→31 pairs, zero
new or removed; every reviewed source blob matches the published PR.

**Not yet clear to merge.** External Codex gate 116 must close. Seyoon merges after the gate closes. Evidence is under
`campaign/gates/116-space-linear-ne-np/`.
