# Fill `ef-r23-regev`: checkpoint 1 (series 1 and 2)

**Head `daaf5e65f753100afc75d8180625c83b8f60e895`** on the local branch `fill/ef-r23-regev`, two unsigned commits on
base IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (tree `9155903018d18fbc735791f21485abaaee3e161a`, checked):

| # | Commit | Series |
|---|---|---|
| 1 | `c7b2361742bc92d956cbbae438007b37c8070d05` | 1: `Encoding/ModularArithmetic.lean` (new) and the `Encoding.lean` facade line |
| 2 | `daaf5e65f753100afc75d8180625c83b8f60e895` | 2: `Encryption/Symmetric/Regev/Asymptotic.lean` (new) and the `Symmetric/Regev.lean` facade line |

**What this checkpoint claims**
- Series 1 (the general-modulus toolkit) and series 2 (`exists_shiftMachine` and
  `singleMessageSecure_of_dlweAssumption`, both in the brief's exact form) are proved and compile: no `sorry`, standard
  axioms only.
- The payload is complete for that claim: `patches/` (0001–0002 and `COMMITS.tsv`), `src/` (the 4 files at
  `daaf5e65`), and the evidence below.

**How the evidence binds this head**
- The series-3 commit (`324c5de20c4b5fe1e0ee95a07612d3fa2ffd4b1a`, delivered with the final) touches only
  `Encryption/PublicKey/Regev{,/Asymptotic}.lean`. `git diff daaf5e65 324c5de2` lists only those two paths.
- So the four series-1/2 sources are byte-identical at both heads.
- The checks below were run at `324c5de2`, and their rows for the four series-1/2 owners apply verbatim to this head.
  The source SHA-256 in `evidence/build/summary.txt` equals `git show daaf5e65:<path>` for these four files.

**Checks for series 1–2** (details, evidence paths and the series-3 rows: see the final `REPORT.md`)
- **C1:** `ModularArithmetic`, `Encoding`, `Symmetric/Regev/Asymptotic`, `Symmetric/Regev` and the downstream
  `Encryption/Symmetric`: rc 0, 0 errors in both forms, 0 `sorry`.
- **C3:** 47 ADDED declarations in the two new files; the facades add no declarations.
- **C5:** standard axioms only.
- **C6:**
  - Seals strict/coe × A/B on the four owners: 0 errors, 0 failing declarations. Requests, coe-A: 1011, 1121, 1131,
    1134.
  - Paired controls on the nine series-1/2 definitions: `ALL_OK True`, strict and coe.
  - Explicit-unfold scan: 0 foreign.
- **C7:** both facades PASS.
- **C8:** `style_lint` 0 findings; campaign lint has no new FAIL or WARN.
- **C9:** 730 / 310 lines, width ≤ 100.
- **C10:** 0 clashes.
- **C12:** R-P1 0 mismatches, R-P2 (symmetric) 0 mismatches.
- **C13:** `git am` reproduces both hashes.

Environment, sub-agent, statement changes, overlap and questions: as in the final report, delivered in the same
session.
