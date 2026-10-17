# C1's normal form moved to `ClassNP/NDNormalForm` (PR #120): resolutions (CLOSED, round 1)

**Gate:** PR #120, which moves NF (`Turing.FinNDTM.exists_codeNDTM_accepts_linear`),
byte-identical, out of `Diagonalization/NTimeHierarchy` into a new module.
- Pack: `audits/nd-normalform-pack.md`, preserved as dispatched.
- Bundle SHA-256: `da4bb710a6ef1f9d12677523212dcc7f1f3af7af0cd6fc95ca7fd994020ef723` (27
  sections; folder `infra_local/gate-dispatches/38-nd-normalform-gate/`; Lean `6d18902f`).
- #120 merged before the gate returned (user, 2026-10-17; tip `75edca6f`).

## Round 1: PASS (0 blockers, 0 majors, 3 minors, 4 notes)

The findings are in `audits/nd-normalform-findings.md`, verbatim. The auditor could not run Lean.
It reconstructed the base files, compared the declarations and blob hashes, and ran the lint on the
three attached files. The maintainer's review sub-agent verified every finding at the tip
`75edca6f`: all true. **The gate is closed.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1–4 | notes | The move is exact; consumers keep access; the home is right; moving rather than copying is acceptable. | No action. |
| 5 | minor | `ClassNP.lean` imports `NDNormalForm` but its `## Contents` list has no entry for it (policy §1); the lint checks imports only. | **True.** The entry is a `.lean` docstring edit, so it rides in gate 37's round-2 follow-up PR (`audits/nd-api-resolutions.md`), after the `ExhaustiveReplay` entry: "* `NDNormalForm` — the linear-overhead coded normal form: every bundled binary NDTM has a coded two-work-tape equivalent whose acceptance tracks its own, forward within a linear allowance and backward unboundedly [AB09, §3.2]; the time hierarchy diagonalizes over these codes. The normal form is sorried." The facade's downstream closure is itself alone, so it adds nothing to that PR's replay. |
| 6 | minor | `move.py.txt` lines 88–91 rewrite an `NDCodes` docstring, which NOTES says stays unchanged, and the script asserts no before/after byte equality, which NOTES and the pack claim. | **True; records.** The saved script is kept as run, and NOTES now says: "`move.py.txt` as saved also rewrote `NDCodes`' pointer (lines 88–91); that edit was reverted before commit, and the committed change is the three-file patch." NOTES' "asserted by `move.py.txt`" now reads "checked by comparing the extracted block of `NTimeHierarchy` at the base with `NDNormalForm` at the head; the script itself asserts only substring counts". The review repeated the comparison: 2,599 characters, byte-identical. **Pack erratum:** question 1's "(`move.py.txt` asserts it)" is likewise the comparison, not the script. |
| 7 | minor | No PR-body snapshot. | **True; records.** `audits/evidence/nd-normalform/pr-body.md` (retrieved 2026-10-17, head `6d18902f`). The gate's PR-body check rested on the pack's attestation. |

The auditor's remaining limit (the imported `NTIME`/`NDCodes` definitions and the full downstream
graph were not in the bundle) is recorded: those were checked by import identity and the replay.
