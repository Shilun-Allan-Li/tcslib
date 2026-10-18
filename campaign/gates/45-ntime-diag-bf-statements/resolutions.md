# C1-E: the exponential decider as a hypothesis (PR #126, X2): resolutions (round 1; gate CLOSED)

**Gate:** the statement gate of PR #126 (`lean/ntime-diag-bf` at `5333b29b`, stacked on #125):
`Turing.NTimeDiag.exists_diagonalizer` takes BF's conclusion as a hypothesis `hBF` (gate 40's
review, X2; the user's ruling, 2026-10-17), and gate 40's X3 (two docstring lines). Pack
`audits/ntime-diag-bf-statements-pack.md`; bundle SHA-256
`296b21e2d98064d29e30761d7d78693cd1ba88ff3113843aaa02d7588515824a` (34 sections; folder
`45-ntime-diag-bf-statements-gate/`). Replay passed (user, 2026-10-17): 2 of 2, static-equal (2).

**Round 1** (`audits/ntime-diag-bf-statements-findings.md`, verbatim): **PASS, 0 blockers,
0 majors, 2 minors, 10 notes.** The auditor could not run Lean and treated the elaboration,
consumer and replay logs as supplied evidence. The maintainer's review sub-agent verified every
finding at `5333b29b`: all true, at the auditor's severities. **The gate is closed.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `exists_diagonalizer`'s docstring (lines 289–292) says `NTimeHierarchy` "imports this module"; it does not (its imports are `NDCodes`, `NTIME`, `TimeConstructible`, `NDNormalForm`). | **True.** **The fix** (`.lean`, docstring only, line count kept; blob `026b52da` → `caafcb34`): "`TCSlib.Complexity.Diagonalization.NTimeHierarchy`, whose `ntime_hierarchy` needs this module, so" / "this module cannot import it; that proof supplies it from `Turing.exists_ndAcceptsWithin_decider`." / "Taking it as a hypothesis keeps the two modules' imports acyclic." It stays true once H's fill adds the import; the auditor's "will import this module when `ntime_hierarchy` is filled" would then need reverting. Elaborated against `oleans-lx2`: exit 0, the two contracts' warnings at 270 and 334; lint unchanged. **A commit on #126**, the top of the stack (no restack), re-replayed by `replay-lx2b.sh` (2 modules). |
| 2 | minor | `x2/replay-lx2.sh:18`'s failure message names `0a5878ed`; the check is against `4ab012d9`. | **True; records.** The script is kept as run. `replay-lx2b.sh` carries the corrected message. The same copied message is in `replay-lc1w.sh`, `replay-lseam.sh` and `replay-lg4c1.sh`. |
| 3–12 | notes | Integrity and freeze (the binder is the only code change); `hBF` is BF's conclusion at the same `c`; truth; `ntime_hierarchy`'s chain; satisfiability; adversarial instantiations; the unchanged definitions and `exists_queryTM`; the cycle removed; lint and screen; the execution records. | No action. Notes 5–8 carry to E-D's and H's briefs. |

**Carried:**
- **E-D's brief** (notes 5 and 8): extract `hBF`'s machine before building `D`;
  `C = max 1 (max C_R C_BF)`; keep the first-verdict stop, silent provisional output and the
  clock's inclusive finish deadline. Sanity checks: BF rejects at budget `0`, and a timed-out
  simulation is rejected despite provisional `[true]` output.
- **H's brief** (notes 6 and 10): add `import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer`
  and apply `exists_diagonalizer hf hg c (exists_ndAcceptsWithin_decider c)`. The X1 sketch
  correction (gate 40's review, L-2) is still to be applied before H's brief.
- **The admissions stay explicit** (note 7): `exists_timed_universal_NDTM` and
  `FinNDTM.exists_exhaustiveDecider` are sorried, so `ndAcceptsWithin_decider_of_universal` is a
  conditional derivation, not an admission-free existence proof.
- **Bundles** carry every file their lint scope reads (note 11; gate 40's review).

**#126 is not yet clear to merge.** Its gate is closed and its replay passed at `5333b29b`, but it
is stacked on #125, which waits on #124 (gate 43 failed). With minor 1's commit, its replay is
re-run first (`replay-lx2b.sh`).
