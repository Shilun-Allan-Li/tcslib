# MIG-1 statement gate, round 2: working notes

Drafted for the maintainer and bundled as `audits/evidence/mig1/gate/r2/NOTES.md`. Paths are
relative to the round-2 directory `gate-mig1-r2/` unless they start with `audits/` or
`TCSlib/`. Every number below is MEASURED (logged) unless marked ESTIMATE.

## 1. Environment and rules kept

- **Checkout and snapshot.** Read-only checkout `wt-mig1r2` at the tip
  99ad2f9894121f45c79a27722d9466223be16473 (`git rev-parse HEAD`), olean snapshot `oleans-t1`,
  toolchain `leanprover/lean4:v4.25.0`.
- **Lean.** Run only through `tools/leanelab.sh`, whose four lines are:

  ```bash
  #!/usr/bin/env bash
  # Elaborate one module file of worktree $1 against olean tree $2 (no olean output, nothing removed).
  WT="$1"; OL="$2"; F="$3"; LP="$OL"
  for d in "$WT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
  export LEAN_PATH="$LP"; cd "$WT"; lean "$F"
  ```

  (Its comment line is over 100 columns; it is quoted, not written by this round.) No `lake`,
  no direct `lean`, no `elan`.
- **Git.** Read-only queries only: for `logs/mig1-statements-r2-provenance.log` (`rev-parse`,
  `diff --stat`, `log`, `status`) and for filling the documents' commit hashes
  (`dev/tools/fillhashes.py`: `rev-parse`, `log --grep`, `cat-file -e`,
  `merge-base --is-ancestor`). The worktree is clean and its index mtime is unchanged
  (`00:36:40`, the checkout time). No hash was typed by hand.
- **No olean written**: nothing under `oleans-t1` is newer than the first round-2 script.
- **Python**: `python3 -I` only. Every scripted edit is asserted (`count == n` before
  replacing); there are no positional splices.
- **Lean files written**: the overlay and the retarget checks. They contain no `#eval`,
  `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`, `native_decide` or syntax/macro/elab
  commands (scanned). Every added line has at most 100 columns; the overlay's 63 over-width
  lines are verbatim lines of the tip's `Loop.lean`.

## 2. What was done, with results and logs

**A. Finding 1's repair** (`gate/scripts/build_overlay.py` → `gate/overlay/`; overlay log).
- **The overlay** `gate/overlay/LoopOverlay.lean` (5,743 lines) = part 1 (5,180) + part 2 (525)
  + 23 `#print axioms`:
  - part 1: the tip's `Build/Loop.lean` with the strengthened `loopHost_prepare` (both
    modes), its two callers, the MIG-0b stand-in, the moved budget family, and the extended
    contract replacing `loopHost_contracts`;
  - part 2: the unit's Loop part with the shims dropped and all six `sorry`s proved.
- **Elaboration**: exit 0, 0 errors, 0 sorry warnings. The 61 other warnings are the tip's
  `Loop.lean` multiset exactly. All 23 prints are within `{propext, Classical.choice,
  Quot.sound}`.
- **Proved beyond the two required specs**: `loopHostTM_decides`, `loopHostTM_finds`,
  `emitLoopTM_computes` and `callTM_run`, each cheaply, from the existing row bodies and
  `emCall_first`. **No sorry is left for F-C to name.**
- **Edits**: `gate/overlay/part1-vs-tip.diff` (12 hunks, +219/−19); `part2-vs-unit.diff`;
  `standin-vs-mig0b.diff` (only the docstring and the declaration line differ).
- **Private statement changes** (`overlaycheck.py stmts`): exactly `loopHost_prepare` and
  `loopHost_contracts`. Body-only changes: the public rows `exists_loopCfgTM`,
  `exists_loopFindTM` and `exists_emitLoopTM`, all subsumed by F-C's row swap.

**B. The systematic retarget check** (`retarget.py` → `gate/data/retarget-table.tsv`;
`retarget_checks.py` → `gate/checks/`; retarget log).
- **Table**: 59 declarations (47 moves, 12 absorptions), 215 citations. Classes: IDENTICAL 53,
  MOVES-WITH 112, GENERALIZATION 11, **WEAKER 1** (`f2_loopHost_prepare`, repaired),
  NOT-CARRIED 38, PROBLEM 0.
- **Accessibility**: 174 now, 3 after F-A's decision-4 import, 38 not carried, **0
  inaccessible**. There is no WEAKER or inaccessible case besides `loopHost_prepare`.
- **Lean evidence**: 21 restated copies, 0 errors after overlay part 1. Against the tip's
  `Loop.lean`, exactly 2 errors, at `f2_loopHost_prepare` and `f2_loopHost_contracts`.
- **The r2 plan** (`gate/data/deletion-plan.tsv`; deletion-plan log). Round 1's classifier
  reproduces round 1's table byte for byte at the tip; the r2 classifier changes two rows:
  - `f2_loopHost_prepare`: new fate "delete: its fuel-head clause is added to Loop's
    loopHost_prepare (strengthened in place)";
  - `f2_head_steps`: absorbed → duplicate of MIG-0b's interval lemma (decision 3).

  So "modified copy" goes 16 → 15 (614 → 564 lines), duplicates 7 → 8, absorbed 13 → 12; the
  total is 378 declarations and 9,172 lines.

**C. Minors 2–4.**
- `gate/scripts/runall.sh` is rewritten and `build_unit.py` fixed.
- The final runner pass gives exit 0, `RESULT: PASS` (`logs/mig1-statements-r2-elaboration.log`;
  stdout in `dev/runall-final3.stdout`).
- Negative controls (`logs/mig1-statements-r2-runner-negative-control.log`):
  - a deliberate one-token elaboration error in a scratch copy: exit 1, 14 deviations;
  - a missing input: exit 2, nothing written;
  - the builder on an empty template set: exit 2, target untouched.
- The bundle lists are `BUNDLE-FILES.txt`, `BUNDLE-MISSING.txt` and `EVIDENCE-MAP.tsv`. The 36
  round-1 runner inputs are byte-identical to the committed files.
- The corrected sentences are in the pack, section "Corrected descriptions".

**D. Re-measurement at the tip** (the runner; one pass).
- **Unchanged from round 1**: the unit 31 sorry / 6 other warnings; the spec probe 70 / 6; the
  bridge probe 0 / 0; the eight cuts as round 1; identity 158 / 0 with the control at exactly
  3; axioms 130 = 46 sorry-free + 84; names 0 clashes and 1 intended moved clash (the tip index
  holds 14,300 declarations in 575 modules), 0 against MIG-0b's 1,211; widths 0, lint 0 FAIL /
  2 WARN; R3 24 checks OK.
- **Consumers**: 221 in 35 files (53 rows) and 216 in 33 (34 home rows), **unchanged**.
- **Replay**: 212 (S, F-A), 82 (F-B), 97 (F-C), 34 (F-D) of 632.
- Logs: `logs/mig1-statements-r2-{elaboration,cutcheck,identity,axioms,names,consumers,
  replay,r3}.log`. The decision-2 records are in `logs/mig1-statements-r2-s-records.log`.

**E. The pack**: `mig1-statements-r2-pack.md` (522 lines, none over 100 columns).

## 3. Unexpected findings

1. **Consumers.** The brief expected new citations in `FormulaKit/Emit.lean` and
   `RAMSimulation/WordSize.lean`. Both are **docstring mentions, not code citations**
   (`Emit.lean:19, :29`, `exists_emitLoopTM`; `WordSize.lean:75`,
   `computesFunInTime_lengthBits_spaceUsed`). The per-row code-citation totals are unchanged;
   doc mentions go 191 → 194. `WordSize.lean:75` cites `Build/Catalog.lean:4318`, which goes
   stale at F-D: a new F-D docstring site in a RAM-simulation file.
2. **The moved contract needs an explicit coefficient.** Catalog's extended contract is
   `∃ c, ∀ x, …`. The public `loopHostTM_contracts` names `10` and cannot be derived from an
   existential, so the moved private contract takes round 1's manifest transform: `∃ c`
   removed, `c ↦ 10`. This is a private statement change beyond a verbatim move, disclosed in
   the pack. Round 1's plan used the transform only in the probe shim.
3. **Three row-body edits.** With the contract replaced, the tip's `exists_loopCfgTM` and
   `exists_loopFindTM` destructure two more conjuncts. `exists_emitLoopTM` discards the
   strengthened preparation's clause. These proof edits are in public rows (statements
   unchanged), and F-C's row swap subsumes them.
4. **Tooling limits found on the way.**
   - `tools/privstmt.py` cuts statements at the first `:=` and stops inside `(input := x)`;
     it misses the contract's change. `overlaycheck.py stmts` is depth-aware.
   - Round 1's `region.statement` cut 3 of 264 copies early (at a `let start :=`); no identity
     verdict changes.
5. **Decision 3 changes a second fate**: `f2_head_steps`, besides the requested
   `f2_loopHost_prepare`. The unit's Part 1 still states `abs_workTapePos_runFrom_sub_le`,
   which is H2's under decision 3 and not in MIG-1's landing set (70 public names, not 71). It
   is kept so the identity and axiom counts stay comparable.
6. **The MIG-0b range.** The brief cites `Finite.lean:385–413`; the declaration with its
   docstring is lines 386–408 of the landing file (385 is blank; 409–413 close the namespace).
   MIG-0b's landing set is not in the repository as files. The stand-in's source is in
   `audits/evidence/mig0b/r2/landing-diffs/TuringMachine/Finite.diff`, byte-identical to the
   scratch landing set's diff (checked).
7. **My runner rewrite dropped one step** of round 1's: the inline writer of
   `work/part-lines.json`, which `namescreen.py` reads. The first pass at the tip failed there
   (`dev/runall-run1.stdout`, with the two replay deviations); restored.

## 4. Open issues for the maintainer

- **Staging.** The bundle files are staged under `stage/` at their repository paths (hashes
  filled from `git rev-parse`). The bundle document itself (`audits/mig1-statements-r2-bundle.md`)
  is not built here.
- **Records only.** The round-2 evidence is non-`.lean` records (`audits/...`). The overlay is
  evidence (`.lean.txt`), not a landing edit.
- **No maintainer re-check** is claimed in the pack. Add one only if it is run.
- **The round-1 findings** `audits/mig1-statements-findings.md` are untracked in the main
  checkout (not at the tip); the bundle stages a byte copy (SHA-256 `8a899aca…`, from
  `shasum`) as a new file.
- **Reproducing from the repository** needs:
  - a gate directory assembled per `EVIDENCE-MAP.tsv` (part B renames `*.lean.txt` templates
    to `*.lean`);
  - the tip's checkout and olean snapshot;
  - MIG-0b's landing set (BUNDLE-MISSING.txt).
- **F-C** must apply the overlay's part-1 edits with the in-place renames (`loopHost →
  loopHostTM`, `emCallTM → callTM`), cite `MultiTapeTM.workTapePos_runFrom_mem_Icc` for the
  stand-in, and swap the six rows. The 97-module replay is the fill gate's.

## 5. Directory map

- `gate/`: the runner's gate directory: inputs (`parts/`, `probe-parts/`, `bridge-parts/`,
  `scripts/`, `data/`) and outputs (`overlay/`, `checks/`, `cuts/`, `probes/`, `work/`,
  `MIG1Statements.lean`).
- `logs/`: the 14 round-2 logs.
- `data/`: copies of `gate/data/deletion-plan.tsv` (round 2) and `gate/data/retarget-table.tsv`.
- `negctl/`: the scratch copies and logs of the runner's negative controls.
- `dev/`: manual development runs (`overlay-manual/`, `checks-manual/`, …; superseded by
  `gate/`), the runner's stdout per pass, and the staging tools.
- `stage/`: the 45 new bundle files, at their repository paths (`dev/tools/evidencemap.py`
  verifies the runner inputs and writes `EVIDENCE-MAP.tsv`; `dev/tools/fillhashes.py` fills
  the documents' commit hashes).
- `round1/`: the byte copy of the untracked round-1 findings.
