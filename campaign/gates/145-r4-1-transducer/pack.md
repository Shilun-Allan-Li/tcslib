# Gate 145 · Closeout R4-1: the SAT/Hardness one-way transducer copies (PR #334)

**Not yet clear to merge** · PR #334 is a draft. Seyoon dispatches and merges.

- Lean head: `7bb1f687d87c8faa25c8523fc4bb1e15a5d473c1`.
- Base: campaign Lean `68cba664c2fcb4e33b4845b385feea3f456d0105`, records `e805e481`.
- This is the first audit.

## Scope

Chapters 3–4 closeout, refactor wave R4, pilot slice R4-1 (`campaign/closeout/REFACTOR-PLAN.md`, R4
row; bundled). The design study and the maintainer's recheck are in
`campaign/closeout/r4-design-request/delivery/` (bundled). Seyoon ruled on 2026-11-16:
- run the pilot;
- extend the colleague-authored `ClassNP/Transducer` instead of adding a new module (a separate
  module was first proposed and approved, then dropped because it duplicated `transduce`);
- allow `SAT` to import `ClassNP/Transducer`, `ClassNP/PolyTimeBlockLoop` and `Build/WordTests`.

### Changes

- **`ClassNP/Transducer`** (new public API, approved). A transducer with a final emission:
  - `transducerFinalTM δ o f q₀`: `transducerTM`, except that its halting transition at the
    right blank also emits `f q`;
  - `transducerFinalTM_computes`: it computes `x ↦ transduce δ o q₀ x ++ (f (x.foldl δ q₀)).toList`
    within `n + 1` steps;
  - `polyTimeComputable_transduce_final`.

  The file also gains private helpers `finalCfg`, `transducerFinalTM_step`, `_step_end` and
  `_run`. No existing declaration changes.
- **`ClassNP/SAT`:**
  - Deletes the twin finite mapper `satMapWord/satMapTM/satMapCfg/satMap_run/satMap_poly` (kind 4).
  - Deletes the scanner run `satScanCfg/satScan_step/satScan_run`.
  - `satScanTM` is now `transducerFinalTM step (fun _ _ => none) (fun q => some (accept q))`. It
    keeps its name; its body changed from a structure to that term.
  - `satScan_computes` cites `transducerFinalTM_computes` through the new private
    `satScan_silent`.
  - `sat_pt_tail`/`sat_pt_head` cite `polyTimeComputable_tail`/`polyTimeComputable_take1`.
  - `sat_pt_eq` cites `FinTM.computesFunInTime_decideEq` (PL-1).
- **`CookLevin/Hardness`:**
  - Deletes the twin mapper `clA5MapWord/clA5MapTM/clA5MapCfg/clA5Map_run/clA5Map_poly` and the
    fill machine `clFillTM/clFill_run`.
  - `clNative_fill` cites `polyTimeComputable_transduce`.
  - `clA5Div_native` reads `transduce` through `transduce_nil/_cons`.
  - `clA5_pt_eq` cites `FinTM.computesFunInTime_decideEq`.
  - No import change.

The kept private names keep their statements, so all their use sites are unchanged. No public
statement changes. Net: **−161 Lean lines** (Transducer +111, SAT −145, Hardness −127).

## Brief for the auditor

1. **New API.** Check the three public declarations' statements, docstrings and proof sketches
   (policy §2–3). Check that `transducerFinalTM` agrees with `transducerTM` on every live bit
   transition and differs only at the right blank. Check the module docstring's lists.
2. **Retirement.** Check that each deleted copy's role is taken by a citation with the same or a
   stronger statement (the base bodies are in the carrier, `source/campaign/`). Check that no
   other file names a deleted declaration (they were private).
3. **Statements.** `SOURCE.json` lists `satScanTM` as `header_changed` and `definitions_changed`:
   a private definition, now a term instead of a `where` structure, defining the same machine
   kind. Confirm that nothing else changed and that no public statement changed.
4. **Rule 10.** The 16 changed or added proofs read other files' definitions only through
   published equations. The evidence is in `seals/`, `controls-part*/`, `qa/FOREIGN-ARGUMENTS.json`
   and the Lean-backed `defsweep/` (counts below). Review in particular the new run proofs in
   Transducer: they use `MultiTapeTM.step_of_some`, `Action.apply_state/_inputPos/_output`,
   `FinTM.inputSymbol_at`, `moveInputPos_pos_of_ne_right`, `Cfg.ext_zero_tapes` and
   `Cfg.init_*` via `MultiTapeTM.initCfg_eq`.
5. **Copy screen** (population: the three owners), `evidence/PAIR-DISPOSITIONS.json`:
   - 16 directed pairs are gone. These are the retired twins (8 unordered pairs).
   - 2 directed pairs are new: `polyTimeComputable_transduce_final` and its existing sibling
     `polyTimeComputable_transduce`. Both are three-line citations of
     `polyTimeComputable_of_linear` and are kept for API symmetry. Judge whether this is
     acceptable.
6. **Records.** Check that the refactor plan's R4 row, the design intake and this pack agree.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the downstream closure of the three changed
  modules, on `oleans-c68cb`.
  - 137 modules replayed: 137 passed, 0 failed.
  - The 14 inherited admissions are pre-existing ones from `main`.
- **Seals** (`seals/`): all 13 changed proofs pass, in all three owners, with every other-file
  definition they reach made irreducible (13 heads).
- **Controls:** 18 definitions' 36 paired controls close natively and fail when sealed.
- **Proof-syntax sweep** (`qa/FOREIGN-ARGUMENTS.json`): 13 roots, 0 explicit reads.
- **Lean-backed sweep** (`defsweep/SUMMARY.json`): it lists four "foreign definitions", all of
  which are mentions inside a `rw` argument rather than unfoldings:
  - `rfl`, a proof argument of `FinTM.inputSymbol_at` in Transducer;
  - `Complexity.transduce`, `List.replicate` and `Unit`, which occur in the `show … from funext hw`
    term of `clNative_fill`'s `rwa`.

  The seals are the authority on this.
- **Lint:** no new finding. One finding is removed: `clFill_run` had no proof sketch, and it is
  deleted.
- Metadata: standard axioms only for the changed proofs.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate145-r4-1-transducer-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
