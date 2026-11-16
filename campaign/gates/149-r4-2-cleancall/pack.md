# Gate 149 · Closeout R4-2: shared clean modules, `ClassNP/CleanCall` (PR #342)

**Not yet clear to merge** · PR #342 is a draft. Seyoon dispatches and merges.

- Lean head: `a12da4d3fb38a849a7c5e8b7cdfd09e2cb30dfb7`.
- Base: campaign Lean `c2ad69cc` (the #335 merge); records `f4d1fae3`.
- This is the first audit.
- The head descends from #335's head `2dc0fc30` (the merge base). The PR diff against the campaign branch is exactly
  the four owners below.

## Scope

This is wave R4, item R4-2: SG1 kinds 1, 2 and 5, with the `live_prefix`, `guard_add` and
first-halt riders. The rulings are in `campaign/closeout/REFACTOR-PLAN.md` and the design study is in
`campaign/closeout/r4-design-request/delivery/`; both are bundled.

Seyoon approved R4-2 on 2026-11-16, with its public API, and with a stop rule: carry it if it
nets more than +50 lines or creates more copy pairs than it retires. It measured **+63**, and
Seyoon accepted the overshoot on 2026-11-16. The audited head is **+66**: the second commit adds
the three-line proof sketch that the style lint requires on the private `stopTM_step` (History).

SAT (`ClassNP/SAT`) and Cook–Levin hardness (`CookLevin/Hardness`) each carried a private copy of
the same "clean subroutine call" layer. A clean module is a machine that runs from the state
`stateWord k arg`, first halts after a positive number of steps within a polynomial budget, and
leaves `stateWord k (result arg)` with output `emit arg`. The layer has these parts:

- **Stop adapter.** This turns a bridge machine with an entry and an exit state into one that
  halts cleanly at its first return to the exit. It tags the state with a "left the entry" flag,
  and it is a definition plus a step lemma.
- **Clean-stop lemma and the clean-module contract.**
- **Bridge budget bound.**
- **Install and emit modules.** Every polynomial-time `f` has a clean module that replaces `arg`
  by `f arg` (install) or keeps `arg` and emits `f arg` (emit).
- **Riders.** The first-halt cut (a positive first halting time), the guard join (avoiding a state
  across a seam) and the live-prefix lemma.

### New module `ClassNP/CleanCall` (374 lines, new public API approved with R4-2)

| Declaration | Kind | Role |
|---|---|---|
| `Turing.MultiTapeTM.exists_first_halt_pos` | theorem | first-halt cut with a positive time (SAT's `sat_call_first_halt` body) |
| `Turing.MultiTapeTM.avoid_add` | theorem | guard join, via `Turing.segment_iff` and `Segment.trans` |
| `Turing.FinTM.CleanModule` | structure (Prop) | the clean-module contract: `pos : 0 < M.k`, `run` |
| `Turing.FinTM.stopTM` (+ `stopTM_k`) | def (+ simps equation, not a simp lemma) | the stop adapter |
| `Turing.FinTM.stopTM_runFrom_clean` | theorem | the adapter's run, stated in the adapter's own fields |
| `Turing.FinTM.CleanModule.of_stop` | theorem | a guarded bridge run gives a clean module, budget `B n + 1` |
| `Complexity.exists_cleanInstall` | theorem | clean install modules, polynomial budget |
| `Complexity.exists_cleanEmit` | theorem | clean emit modules, polynomial budget |

Three private helpers support these: `bridge_bound`, `output_le` and `clean_of_bridge`. The last
one is shared by install and emit. Two private step helpers (`mapState_workTapes_eq` and
`_workTapePos_eq`) give function-level forms of the pointwise `Cfg.mapState` equations.

`stopTM_runFrom_clean` and `CleanModule.of_stop` state the adapter's start and tape count as
`(stopTM C entry exit).tm.q₀` and `(stopTM C entry exit).k`. Consumers that use them therefore
never unfold `stopTM` (rule 10).

### Owners

- **`ClassNP/SAT`** (4,225 → 4,067 lines).
  - **Deleted:** `satStopTM`, `satStopCfg`, `satStop_step`, `sat_live_prefix`, `satStop_clean`,
    `satClean_stop` and `sat_bridge_bound`.
  - **Now one-line private citations:** `sat_call_first_halt`, `sat_guard_add`, `SatClean` (a
    private `abbrev` of `FinTM.CleanModule`), `satClean_install` and `satClean_emit`. Their use
    sites are unchanged.
  - **New import:** `ClassNP/CleanCall`.
- **`CookLevin/Hardness`** (8,277 → 8,125 lines).
  - **Deleted:** `clA5StopTM`, `clA5StopCfg`, `clA5Stop_step`, `clA5_live_prefix`,
    `clA5Stop_clean`, `clA5Clean_stop`, `clA5_bridge_bound` and `clA5_call_first_halt`.
  - **Now one-line private citations:** `clA5_guard_add`, `CLA5Clean` (abbrev),
    `clA5Clean_install` and `clA5Clean_emit`.
  - **Restated** (private): `clA5Copy_clean` (statement in `FinTM.stopTM clInputTM 0 2` with
    `output := []`), `clA5Modules` (`| 0 => FinTM.stopTM clInputTM 0 2`), `clA5Modules_bound`
    (reads `FinTM.stopTM_k`), and `clA5Startup`'s proof.
  - **New private readers:** `clA5_initCfg` (`tm.initCfg x` as `Cfg.ofWords`, through the
    published `Cfg.init_*` and `Cfg.ofWords_*` equations) and `clA5_ofWords_out`.
  - Hardness already imports ClassNP, so no import changes.
- **`ClassNP`** (the facade): imports `CleanCall` and adds one Contents line.

The public statements of SAT and Hardness are unchanged. The `header_changed` entries are all
private: `SatClean`, `CLA5Clean`, `clA5Copy_clean` and `clA5Modules`. Net: **+66 Lean lines**
(+449/−383).

## Brief for the auditor

1. **API.** Check that the eight public declarations in `CleanCall` are stated as in the table:
   - general in `k`, `S` and the input `x`;
   - no campaign labels in docstrings;
   - each with a proof sketch and the [AB09, §1.2] attribution (policy §§2–3).

   `CleanModule.run` should say exactly what the deleted private contracts said.
2. **Statements.** Confirm that the public statements of SAT and Hardness are byte-identical to
   base. Check that the private restatements (`clA5Copy_clean`, `clA5Modules`) preserve what their
   consumers (`clA5Startup`, `clA5Modules_bound`, the module bank) need.
3. **Citations.** Check that each one-line citation has the deleted copy's statement:
   `sat_call_first_halt`, `sat_guard_add`, `clA5_guard_add`, `satClean_install/_emit` and
   `clA5Clean_install/_emit`. Check that `SatClean`/`CLA5Clean` as `abbrev`s keep projections
   (`.pos`, `.run`) working at the use sites.
4. **Deadness.** Check that each deleted declaration was referenced at base only from the deleted
   set, or from a site that now cites `CleanCall`.
5. **Rule 10.** The changed and added proofs: seals, controls and both sweeps (counts below). The
   adapter's consumers in Hardness must not unfold `FinTM.stopTM`; they read it through
   `stopTM_k`, `stopTM_runFrom_clean` and the adapter-field statements.
6. **Copy screen** (population: CleanCall, SAT and Hardness): see
   `evidence/PAIR-DISPOSITIONS.json` and the note under Evidence.
7. **Stop rule.** The overshoot is accepted (+63 measured; +66 with the required sketch). Judge
   whether the residual pairs are acceptable.

**History.** At the first head, `38bdef17`, the replay (53/53, run on #335's prospective merge
before #335 merged), the seals (25 proofs) and the controls passed. The style lint found one new
item: the private `stopTM_step` had no **Proof sketch.** The head `a12da4d3` adds it (docstring
only; `patch/head1-to-head2.patch`). Every check below was rerun at `a12da4d3`, and the copy screen
delta is identical. The first head's results are in the carrier (`history/head1-38bdef17/`).

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the four owners' downstream closure on
  `oleans-cc2ad` (the #335 merge's snapshot), against records tip `f4d1fae3`.
  - 53 modules replayed: 53 passed, 0 failed, 0 inherited admissions.
  - 873 input objects and 874 output objects. The one added object is `ClassNP/CleanCall`, and
    four objects change.
  - The driver gained one option for this gate, `added_owners`, because CleanCall is the first new
    module in a closeout replay. A declared new module needs no input object, and it is the only
    output object without one (`drivers/driver/driver.py`).
- **Seals:** all 25 changed or added proofs pass with every other-file definition they reach made
  irreducible (23 heads): 13 in CleanCall, 4 in SAT and 8 in Hardness.
- **Controls:** 23 definitions' 46 paired controls close natively and fail when sealed.
- **Proof-syntax sweep:** 25 roots, 0 explicit reads.
- **Lean-backed sweep:** 108 identifiers, with two flagged constants. Both are term arguments
  inside a rewrite list, not rewrite rules:
  - `rfl`, in `rw [if_pos ⟨rfl, rfl⟩]` in `stopTM_runFrom_clean`;
  - `Turing.stateWord`, in `rw [hi, hw, ← clA5_ofWords_out (2 : Fin 3) (stateWord 1 x)] at he` in
    `clA5Copy_clean`.

  Neither unfolds a definition. The sealed check of both proofs passes.
- **Citation homes** (G147-02 procedure): `defsweep/CITATION-HOMES.json` resolves every identifier
  of the changed declarations at head and at base, and lists the TCSlib files defining constants
  that are newly cited. All ten files are in the bundle, pinned at the head (their Lean is the
  campaign's):
  - `TuringMachine/`: `Configuration`, `Deterministic`, `Finite`, `Simulation`, `StateRenaming`
    and `CfgFacts`;
  - `TuringMachine/Build/`: `Convention`, `Loop` (home of the install and emit bridges) and
    `Contract/Basic`;
  - `ClassNP/PolyTime`.
- **Lint:** no new finding at the head; the campaign lint is unchanged.
- **Copy screen** (population: CleanCall, SAT and Hardness at head; SAT and Hardness at base): 255
  → 222 directed pairs, 36 gone and 3 new. All 36 gone pairs involve a deleted copy or one now
  reduced to a one-line citation. The 3 new pairs:
  - `exists_cleanInstall` and `exists_cleanEmit`, both directions (86%/80%). These are the two
    public 8-line wrappers over the shared private `clean_of_bridge`. They differ in the bridge
    and in the endpoint repair, and they replace four 600-character copies.
  - `Hardness.clFirst` reproducing `exists_first_halt_pos` (61%). At base `clFirst` paired at 61%
    with both first-halt copies (SAT's and Hardness's); those are now one public lemma. The
    statements differ (first entry to a fixed return state versus first halt), and the shared
    text is the six-line positivity cut.

  This is disclosed, not hidden copying. Judge whether it is acceptable.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate149-r4-2-cleancall-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
