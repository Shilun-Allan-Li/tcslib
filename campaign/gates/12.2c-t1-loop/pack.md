# External audit pack — 12.2c tranche T1, batch 11A: one loop host, shared run facts

Campaign: Arora-Barak chapters 3-4. **12.2c** is the maintainer's refactor
window, run as three tranches (`AroraBarakChapters3-4Plan.md` §4e). Each
tranche gets a PR the user merges and **its own audit gate**. This batch
covers two items:

- **12.2c item 11.** RB4 left `Build/Loop.lean` with two hosts. The
  forwarding host `emLoopHost` re-proved the original `loopHost_*` phases
  inline (ledger row "RB4's inlined residue", acknowledged by the user).
  Per-phase Z5 transfer cannot merge them: the anchor-return phase runs in
  body control from `t = 0`, where the hosts differ (RB5's kernel-checked
  counterexample).
- **CH7-D2, library half.** The run facts that ch7's `EmitIterEmbed`
  re-proved, and that Loop held as private copies, get one public home in
  `Finite.lean`.

The change is PR #20 (`integrate/12.2c-t1-loop`): Codex commit `bfa5fecf` on
base `b4be0717`, plus the maintainer's records commit. **Statements are
frozen.** The gate closes on zero blockers and zero majors. The duplication
rule (`audits/TEMPLATE.md`, failure mode 5) is in force.

## What changed (verify)

- **`Finite.lean`**: three new public lemmas, the brief's Task 1 text
  verbatim, after `spaceUsed_le_mul_succ`:
  - `Turing.MultiTapeTM.step_output_prepend`;
  - `Turing.MultiTapeTM.runFrom_output_prepend`, proved through
    `runFrom_comm_of_step`;
  - `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`.

  Also one *Main results* bullet. The existing 14 declarations are
  unchanged.
- **`Build/Loop.lean`**:
  - **One parametric host.** `loopHostM body F anchor forward findMode`, with
    the body dispatch in `loopBodyDispatch`. `loopHost` and `emLoopHost` are
    `abbrev`s at `forward := false` and `true`.
  - **Generalized phases.** The 14 fuel and controller phase lemmas are
    generalized over `forward` with their proofs unchanged.
  - **Body phase once.** It is proved by `loopHost_body_run`, with
    `loopBodyImage` as the mode-dependent image.
  - **Shared anchor return.** `loopHost_anchor_return` is generalized and
    serves both hosts.
  - **Deletions and merges.** The forwarding family's inlined re-proofs are
    deleted. The two rewinds are merged into `loopHost_payload_scan` through
    the generic `loop_scan_left`.
  - **Removed copies.** Loop's private `loop_live_prefix`,
    `emLoop_step_prefix` and `emLoop_run_prefix` are deleted in favour of the
    Finite lemmas. RB5's `local notation "emCall_state_run"` alias is
    removed. `loop_input_move_le` and `loop_input_run_le` are deleted in
    favour of the public `timed_input_bound`.
  - **Counts.** Privates go from 190 to 185 (12 deleted, 7 added), and 17
    private statements change, as the brief lists.
- **Frozen surface.** All 8 Loop public statements are byte-identical, and
  seven are identical in full. In `exists_emitLoopTM` only the sanctioned
  three lines change: two calls retargeted to the generalized lemmas, and the
  docstring token `emLoop_run_prefix` → `runFrom_output_prepend`.

## Brief for the auditor

1. **Freeze.** From the attached base and after sources, confirm each claim
   under "Frozen surface". Confirm also that the 17 changed private
   statements change only by the `forward` parameter or the documented
   generalizations, and that no consumer outside the two files was edited.
2. **The three public run facts.** Blind-restate them. Are they true, minimal
   and correctly homed? `Finite.lean` holds raw-layer additions, since the
   vendored `Deterministic.lean` stays untouched. Do they subsume
   `EmitIterEmbed`'s five, which become citations in tranche T2?
3. **The parametric host.** Verify that both `abbrev` instances are exactly
   the old hosts' transition tables on every control case. The maintainer's
   pre-ship probe checked this; it is attached. Verify that
   `loopHost_body_run` is the only place the modes differ, and that no
   `emLoopHost_*` lemma restates a generalized one.
4. **The rewind merge.** Is `loopHost_payload_scan` with its table hypothesis
   `htr` a genuine generalization of both old rewinds? Is `loop_scan_left` a
   sound generic scan lemma?
5. **Duplication (failure mode 5).** The screen over Loop, Finite,
   Deterministic, EmitIterEmbed and Catalog goes from 673 pairs / 280,141
   characters to 540 / 223,798.
   - Loop→Loop goes from 110 to 65 pairs, Loop→Catalog from 115 to 87, and
     Catalog→Loop from 161 to 100. Every pair on the brief's removal
     checklist is gone. Census pass 4 for Loop goes from 98 to 92.
   - There are nine new pairs:
     - three cross-file **carry-overs** at lower shares (a renamed source
       whose partner paired with the absorbed declaration at baseline);
     - four in-file pairs at 52–65%;
     - **E1**, two pairs: Finite's `runFrom_state_ne_none_of_le` ↔ Catalog's
       pre-existing private `f2_loop_live_prefix`, at 100% and 92%.

   E1 was accepted by the maintainer: the Catalog private is an existing
   copy, already recorded for conversion to a citation in tranche T3, and the
   new public home is the fix. Rule on the carry-overs, the in-file pairs
   and E1 under failure mode 5. The pair-by-pair comparison is
   `audits/logs/12.2c-t1-loop-screen-delta.txt`.
6. **Downstream.** 204 modules, 0 errors. The sorry sets are identical to
   base: 55 = 55 over the 194 modules the C1 integration log covers, and 0 in
   the remaining ten. Confirm from the logs.
7. **Docstrings.** Report any docstring made false. One is known: the
   historical docstring of `loopHost_contracts` still names the deleted
   `loopHost_body_capture`, and the brief told the batch to leave it.
8. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Integrity.** The zip's `SHA256SUMS` is OK (the zip is not attached). The
  C shim is excluded and unreferenced. The integrated files are
  byte-identical to the delivered sources.
* **Freeze** (`audits/logs/12.2c-t1-loop-freeze.txt`).
* **Replay** (`…-replay.log`): 204 modules, 0 errors.
* **Axioms** (`…-axioms-{base,after}.log`, from the probe
  `…-axioms.lean.txt`): the 22 pre-existing prints are byte-identical after,
  and the three new lemmas are at `[propext, Quot.sound]`. No `sorryAx`.
* **Lint** (`…-stylelint.log`): 0 FAIL.
* **Screens and census** (`…-screen-{before,after,delta}.txt`,
  `…-census.txt`):
  - the screen script and the sources are attached: Loop and Finite at base
    and after, the unchanged Deterministic, EmitIterEmbed and Catalog once;
  - the census generator `audits/evidence/retrofit/r1-public-proof-screen.py`
    is attached.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/12.2c-t1-loop-findings.md`.
