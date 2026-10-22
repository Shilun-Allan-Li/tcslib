# Ch3–4 fill campaign — U2-S continuation 1: the `k`-generic startup (`Turing.exists_selfStartupTMK`, `UniversalK.lean`)

> **Megafill B, item 1 of 3** (cover brief `megafill-B.md`; addendum v2.4, Part 3). The
> preflight, the toolchain, the clone and the cache are done once for the whole queue. For this
> item: create its branch from the shared base (below), make your first edit, bootstrap your order
> list, then follow this brief. **Budget: 4 hours** from your branch's creation; then deliver this
> item's zip, partial if need be, and start item 2.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (the U2 statement gate; `campaign/items/u2/U2-design.md`
    §2.2);
  - **the first round's landing (PR #130):** 15 proved private `ss_` helpers in your file (the
    cleaned canonizer and its `ComputesFunInTime`, the suffix-uniform prefix halt, the restarted
    returning capture, the tape layout); the review
    `campaign/fills/u2s/reviews/startup-1/REVIEW.md` and its fill gate 48
    (`campaign/gates/48-u2s-startup-fill/`, PASS);
  - **the API PR that answers its F1 (PR #132; gate 50, PASS):**
    `FinTM.bufferedSecondCfg_workTapes_cast` / `_workTapePos_cast` in `Simulation`, the buffered
    composite's fields at its own index type; gate 50's note 8 ran the review's phase-2 goals
    under the seal through them
    (`campaign/gates/50-un-u2s-api/evidence/round1-fix/U2SPhase2TransportPositive.lean.txt`);
  - **the seam layout's contract** `Turing.exists_seamLayoutTM` (`Build/SeamLayout`, PR #124,
    statement gate 46 PASS), sorried at the base (its fill was delivered complete on 2026-10-22
    and lands after your base): the one redistribution of a
    captured serialization onto the step block's table and summary tapes, the review's phase-3
    route (i);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.4**: Part 1, the resources and the cache for the Mathlib roots only; **Part 3, the
    megafill**, under which this session runs), and the copy-text screen v3
    `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/u2s/inputs/u2s-fill-startup-cont1/`): the overlay
    (your file with the one new import), the import probe and the screen population; the order
    list `campaign/fills/u2s/orders/u2s-fill-startup-cont1.txt`, the base sorry set, the screen
    base and the pre-ship log (`campaign/fills/u2s/logs/u2s-fill-startup-cont1-*`).
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of
  `campaign/standards/fill-environment-addendum.md` and its Part 3): the preflight, the
  toolchain, the clone and the cache for the whole queue's Mathlib roots. If Lean cannot start,
  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/u2s-startup-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-u2s-startup-cont1.zip`, with
  `REPORT.md` and the full modified source; a `git format-patch` series against your base and a
  git bundle whose only prerequisite is your base; the bootstrap and final sweep logs and the
  axiom log; both screen outputs; and `SHA256SUMS`.
- **Checkpoint zips.** After each phase below, commit and write
  `fill-u2s-startup-cont1-cp<N>.zip` with the same contents as of that commit.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #137** (`2ff214c5`, #137's merge; #140,
  #138, #133, #134 and #136 merged since #132; of them only #133's `Build/InputDevice` is upstream
  of your file). **In flight, merging after it and invisible to it:** #139 (`Build/StepClock`),
  #143 (`Build/ZoneRebalance`), the seam layout's landing (`Build/SeamLayout`), MIG-12's fill
  (`Build/CfgRecord`); later in this session, on their own branches, F5 (`Build/InputDevice`,
  upstream of your file) and G4 (`Build/ZoneRebalance`); on another host, R (`NDCodeSimulator`),
  UN (`Diagonalization/NTimeHierarchy`) and the canonizer (`CodeSimulator`, upstream of your
  file). Cite nothing that merges after your base. Every probe and measurement below was run on
  the overlay against the olean snapshot `oleans-lg4c2` (the tip's merged-tree replay).
- **Your first edit makes your file equal to the overlay** (`UniversalKOverlay.lean.txt`): the one
  import below added after line 10. **Line numbers below are the overlay's** (591 lines: the
  target at line 500, its `sorry` at 514; `exists_selfUniversalK` at 545; `universalK` at 583).
- **The file's other two stubs,** `exists_selfUniversalK` (U2-U) and `universalK`, stay sorried.

## What this is

**U2-S, the startup of the `k`-generic universal machine**, continued. One target, frozen:
**`Turing.exists_selfStartupTMK`**: one machine `R` on `K + (k + 2)` work tapes and an exit such
that for every code `α` there are `T` and `B`, depending on `α` only, with this property on every
input `pairEncode α w`: at `T`, and not before, `R` is at its exit with the input head at `1`, the
output empty (and empty throughout), tape `k` holding `tableBitsK` of the decoded machine, tape
`k + 1` holding its unary initial state from cell `2`, every other tape blank, every head at `0`,
and at most `B` cells visited.

**Where it stands** (the first round's review, (c)): phase 1 complete (the cleaned canonizer
`ss_cleanCanonizer` and its contracts); phase 2 partial (`ss_capturedPrefix_run`: the restarted
capture's exact first return at `N(α) = 3|α| + 4 + t(α)`, chosen before the suffix, with silence
and a space bound, but its final configuration still written as `embedSilentCfg … (prefix run)`);
phases 3 and 4 open.

**Proved modulo, exactly:** `Turing.exists_seamLayoutTM` (sorried at your base). Cite its
statement; never its body.

**The published lemmas your route reads** (ground rule 10), the first round's list plus:
- **the composite at its own index type** (PR #132): `FinTM.bufferedSecondCfg_workTapes_cast`,
  `_workTapePos_cast`, with `FinTM.tapeBlocks_left`, `_buffer`, `_right`;
- **the canonizer's configuration:** `prefixCanonTM_eq`, `prefixCanon_run`;
- **the capture's placement:** `embedSilentCfg_selected_tape` / `_selected_pos`,
  `embedSilentCfg_cap`, `embedSilentCfg_unselected`, `embedSilentCfg_{state,inputPos,output}`;
- **the redistribution:** `Turing.exists_seamLayoutTM`, with `serializeK_eq`, `unaryFin_eq`
  (the captured word is `serializeK = pairEncode n.bits ((1^{q₀} 0) ++ tableBitsK tr)`, the
  layout's `pairEncode a ((List.replicate q true ++ [false]) ++ v)`), `StepBlock.summaryCells_eq`
  and `FinTM.bufferTape_of_neg` where you compare its summary form;
- **the cleanup:** `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `clearTM_run_ofCfg`; the input
  rewind `FinTM.rewind_heads` (or `timed_rewind`) over a private leaf of yours built from
  `FinTM.controlAction`;
- **composition and space:** `phaseHostTM_run`, `MultiTapeTM.spaceUsed_le_mul_succ`.

**Read first:**
- the target's docstring (its sketch is binding where this brief does not refine it);
- the first round's review, **(c)** ("Caveat for the continuation") and **(g)**;
- `exists_seamLayoutTM`'s statement: **the source head may start anywhere in `[0, |s|]`**, so the
  capture's head one past the word needs no rewind;
- gate 50's note 8 probe (above): the phase-2 rewrite under the seal.

**Pre-ship check** (maintainer, at the base;
`campaign/fills/u2s/logs/u2s-fill-startup-cont1-preship.log`):
- **The overlay** elaborates with exactly the file's three sorry warnings (lines 500, 545 and
  583).
- **The import probe** (`U2SCont1ImportProbe.lean.txt`, 111 `#check`s: the first round's 100 and
  the 11 names above that it lacked): 0 errors. Re-run it after your delivery.
- **The import** adds `Build/SeamLayout` to your closure and nothing else, and SeamLayout's
  closure does not contain your file.

## Owned regions and targets (modify these and nothing else)

| # | File:line (overlay) | Target |
|---|---|---|
| 1 | `UniversalK.lean:500` | `Turing.exists_selfStartupTMK` (frozen statement) |

Your regions:
- **(a) the import**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.Build.SeamLayout`, after the file's last import. No
  other import.
- **(b) the home**, between `/-! ## U2-S: the startup -/` and the target's docstring, holding the
  15 `ss_` helpers. You may restate or remove them (private; report each change). `private` only,
  and no `section`, `open` or `variable` that leaks past it (`open … in` on one declaration is
  fine).
- **(c) the target's body**, its `sorry`.
- **(d) for a partial only, a paragraph headed `**Implementation status.**`** before the target
  docstring's closing ` -/`: public-facing library text (what is proved and what is open, in
  mathematical terms; no campaign labels, dates or session narrative). The same holds for your new
  docstrings.

Frozen: the module header, every other declaration, the statement, and every other file.

### The route (binding where it names a row)

1. **Required first: two missing sketches** (gate 48's minor): give `ss_captureInitial` and
   `ss_capture_indices` a literal "**Proof sketch.**" paragraph.
2. **Restate the capture over the composite** (the review's caveat): state `ss_capturedPrefix_run`
   (or its successor) over `FinTM.bufferedCompTM universalPrefixTM F'` from the start, rewriting
   `prefixCanonTM_eq` before choosing the embedding, so that `ι` is typed at
   `Fin (bufferedCompTM universalPrefixTM F').k` and no dependent rewrite under `ι` is needed.
3. **Normalize the return** (phase 2's open half): at the return anchor, read the source block
   through `embedSilentCfg_selected_*`, the composite's fields through the **cast pair** and
   `tapeBlocks_*`, and `prefixCanon_run`'s formula: the code buffer holds `bufferTape α`, the
   cleaned canonizer's block is blank with heads at `0` (`cleanTM_run`), the capture tape holds
   `serializeK (E.machine α)` with its head at its length (`embedSilentCfg_cap`), the input head
   is at `2|α| + 3`, and the output is `[]`.
4. **Redistribute** by `exists_seamLayoutTM` with `src` the capture tape (its head at `r = |s|`),
   `tbl` tape `k` and `sm` tape `k + 1`. Its end is the target's tapes `k` and `k + 1` exactly
   (by `serializeK_eq`, `unaryFin_eq`), `src` cleared, all three heads at `0`, the input head and
   the output unchanged, at a time chosen before the configuration.
5. **Clear the code buffer** `bufferTape α`. Its head is the cleaned canonizer's virtual input
   position minus one, which `cleanTM_run` does not fix: **it may be `−1` (the left blank) or any
   cell up to `|α|`**. Bring it to `α`'s first cell (`skipTM_run_ofCfg`, then
   `skipBackTM_run_ofCfg`; at `−1`, one step right) and clear it (`clearTM_run_ofCfg`), heads to
   `0`. `α = []` is allowed.
6. **Rewind** the input head to `1` (your leaf, `FinTM.rewind_heads`). Enter `exit`, a fresh state
   reached exactly once, at `T`.
7. **`T` and `B`.** `T` is the sum of the phase times, each a function of `α` and `k` only; `B` by
   `MultiTapeTM.spaceUsed_le_mul_succ` at `T` or the phases' visited sets. The first-exit clause
   holds because `exit` is fresh; silence because R1′ suppresses and every row is silent.

Join the phases with `phaseHostTM_run` (or R2 seams). **No new host.**

### Phases (for a partial; ground rule 9)

1. The two sketches; the capture restated over the composite.
2. The normalized return (step 3).
3. The redistribution and the buffer's clear (steps 4–5).
4. The rewind, the assembly, `T` and `B`: the target.

## Gate guidance (binding)

- **The U2 statement gate:** the control varies with `k` alone; `E`, `α` and the suffix are data;
  `T` and `B` may depend on `α` only, and `E.canonizerTime` is arbitrary.
- **The adversarial instances that must stay true:** `k = 0` (the table and summary are tapes `0`
  and `1`); an empty suffix `w = []`; a canonizer with no work tapes; `α = []`; the code-buffer
  head at `−1`.
- **The seam layout's gate** (46, PASS): its time is chosen before the configuration; cite it as
  stated.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `UniversalK.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed public declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. **An API gap is an escalation:** if a fact about another file's definition has no
   published lemma, name the lemma in `REPORT.md` (the first round's F1 was unreported).
5. **No touching other sorries** (U2-U's and `universalK`'s stay). Cite proved material.
6. **Imports.** Exactly the one in region (a).
7. **One proof per shared argument.** Never write a second host, seam, embedding, prefix parser
   or layout machine; never re-walk `UniversalStartup`'s or `SeamLayout`'s privates. The
   input-rewind leaf is allowed.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and declaration
   counts.
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each
   with a literal "Proof sketch") and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).** Cite only declarations public at
    your base, and your file's own privates. **Never unfold a definition of another file**, and no
    definitional closure either; in particular read the buffered composite only through the cast
    pair and `tapeBlocks_*`, and `prefixCanonTM` only through `prefixCanonTM_eq`,
    `prefixCanon_run` and `prefixCanon_complete`. Cite Hydroxyi's `cleanTM` lemmas as they are;
    never edit his files. **Self-check:** the first round's 21-definition seal (its review, row 20)
    extended to every new definition you reach, with a control that fails under it, and an
    inspection of every `rw`/`simp`/`simpa`/`unfold` argument (a `simp` given a definition
    explicitly unfolds it even when sealed).
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows; cite no private declaration of
    another file; keep your new privates under `ss_`.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**.
- **The population** (`campaign/fills/u2s/inputs/u2s-fill-startup-cont1/screen-population.txt`,
  13 files): the first round's 10, and `Build/SeamLayout`, `Diagonalization/NTimeHierarchy`
  (UN's setup reads the same composite) and `NDCodeSimulator` (R's header capture).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths. **The base** is
  `campaign/fills/u2s/logs/u2s-fill-startup-cont1-screen-base.txt`, measured on the overlay:
  **674 declarations, 514 pairs, 151,065 characters** (MEASURED). Run the before screen after
  your first edit: it must equal the base.
- **No new cross-file pair** with an owned-file declaration on one side. **Known hazards:** the
  chapter-1 startup (`universalCanonTM`, `universalCaptureTM`), UN's and R's header captures.
  Follow their pattern, never transcribe it. A pair at 90% or more is a copy.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only** (addendum v2.4, fetched once for
  the queue;
  40 roots at the overlay); **never `lake build`**, and never the unfiltered `lake exe cache get`.
  Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap** (addendum Part 3, item 3.2) from
  `campaign/fills/u2s/orders/u2s-fill-startup-cont1.txt` (95 modules), after your first edit.
  **The base sorry-warning set has 33 entries in 14 modules**
  (`campaign/fills/u2s/logs/u2s-fill-startup-cont1-base-sorries.txt`); yours is the target.
- **Final checks:** `UniversalK`: zero errors, exactly the other two stubs' sorry warnings (for a
  partial, plus the open declarations'); every other module of the order list: zero errors, sorry
  warnings exactly the base's minus yours; the import probe re-run, 0 errors.
- **Axiom prints** for the target and every new private: within
  `[propext, Classical.choice, Quot.sound]`, plus the seam layout's `sorryAx`.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL
  (base: 0 FAIL, 63 WARN over 82 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The session's shared preflight and cache numbers (quoted from its logs), and this item's
      bootstrap.
- [ ] The target proved (or the phase reached); the base hash and the ancestor check; the
      checkpoint zips.
- [ ] The import as the first edit; nothing else outside regions (b)–(d); the two sketches.
- [ ] Every new or restated declaration with its role; the tapes chosen; the code-buffer cases.
- [ ] `T` and `B`, phase by phase.
- [ ] Promotion candidates and escalations (each API gap named), or "none".
- [ ] Rule 10: the declarations cited outside your file, the probe re-run, the seal test with its
      control, the inspection. Rule 11.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **The composite's index type.** Read its tapes at `i : Fin (bufferedCompTM M₁ M₂).k` through the
  cast pair; the older `bufferedSecondCfg_workTapes` at `Fin (M₁.k + (1 + M₂.k))` does not match
  there without unfolding (the first round's F1).
- **`Cfg.inputPos` is shifted by one,** and the buffer head is the source's virtual input position
  minus one (`tapeBlocks heads (inputPos − 1) …`).
- **`cleanTM_run` gives no input-position clause**: the code buffer's head is not fixed by it.
- **`summaryCells none (unaryFin q₀)` against `fun p => bufferTape (unaryFin q₀) (p − 2)`:** they
  agree at every cell, cell `0` by `FinTM.bufferTape_of_neg` (`StepBlock.summaryCells_eq`).
- **The simps field equations are pointwise** (`Cfg.mapState_*`, `embedSilentCfg_*`, `Cfg.init_*`):
  `funext` first, or the step closes by unfolding and the seal rejects it.
- **`prefix` is a reserved keyword**; do not name a hypothesis `prefix`.
- **A canonizer with no work tapes** is covered by `Fin 0` sums (`Finset.sup` over `Fin 0`), as in
  the first round's phase 1.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
