# Ch3–4 fill campaign — C1, the seam layout: the step block's layout from a captured serialization (`Turing.exists_seamLayoutTM`, `Build/SeamLayout.lean`)

<!-- DRAFT (maintainer), revised 2026-10-18 for the user's ruling (the word identities from a new
public module, PR #140). Before issue, after #140 merges: refresh the base and the in-flight list
(the base must contain #140; #132 and #138 may have merged), build the overlay (the file with the
one import), and re-measure on it against the then-current snapshot: the regions' lines, the
order list (BufferWords joins the closure), the Mathlib roots, the base sorries, the screen base
(add `TuringMachine/BufferWords` to the population) and the import probe (add the six lemmas).
-->

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (PR #124; the seam-layout statement gate, round 2 PASS
    0/0/1/11: `campaign/gates/43-seam-layout-statements/findings-r2.md`, resolutions
    `resolutions.md`, the maintainer's review `campaign/items/c1/seam-layout/gate46-review.md`
    with its carry-forward (c), which this brief repeats);
  - the round-2 evidence (`campaign/items/c1/seam-layout/r2/`): the consumer probe
    `SeamLayoutConsumerR2.lean.txt` and the route simulations `sim_route.py`, `sim-route.txt`
    (evidence, not proof);
  - **the API PRs** (the user's "Everything" rule, 2026-10-16): the specification API (PR #112),
    the core API (PR #116), the brief-inventory API (PR #118), the ND inventory API (PR #119) and
    its round 2 (PR #122: `FinTM.bufferTape_of_neg`, `MultiTapeTM.agreeOn_iff`);
  - **the buffer-word identities** (PR #140, the user's ruling of 2026-10-18 on this brief's word
    identities): the module `TuringMachine/BufferWords`, six `FinTM.bufferTape` lemmas, and its
    API gate `campaign/gates/57-buffer-words/`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.3**: Part 1, the resources and the cache, applies on every host; **the cache is fetched
    for your brief's Mathlib roots only**), and the declaration-keyed copy-text screen v3
    `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/c1/inputs/c1-fill-seamlayout/`): the import probe and
    the screen population. Also the order list `campaign/fills/c1/orders/c1-fill-seamlayout.txt`,
    the base sorry set, the screen base and the pre-ship log
    (`campaign/fills/c1/logs/c1-fill-seamlayout-*`).
- **Before anything else, run Part 1 of `campaign/standards/fill-environment-addendum.md`**: the
  preflight, with its stop rule (E-RES). If Lean cannot start, follow Part 2 exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-seamlayout @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-seamlayout.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below (the leaves, the word identities, the phase
  joins, the frame), commit and write `fill-c1-seamlayout-cp<N>.zip` with the same contents as of
  that commit (the final sweep may be your module's check only). Deliver the latest if the session
  ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #124** (`dac6b3b0`, #124's merge). The
  inputs commit adds no Lean change. Lines in this brief are those of that tree.
  `Build/SeamLayout.lean` has 120 lines there (1 public declaration, sorried). Every probe and
  measurement below was run there, against the olean snapshot of #124's replay
  (`oleans-lseam2`).
- **In flight, merging after your base and invisible to it:** #129
  (`Diagonalization/NTimeHierarchy`), #130 (`UniversalK`), #131 (`CodeSimulator`), #132
  (`Build/Primitives`, `Simulation`), the ruler device's landing (`Build/InputDevice`), and the
  fills of `NDCodeSimulator` (R, which cites your target), `Build/InputWindow`,
  `Build/ZoneRebalance`, `Build/CfgRecord` and `ClassNP/ExhaustiveReplay`. #132 changes
  `Simulation`, upstream of your file. Cite nothing they add.

## Parallel batches this round

None in `Build/SeamLayout.lean`. Your consumers: R (`exists_ndInterpreterCore`, filled in parallel
against your statement), U2-S's continuation (`UniversalK.exists_selfStartupTMK`, which may import
your module) and B5a's H1.

## What this is

**The step block's seam layout** (C1's route gap G2; the user's ruling of 2026-10-17: one public
contract, stated in its own PR and gated; and of 2026-10-18: a standalone fill proves it). One
target, frozen:
1. **`Turing.exists_seamLayoutTM`** (line 96): for distinct tapes `src`, `tbl`, `sm`, one machine
   takes `src` holding `s = pairEncode a ((List.replicate q true ++ [false]) ++ v)` with its head at
   `r ≤ |s|`, and `tbl`, `sm` blank with heads at `0`, to `tbl` holding `v` and `sm` holding the
   unary word from cell `2`, `src` cleared, the three heads at `0`, every other tape, head, the
   input position and the output unchanged, no emission, at **one time `T ≤ C·(|s| + 1)` chosen
   before the configuration** (depending on `a`, `v`, `q` and `r` only), and not before.

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in the target.

**Read first:**
- the target's docstring, whose eight-phase proof sketch is **binding**;
- gate 46's review, (c), and the round-2 resolutions;
- `Build/Seam`'s `phaseHostTM` and `phaseHostTM_run`, all their hypotheses;
- the five rows' `_run_ofCfg` contracts in `Build/Catalog`: `skipTM_run_ofCfg`,
  `skipBackTM_run_ofCfg`, `walkTM_run_ofCfg`, `transferTM_run_ofCfg`, `clearTM_run_ofCfg`;
- `StepBlock.lean`'s phase key and instances (lines 2202–2283): **the model for yours**, not a
  citation (that module is outside your closure).

**Pre-ship check** (maintainer, at the base, against `oleans-lseam2`;
`campaign/fills/c1/logs/c1-fill-seamlayout-preship.log`):
- **Your file** elaborates with exactly the target's sorry warning (line 96).
- **The import probe** (`SeamLayoutFillImportProbe.lean.txt`, 39 `#check`s): every public
  declaration this brief cites resolves from your file's import context. 0 errors, 0 warnings.
  Re-run it after your delivery.
- **The closure** (17 modules) contains none of `Build/StepBlock`, `CodeSimulator`, `UniversalK`
  and `NDCodeSimulator`.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `Build/SeamLayout.lean:96` | `Turing.exists_seamLayoutTM` |

<!-- ⟨LINES⟩ at issue: the regions' line numbers are the overlay's (the file with the one import
added, +1 below the imports); re-measure them and the pre-ship on the overlay. -->
Your regions:
- **(a0) the import**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.BufferWords`, after the existing imports. No other
  import.
- **(a) one home**, for your `private` declarations: the blank line **35**, after
  `namespace Turing` and before the target's docstring. `private` only, and no `section`, `open` or
  `variable` that leaks past one.
- **(b) the body**, the `sorry` on line **118**.
- **(c) for a partial only, a paragraph headed `**Implementation status.**` at the end of the
  target's docstring**, before its closing ` -/` (line 95). The closer ends a text line; put it on
  its own line after your paragraph. It is public-facing library text: what
  is proved and what is open, in mathematical terms, with no campaign labels (brief, gate, finding
  or escalation names), no dates and no session narrative. The same holds for the docstrings of
  your new declarations; provenance goes in `REPORT.md`.

Frozen: the module header and docstring, the imports other than (a0), the target's statement and
its docstring before (c), and every other file. The maintainer updates the module's status text at integration.

### Route (binding: the docstring's eight phases, with gate 46's carry-forward)

Write `m = List.replicate q true ++ [false]`, `h = 2|a| + 2` and `n = |s| = h + q + 1 + |v|`.
- **The phases, exactly as the docstring gives them,** composed by `Turing.phaseHostTM`: skip,
  skip back, the leaf `pairSkip`, the leaf `unarySplit`, the walk on `sm`, transfer, skip back,
  clear. **Seven dispatches**, and no extra rewinds after transfer or clear: clear's `done` is the
  exit `done`.
- **The time is closed form, fixed before `d`:** `T = 2n − r + 4h + 5q + 2|v| + 23`.
  - Per phase: `n − r + 1`, `n + 3`, `h`, `q + 3`, `q + 2`, `2|v| + 2`, `h + q + 3`,
    `2(h + q) + 2`.
  - **`C = 18`**, from `T ≤ 7n + 18` (slack `h + 3|v| + r`).
- **The last phase is not covered by `phaseHostTM_run`**, which needs a redirect at the end state.
  Run phase 8 through `MultiTapeTM.runFrom_mapState_of_agreeOn` (`StateRenaming`, public, in your
  closure) with the trivial guard (no redirect from phase 8's states), as `phaseHostTM_run`'s own
  proof does. Do not add a terminal halting phase: that costs an eighth dispatch and contradicts the
  docstring's time.
- **The joins.** Each of the seven rewraps `c'.mapState (fun _ => q')` as
  `c_next.mapState (Sigma.mk i')` (`Cfg.ext` and the `Cfg.mapState_*` fields).
- **The phase key and its instances:** follow StepBlock's precedent: an inductive key, an
  `abbrev` for the phase family, and `cases key <;> dsimp [Ph] <;> infer_instance` for `Fintype`
  and `DecidableEq`.
- **Silence at every time `u ≤ T`.** The rows' `_run_ofCfg` contracts give the output only at the
  endpoint. Derive the per-time clause from `MultiTapeTM.output_prefix` (`Finite`) sandwiched by
  the endpoint equality, or from table-level silence. The leaves' contracts state it themselves.
- **The leaves**, private, each with a framed contract: an exact time, no earlier `done`, every
  other tape, head and the input position unchanged, and silence.
  - `pairSkip` remembers only the first bit of each pair; its separator step both moves and
    enters `done`, giving exactly `h` steps.
  - `unarySplit` writes `false` on `sm` with that head staying, and blanks `src` at `h + q` while
    moving right. The unary terminator is not restored on `src`.
  - Each leaf's docstring says why no row serves it (as the target's docstring does).
- **The word identities** — `s.drop r`, `s.take (h + q)`, the cells of `m` and `v`, and the
  blanks — through `Turing.pairEncode_eq` and **`TuringMachine/BufferWords`** (the user's ruling,
  PR #140): `FinTM.bufferTape_append_shift`, `_append_mid`, `_drop`, `_take`,
  `_eq_none_of_not_mem` and `_unary`, with `Simulation`'s `bufferTape_nat`, `_left`, `_eq` and
  `_of_neg`. Not `serializeK_eq` (outside your closure), and never `StepBlock`'s private copies.
  The module's gate probe (`campaign/gates/57-buffer-words/evidence/BufferWordsProbe.lean.txt`)
  derives the unary state's cells (terminator included), the table's cells from its first cell,
  `s.drop r`, `s.take n`, the blanks past `s` and a separator cell from them alone, sealed: **a
  reference, not a citation** (its examples are probe-local).
- **The frame.** Prove the full triple `Function.update` endpoint, not just the three tapes: R
  relies on it for the bank fields, including an installed choice tape. Prove `inputPos`
  unchanged.
- **Natural-number casts:** `(r : ℤ) + ((n − r : ℕ) : ℤ) + 1 = n + 1` needs `r ≤ n`
  (`push_cast`, `omega`).

### Checkpoints (for a partial; ground rule 9)

1. The two leaves, with their framed contracts.
2. The word identities.
3. Phases 1–7 joined by `phaseHostTM_run`, with the time ledger.
4. Phase 8 by the agreement transport; silence; the frame; the target proved.

## Gate guidance (binding)

- **The seam-layout gate, round 2** (PASS): `T` is chosen before the configuration (finding 2 of
  round 1); the eight phases and the exact time are the binding sketch (finding 1).
- **Edge cases that must stay true of your proof** (the gate's notes and the rows):
  - `r = n` (skip over `[]`, 1 step);
  - `q = 0` (the walk over `[false]`, 2 steps; `unarySplit` in 3);
  - `v = []` (transfer in 2; cell `n` is the right blank);
  - `a = []` (`h = 2`);
  - the auditor's four instances, with times 37, 34, 66 and 49;
  - an extra populated tape with a negative head position, preserved;
  - all-`false` table bits.

  Prove them as `example`s in a scratch file, or report them checked by evaluation of your
  closed-form `T`; they are sanity checks, not deliverables.

## Cited infrastructure (public and proved at the issue commit; all in `SeamLayoutFillImportProbe.lean.txt`)

The probe's names: the target; the five rows' `_run_ofCfg` contracts; `phaseHostTM` and
`phaseHostTM_run`; `MultiTapeTM.runFrom_mapState_of_agreeOn`, `MultiTapeTM.AgreeOn` and
`agreeOn_iff`; `MultiTapeTM.output_prefix`; `pairEncode`, `pairEncode_eq`, `length_pairEncode`;
`FinTM.bufferTape` with `_nil`, `_nat`, `_left`, `_eq`, `_of_neg`, `_append`; `Cfg.ext`; the model's
step, run, action and `Cfg.mapState` lemmas; `Cfg.workTapeSymbols_eq`.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `Build/SeamLayout.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target.
3. **No new public declaration.** The leaves are private; a generic helper you would publish is a
   promotion candidate, in `REPORT.md`.
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and continue with every item that does not depend on it.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly one added, `TuringMachine/BufferWords` (region (a0); it imports
   `Simulation` only). Your closure must stay free of `Build/StepBlock`, `CodeSimulator`,
   `UniversalK` and `NDCodeSimulator`, so that U2-S's continuation can import your module.
7. **One proof per shared argument.** Never write a second seam, phase host, row or embedding.
   Compose the rows' contracts; never re-walk a row's trace.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 120 lines; 1 public, 0 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch"), and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and no definitional closure either (a `rfl`,
      `exact`, `show`, `decide` or `simp` step that closes only because another file's definition
      reduces; `FinTM.bufferTape` included). Read every definition through its published lemmas.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their lemmas. Unfold `step` and `Action.apply` only for a
      leaf defined in your own file; `phaseHostTM`'s table is read through `phaseHostTM_run` and
      the agreement transport.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check:** a seal test (a scratch copy of your module with `attribute [local
      irreducible]` on every other-file definition your proofs mention, which must still
      elaborate) and an inspection of every `rw`/`simp`/`simpa`/`unfold` argument in your diff.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows (`copyTM_run`, `transferTM_run`, `clearTM_run`,
      `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`); the `_run_ofCfg`
      forms above are the framed ones.
    - Cite no private declaration of another file.
    - Keep your new privates under the `sl_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 8 files
  (`campaign/fills/c1/inputs/c1-fill-seamlayout/screen-population.txt`): your file; the files the
  route cites (`Build/Catalog`, `Build/Seam`, `StateRenaming`, `Simulation`); and the hazards
  `Build/StepBlock` (its private word identities and its phase key), `UniversalStartup` (the
  chapter-1 startup) and `Build/Primitives` (the pair extractor, next to `pairSkip`).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/c1/logs/c1-fill-seamlayout-screen-base.txt`: **858 declarations, 1,112 pairs, 406,659 characters**
  (MEASURED).

```sh
P=campaign/fills/c1/inputs/c1-fill-seamlayout
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed: the word identities are cited from `BufferWords`, not copied.
- **Known hazards:** `StepBlock`'s word identities (now public in `BufferWords`: cite those) and
  its phase-key instances (follow, never transcribe); `FinTM.pairExtractTM`'s pair reading
  (`Build/Primitives`) against `pairSkip`. A pair at 90% or more is a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only** (addendum v2.3, items 2–4);
  **never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check. ⟨ROOTS: the Mathlib roots' count at the
  overlay⟩
- **Bootstrap once** from `campaign/fills/c1/orders/c1-fill-seamlayout.txt` (**81 modules**: the
  upstream closure of your owned file and of every module downstream of it, without the root
  `TCSlib`; one module is downstream of it, the `TuringMachine` facade).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < campaign/fills/c1/orders/c1-fill-seamlayout.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules**
  (`campaign/fills/c1/logs/c1-fill-seamlayout-base-sorries.txt`). Yours is `Build/SeamLayout`'s
  one. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `Build/SeamLayout`: zero errors, no sorry warning (for a partial, exactly the open
     declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours.
  3. Re-run `SeamLayoutFillImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the target and every new private: within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 30 WARN over 38 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The preflight's numbers (addendum v2, Part 1).
- [ ] The target proved, or the checkpoints reached; the base hash and the ancestor check; the
      checkpoint zips written.
- [ ] Every new declaration with its role; the two leaves and why no row serves each; the status
      paragraph, if a partial.
- [ ] The time ledger, phase by phase, and `C`.
- [ ] The word identities, as the ruling prescribes.
- [ ] The edge cases checked.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file, the probe re-run, the seal test and the
      inspection. Rule 11: a grep of your diff for the six R3 rows and for other files' private
      names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **Read each row's precondition exactly as its `_run_ofCfg` states it.** The docstring's
  per-phase endpoints (the skip's head at `n + 1`, skip back's at `0`, transfer's return to
  `h + q + 1`) were checked against the rows' contracts by the gate (notes 4–6) and the review's
  simulations; a mismatch is an escalation, not a license to re-route.
- **`phaseHostTM_run`'s guard must hold strictly before each phase's `T`,** and it has no redirect
  at the last phase's end: hence phase 8's agreement transport.
- **`FinTM.bufferTape w` is blank at negative cells,** and cell `p ≥ 0` reads `w[p]?`, so it is
  blank from `|w|` on (`bufferTape_nat`, `bufferTape_of_neg`).
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
