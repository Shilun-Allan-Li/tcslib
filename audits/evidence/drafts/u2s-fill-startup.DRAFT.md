# Ch3–4 fill campaign — U2-S: the `k`-generic startup (`Turing.exists_selfStartupTMK`, `UniversalK.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (PR #102; the U2 statement gate
    `audits/u2-statements-findings.md`, PASS 0/0/2, resolutions `audits/u2-statements-resolutions.md`).
    The auditor's constructive outline of your target is the gate's "four admitted contracts",
    item 2;
  - **the prefix canonizer, generic in the canonizer** (PR #110, `UniversalStartup`):
    `Turing.prefixCanonTM` with `prefixCanon_start`, `prefixCanon_run` and `prefixCanon_complete`,
    promoted for you (user, 2026-10-15);
  - **the cleaned machine** `Complexity.LogProg.cleanTM` (`SpaceComplexity/Machines/Clean`, by
    Hydroxyi) with `cleanTM_run`. You cite it as it is, under the one import this brief
    authorizes (user, 2026-10-15);
  - **the API PRs** (the user's "Everything" rule, 2026-10-16: every definition your route reads
    has a published lemma): the specification API (PR #112), the core API (PR #116) and the
    brief-inventory API (PR #118, which gives the buffered composite's and the prefix machines'
    tape counts and state types for this brief);
  - the returning silent embedding `Turing.embedSilentRetTM` (`Build/Embed`), the catalog rows
    (`Build/Catalog`), the phase host and R2 seams (`Build/Seam`);
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/u2s-fill/`): the import overlay, the import probe and
    the screen population. Also the order list `briefs/orders/u2s-fill-startup.txt`, the base sorry
    set, the screen base and the pre-ship log (`audits/logs/u2s-fill-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/u2s-startup @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-u2s-startup.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #118** (⟨BASE-LEAN⟩). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree. `UniversalK.lean` is unchanged
  since #102 (279 lines). Every probe and measurement below was run there, against the olean
  snapshot of #118's replays (`oleans-lbapi2`).
- **In flight, merging after your base and invisible to it:**
  - B6 F5 (`Build/InputDevice`) and the B6 F3 continuation (`SpaceComplexity/WindowClock`);
  - the canonizer's continuation 6 (`CodeSimulator`);
  - G4's continuation (`Build/ZoneRebalance`), MIG-12 (`Build/CfgRecord`) if issued, and MIG-1's
    batches.

  Cite nothing they add.

## What this is

**U2-S, the startup of the `k`-generic universal machine** (`audits/evidence/u2/U2-design.md`
§2.2; design note §6, item 3).
- One target: **`Turing.exists_selfStartupTMK`**, frozen.
- **It states:** one machine `R` on `K + (k + 2)` work tapes and an exit, such that for every code
  `α` there are `T` and `B`, **depending on `α` only**, with this property on every input
  `pairEncode α w`. At `T`, and not before, `R` is at its exit with:
  - the input head at `1` and the output empty (and empty throughout);
  - tape `k` holding `tableBitsK` of the decoded machine;
  - tape `k + 1` holding its unary initial state from cell `2`;
  - every other tape blank and every head at `0`;
  - at most `B` cells visited.
- **Its consumers** are U2-U (`exists_selfUniversalK`, which composes you with H2-F) and B6's
  `Turing.exists_selfStartupTM`. The latter is already proved from you at `k = 1`
  (`SelfUniversal.lean`).
- **The fill gate** covers this target with H2-F and U2-U (design note §6).

**The published lemmas your route reads** (the core API, PR #116, the specification API, PR
#112, and the brief-inventory API, PR #118; ground rule 10):
- `FinTM.bufferedCompTM_k`, `FinTM.bufferedCompTM_State`, `universalPrefixTM_k`,
  `universalPrefixTM_State` and `prefixCanonTM_eq` (#118): the prefix canonizer's tape count and
  state type, for placing it in your host; `FinTM.VirtualTag_iff` (#118), if you cite
  `bufferedSecondCfg_run` directly;
- `serializeK_eq`, `pairEncode_eq`, `unaryFin_eq`: the captured word's shape;
- `MultiTapeTM.initCfg_eq` and `Cfg.init_*`: the starting configurations (for `cleanTM_run`);
- `MultiTapeTM.initCfg_with_q₀` and `MultiTapeTM.runFrom_with_q₀`: the restarted machine's start
  and runs, which are `cleanTM`'s (the same device serves a host composite `R`, whose `q₀` has no
  equation);
- `FinTM.computesFunInTime_iff` (with `computesInTime_iff`): a function computation, input by
  input;
- `FinTM.bufferedSecondCfg_*` with `tapeBlocks_left`/`_buffer`/`_right`: the prefix canonizer's
  configuration from `prefixCanon_run`;
- `embedSilentCfg_selected_tape`/`_pos`, `embedSilentCfg_cap`, `embedSilentCfg_unselected` and
  `embedSilentCfg_{state,inputPos,output}`: the capture's placement;
- `Cfg.inputSymbol_of_zero`/`_of_end`, `inputSymbolInner`, `Cfg.workTapeSymbols_eq`: the heads'
  readings;
- the catalog rows' `_run_ofCfg` contracts and `<row>_contract_*` field equations, and the layout
  facts (`fieldsTape_*`, `fieldOffset_zero`).

**Read first:**
- the target's docstring (`UniversalK.lean` 159–187), whose sketch is binding where this brief
  does not refine it. Where the two differ, this brief's route supersedes the sketch's
  "captured on a scratch tape" step.
- the U2 auditor's outline (findings, "The four admitted contracts", item 2);
- `UniversalStartup.lean`: `prefixCanonTM` and its three lemmas;
- `SpaceComplexity/Machines/Clean.lean` and `CleanSweep.lean`: `cleanTM`, `cleanTM_run`, and
  the public stage lemmas behind it (`sim_step_clean`, `stages_run`);
- `Build/Embed.lean`: `embedSilentCfg`, `embedSilentRetTM`, `embedSilentRetTM_run`,
  `embedSilentRetTM_visitedByTapeHead`.

**Pre-ship check** (maintainer, at the base, against `oleans-lbapi2`; `audits/logs/u2s-fill-preship.log`):
- **The import overlay** (`audits/evidence/u2s-fill/UniversalKOverlay.lean.txt`): your file with
  the one authorized import added after line 9. It elaborates with your target's sorry warning
  and the other two, and nothing else.
- **The import probe** (`audits/evidence/u2s-fill/U2SImportProbe.lean.txt`, 91 `#check`s): every
  public declaration this brief cites resolves from the overlay's import context. 0 errors,
  0 warnings. Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `UniversalK.lean:188` | `Turing.exists_selfStartupTMK` (frozen statement) |

Your regions:
- **(a) the import**, as your first edit: exactly
  `import TCSlib.Complexity.SpaceComplexity.Machines.Clean`, after line 9. No other import.
- **(b) the home**, the blank line 158, between the section header `/-! ## U2-S: the startup -/`
  (157) and the target's docstring (159): your `private` declarations. `private` only, and no
  `section`, `open` or `variable` that leaks past it. (`open Complexity.LogProg in` on a single
  declaration is fine.)
- **(c) the target's body**, the `sorry` on line 202.
- **(d) a flagged "Fill appendix (U2-S)" paragraph** before the target docstring's closing ` -/`
  (line 187).

Frozen: the module header, every other declaration, the statement, and every other file. The
maintainer updates the module's status text at integration.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The prefix canonizer:** `Turing.prefixCanonTM`, at a cleaned canonizer (below). Its
  configuration at every time from `3|α| + 4` on is `prefixCanon_run`'s exact formula, so
  **suffix independence comes from that formula**: no two-input comparison and no new locality
  lemma. Before `3|α| + 4` the composite is live, since it is live at `3|α| + 4`
  (`prefixCanon_start`) and halting is absorbing.
- **Cleaning the canonizer's scratch:** `Complexity.LogProg.cleanTM` around `E.canonizer.tm`,
  bundled as a `FinTM` (its `CleanSt` derives `Fintype` and `DecidableEq`).
  - `cleanTM_run` gives a halt with the canonizer's output, blank work tapes and heads at `0`, at
    a time depending on the input `α` alone.
  - Take the cleaned canonizer's time bound as a function of `|α|` by a finite maximum over the
    strings of that length, so it `ComputesFunInTime (fun α => serializeK (E.machine α))`, which
    is `prefixCanon_complete`'s hypothesis. Halting is absorbing, so the run is frozen past its
    own time.
  - Cite Hydroxyi's lemmas as they are; never edit his files. If a clause you need is missing,
    get it from `sim_step_clean` and `stages_run`. If they do not give it, escalate (ground rule 4).
- **Capture and placement:** `Turing.embedSilentRetTM` (R1′) runs the prefix canonizer on scratch
  tapes selected by an embedding, records its emissions on a scratch capture tape, and lands in
  its live return anchor after the halting transition (`embedSilentRetTM_run`,
  `embedSilentRetTM_visitedByTapeHead`). The first `k + 2` tapes stay blank and stationary.
- **Redistribution, clearing, rewinding:** the catalog rows, each through its `_run_ofCfg`
  contract (`copyTM`, `copyMapTM`, `clearTM`, `skipTM`, `skipBackTM`, `seekStartTM`,
  `seekEndTM`, `walkTM`), and `Turing.FinTM.timed_rewind` for the input head.
  - The captured word is `serializeK = pairEncode n.bits (unaryFin q₀ ++ tableBitsK tr)`.
  - Skip the doubled state count and the separator, place `unaryFin q₀` on tape `k + 1` from
    cell `2`, and place the table on tape `k`.
  - Clear the capture tape and the canonizer's code buffer (`bufferTape α`, at the virtual head
    `prefixCanon_run` names). Return every head to `0`; rewind the input head to `1`.
- **Composition:** the phase host (`phaseHostTM`, `phaseHostTM_run`) or R2 seams. **No new host.**
- **Leaves:** where no row serves (scanning the doubled pairs to the separator; splitting the
  self-delimiting `unaryFin` from the table, if no row does it), write a small finite
  controller. Its docstring says why no row serves it.
- **Promotion candidates** (list each in `REPORT.md`; notes only): the cleaned-canonizer bundle
  and its `ComputesFunInTime`; any leaf; any reusable redistribution lemma (B6 F6's startup and
  U2-E read the same serialization).

### The route (binding where it names a row)

1. **The cleaned canonizer.** `F' := ⟨_, _, { cleanTM E.canonizer.tm E.canonizer.tm.q₀ with
   q₀ := .init E.canonizer.tm.q₀ }, _, _⟩`: the cleaned machine restarted at its cleaning state,
   so its initial state is read without unfolding `cleanTM` (the #116 gate, finding 1). Prove
   `F'.ComputesFunInTime (fun α => serializeK (E.machine α)) τ'` through
   `FinTM.computesFunInTime_iff` and `FinTM.computesInTime_iff`. In the halted configuration
   its work tapes are blank, its heads are at `0`, and its virtual input position is a
   function of `α`.
2. **The prefix phase.** `prefixCanonTM F'` on `pairEncode α w`. Its first halt is at
   `3|α| + 4 + (F'`'s first halt on `α`): live before, by step 1 and `prefixCanon_run`. At the
   halt, `prefixCanon_run` gives the configuration exactly: the buffer holds `bufferTape α`, the
   canonizer block is blank, the input head is at `2|α| + 3`, and the output is
   `serializeK (E.machine α)`.
3. **Capture.** `embedSilentRetTM` of step 2 on the scratch tapes, the capture tape last: at the
   return anchor the capture tape holds `serializeK (E.machine α)` with its head one past it,
   and the physical output is `[]` throughout.
4. **Redistribution** (catalog rows, plus leaves where justified): the table to tape `k`, the
   unary state to tape `k + 1` from cell `2`, every scratch tape cleared, every head at `0`.
5. **Rewind** the input head to `1`. Enter `exit`, a fresh state reached exactly once, at `T`.
6. **`T` and `B`.**
   - `T` is the sum of the phase times, each a function of `α` (and `k`) only.
   - `B` follows from `Turing.MultiTapeTM.spaceUsed_le_mul_succ` at `T`, or from the phases'
     visited sets.
   - The first-exit clause holds because `exit` is fresh. Silence holds because R1′ suppresses,
     and every row is silent.

### Phases (for a partial; ground rule 9)

1. The cleaned canonizer and its `ComputesFunInTime` (step 1).
2. The captured prefix phase: steps 2–3, with the exact configuration at the return anchor.
3. Redistribution and rewind: steps 4–5.
4. The assembly, `T` and `B`: the target complete.

A partial may leave only the target open. Insert a helper only once it is proved.

## Gate guidance (binding)

- **The U2 statement gate** (`audits/u2-statements-resolutions.md`): the control varies with `k`
  alone. `E`, `α` and the suffix are data. `T` and `B` may depend on `α` only, and
  `E.canonizerTime` is arbitrary: nothing needs a computable bound on it.
- **The adversarial instances the auditor checked must stay true of your proof:**
  - `k = 0`: the table and the summary are tapes `0` and `1`, and every other tape is scratch;
  - an empty suffix `w = []`: the rewind and the input bound;
  - a canonizer with no work tapes: `cleanTM` at `k = 0`.

## Cited infrastructure (public and proved at the issue commit; all in `U2SImportProbe.lean.txt`)

The probe's 91 names, in six groups:
- the target and the scheme;
- the prefix canonizer and buffered composition;
- the cleaned machine;
- embedding, capture and composition;
- the catalog rows and the rewind;
- the brief-inventory API (#118).

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in the target.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `UniversalK.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed declaration: no renames, re-signatures,
   restatements or attribution edits.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated, including a cited contract that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** U2-U and U2-E (lines 233 and 271) stay sorried. Cite proved
   material; never re-prove it.
6. **Imports.** Exactly the one in region (a).
7. **One proof per shared argument.**
   - Never re-walk `prefixCanonTM`'s or `cleanTM`'s phases; cite their lemmas.
   - Never write a second capture or embedding host.
   - Never copy `UniversalStartup`'s private lemmas.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 279 lines).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each
   with a literal "Proof sketch"), and the target's axiom walk. A partial is expected and fine;
   an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas: the equation and field lemmas of the specification API (PR #112), the core API
      (PR #116) and the brief-inventory API (PR #118), and the landed lemmas the probe lists.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their existing lemmas (`runFrom_add`,
      `runFrom_succ_eq_step'`, `step_of_*`, and the renamings' field equations
      `Cfg.mapState_state`/`_inputPos`/`_workTapes`/`_workTapePos`/`_output` and
      `Action.mapState_*`, #118's round 2). Unfold `step` and `Action.apply`
      only for a leaf defined in your own file. `phaseHostTM`'s two-line table is read through
      `phaseHostTM_run`.
    - Your own file's definitions may be unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need. Never prove it by unfolding.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of another file.
    - Keep your new privates under the `ss_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 10 files (`audits/evidence/u2s-fill/screen-population.txt`): your file;
  `UniversalStartup` and `Universal`'s startup users (`UniversalInterpreter`); `Simulation`
  (buffered composition); `Build/Embed`, `Build/Catalog`, `Build/Seam`, `Build/Wrappers`; and
  Hydroxyi's `Machines/Clean` and `Machines/CleanSweep`.
- **The screen** is the declaration-keyed `audits/evidence/retrofit/copy-text-screen-v3.py`, on
  the repository paths.
- **The base**, at the issue tree, is `audits/logs/u2s-fill-screen-base.txt`: **654 declarations, 514 pairs, 151,065 characters**
  (MEASURED).

```sh
P=audits/evidence/u2s-fill
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:**
  - **`UniversalStartup`'s capture** (`universalCaptureTM` and its privates) and
    **`UniversalInterpreter`'s startup assembly**: the chapter-1 startup. Follow the pattern;
    never transcribe it.
  - **`cleanTM`'s stage lemmas:** cite them; never re-walk the sweeps.
  - **The catalog's `_run_ofCfg` proofs:** cite them; never restate them for your tapes.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor
  it. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/u2s-fill-startup.txt` (**92 modules**: the upstream
  closure of your owned file, with the authorized import, and of every module downstream of it,
  without the root `TCSlib`; downstream of it: `SelfUniversal` and the `TuringMachine` facade):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/u2s-fill-startup.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules** (`audits/logs/u2s-fill-base-sorries.txt`,
  one per declaration). Yours is `UniversalK`'s first, the target. Record the base list by name
  first, and report any difference.
- **Final checks:**
  1. `UniversalK`: zero errors; sorry warnings exactly U2-U's and U2-E's (for a partial, also the
     open declarations'); no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's.
  3. Re-run `U2SImportProbe.lean.txt`: 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for the target
  and every new private: within `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a
  complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL
  (base: 0 FAIL, 67 WARN over 79 files). No new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target, among them:
- U2-U and U2-E in your own file;
- H2-F (`Build/StepBlockForward`; in flight);
- `CodeSimulator`'s three;
- the record-table, input-device, NDHost, input-window and zone rows;
- the older specs in `Simulation`, `Composition`, `Build/Wrappers`, `Build/Loop`, `Encoding`,
  `Build/Primitives` and `ClassP/TimeConstructible`.

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 1/1, or the phase reached; the base hash and the ancestor check.
- [ ] The import as the first edit, and nothing else outside regions (b)–(d).
- [ ] Every new declaration with its role; each leaf and why no row serves it; the flagged
      appendix.
- [ ] `T` and `B` as functions of `α`, with the phase times.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **`FinTM` bundles its instances:** a `FinTM` around `cleanTM` needs `Fintype` and
  `DecidableEq` of `CleanSt S k`, which derive from the canonizer's (`E.canonizer.fintypeState`,
  `E.canonizer.decEqState`).
- **`initCfg` is `Cfg.init q₀`**: the restarted cleaned canonizer's initial configuration is
  `Cfg.init (.init q₀) α` by `MultiTapeTM.initCfg_with_q₀`, `cleanTM_run`'s starting point, and its
  runs are `cleanTM`'s by `MultiTapeTM.runFrom_with_q₀`. `cleanTM`'s own `q₀` has no published
  equation (Hydroxyi's file, cited as is).
- **`ComputesFunInTime` bounds by the input's length:** `cleanTM_run`'s time depends on the
  string. Take the maximum over the strings of each length (a `Finset.sup` over a finite type).
- **`prefixCanon_run` names the virtual head** through the canonizer's own `inputPos` (the buffer
  head sits at it minus one). Read the halted value off the cleaned run; it is a function of `α`.
- **`unaryFin q = replicate q true ++ [false]`** (self-delimiting). The target places it with
  `FinTM.bufferTape (unaryFin q₀) (p - 2)`: cells `0` and `1` blank.
- **`pairEncode x α = x.flatMap (fun b => [b, b]) ++ [false, true] ++ α`**: the code first, then
  the separator `false, true`.
- **`timed_rewind` is existential** (`r ≤ inputPos + 2`). The rewind is deterministic, from the
  fixed head `2|α| + 3` over the code's cells, so its time is a function of `α`. Get it from the
  run and keep it per `α`; do not take it from the existential.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
