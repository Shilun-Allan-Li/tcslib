# Ch3–4 fill campaign — H2-F: the step block's forwarding round loop (`Turing.StepBlock.exists_forwardLoopTM`, `Build/StepBlockForward.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **H2, the step block** (`Build/StepBlock`, PR #88): `Turing.StepBlock.roundTM` with its exact
    effect `roundTM_effect`, the visited sets `roundTM_visited`, `roundTM_iterate` and
    `roundTM_firstExit_unique`;
  - **its clocked loop form H2-L** (`Build/StepBlockLoop`, PR #94), the model for this fill;
  - **your target as a gated statement** (PR #102; the U2 statement gate
    `audits/u2-statements-findings.md`, PASS 0/0/2, resolutions `audits/u2-statements-resolutions.md`).
    The auditor's constructive outline of your target is the gate's "four admitted contracts",
    item 1.
  - the macro-step lockstep `Turing.Lockstep` (`Build/Contract/Basic`), with `runFrom`, `cut` and
    `locate`;
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/h2f-fill/`): the import probe and the screen
    population. Also the order list `briefs/orders/h2f-fill-forwardloop.txt`, the base sorry set,
    the screen base and the pre-ship log (`audits/logs/h2f-fill-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/h2f-forwardloop @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-h2f-forwardloop.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #109** (`e5fcd8ee`). The inputs commit adds
  no Lean change. Lines in this brief are those of that tree. `Build/StepBlockForward.lean` is
  unchanged since #102 (132 lines). Every probe and measurement below was run there, against the
  olean snapshot of #109's replay.
- **In flight, merging after your base and invisible to it:** the canonizer's continuation 5
  (`CodeSimulator`), B6 F3 (`WindowClock`), G4's fill (`ZoneRebalance`), and MIG-1's batches.
  Cite nothing they add.

## Parallel batches this round

None in `Build/StepBlockForward.lean`. U2-S (`UniversalK`'s startup) may be briefed in parallel; it
does not use your target. U2-U (`exists_selfUniversalK`) composes U2-S with your target after both
land.

## What this is

**H2-F, H2's unclocked loop form** (`machine-library-design.md` §14, the H2 row;
`audits/evidence/u2/U2-design.md` §2.2).
- One target: **`Turing.StepBlock.exists_forwardLoopTM`**, frozen.
- **It states:** one finite `(k + 2)`-tape machine `L` per `k`, simulating any `k`-tape binary
  table in macro-step lockstep through the defined encoding `forwardLoopCfg`, with each simulated
  emission forwarded, a per-step cost `≤ 50 · (|tableBitsK M.tr| + 1) + C`, and a per-head space
  ledger.
- **Its consumers** are U2-U, U2-E, B6's `U₀` (at `k = 1`) and U-1. With U2-S, it is the last
  admission between the two-tape universal machine and the `f log f` time hierarchy (U2 design
  note §6).
- **The fill gate** covers this target with U2-S and U2-U (design note §6).

**Read first:**
- the target's docstring, whose proof sketch is binding where this brief does not refine it;
- the U2 auditor's outline (findings, "The four admitted contracts", item 1);
- `Build/StepBlock.lean`: `exit` and `roundTM` (lines 2195–2222), `Rep` (3037),
  `roundTM_effect` (3116), `roundTM_visited` (3269), `roundTM_firstExit_unique` (3457),
  `summaryEmit`/`summaryEmit_none` (121, 167), `summaryCells` (1999), `summaryTape` (188);
- `Build/Seam.lean`: the release adapter `seamReleaseTM` and its run lemmas (705–825), and the
  phase host `phaseHostTM`/`phaseHostTM_run` (832–900);
- `Build/StepBlockLoop.lean`, how H2-L consumes `roundTM_effect` round by round
  (`loopRoundTime`, `loopOrbit_round`). **It is the model, not a citation:** your module does not
  import it, and its composition host (the counter loop) is clocked and outside your import
  context.

**Pre-ship check** (maintainer, at the base, against `oleans-lwalk`;
`audits/logs/h2f-fill-preship.log`):
- **The import probe** (`audits/evidence/h2f-fill/H2FImportProbe.lean.txt`, 41 `#check`s): every
  public declaration this brief cites resolves from your file's import context (`Build/StepBlock`
  and `Build/Contract/Basic`, and through them `Build/Seam`, `Build/Embed` and `Build/Catalog`; not
  `Build/CounterLoop` or `Build/StepBlockLoop`). 0 errors,
  0 warnings. **No import is needed or allowed.** Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `Build/StepBlockForward.lean:111` | `Turing.StepBlock.exists_forwardLoopTM` (frozen statement) |

Your regions:
- **(a) the home**, the blank line 76, between `forwardLoopCfg` (66–75) and the target's docstring
  (77): your `private` declarations. `private` only, and no `section`, `open` or `variable` that
  leaks past it.
- **(b) the target's body**, the `sorry` on line 128.
- **(c) a flagged "Fill appendix (H2-F)" paragraph** before the docstring's closing ` -/` (line
  110).

Frozen: the module header, `forwardLoopCfg`, the statement, and every other file. The maintainer
updates the module's status text at integration.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The round is the step block `roundTM k`, cited through its contracts:** `roundTM_effect`
  (exact time `0 < T ≤ 50 · (|table| + 1)`, the exit, `Rep` of the stepped configuration, the
  summary cell, the strict cut, silence, the head bounds), `roundTM_firstExit_unique` and
  `roundTM_visited`. **Never re-walk the block's phases.**
- **Composition: the release adapter inside the phase host.** The block's live exit is its
  entry (`exit k true = ⟨.entry, ()⟩`), so a host that dispatches on the block's arrival at
  `entry` would fire at time `0`. The release adapter `seamReleaseTM (roundTM k) ⟨.entry, ()⟩`
  is the landed answer: its fresh start `Sum.inl ()` executes the entry's action unconditionally,
  and its first re-arrival at `Sum.inr ⟨.entry, ()⟩` or `Sum.inr ⟨.halt, ()⟩` is a positive-time
  event (`seamReleaseTM_runFrom_pos`, `seamReleaseTM_visitedByTapeHead`). Make it one phase of
  `phaseHostTM`, the leaf the other:
  - the block phase redirects `Sum.inr ⟨.entry, ()⟩` to the live leaf and `Sum.inr ⟨.halt, ()⟩`
    to the halting leaf, and nothing else (in particular not `Sum.inl ()`);
  - the live leaf's last state redirects to the block phase's fresh state, which is `L`'s
    `entry`;
  - `phaseHostTM_run` gives each phase's prefix and its dispatch; its `hguard` at the block phase
    is the block's cut (`roundTM_effect`), with time `0` at `Sum.inl ()`.

  No second host, seam or loop. An equivalent composition from the same public hosts
  (`seamCompTM₂` for the two exits, say) is fine if `REPORT.md` says why.
- **The lockstep:** `Turing.Lockstep`'s three fields are your target's first conjunct. The
  iteration over rounds is `Lockstep.runFrom`'s, so you prove one round, not a run.
- **The space ledger:** `roundTM_visited` per round, summed by
  `MultiTapeTM.visitedByTapeHead_add_subset`, with `Lockstep.locate` to place a target time inside
  a round.
- **The one leaf you write:** the forwarding leaf on the summary tape (`summaryTape k`).
  - Read cell `0`; if it holds a bit, emit it; blank the cell.
  - Then enter the block's entry, or halt, according to the block's exit.
  - It is a small finite controller (`tapeAction`, `inputMoveAction`, `step_of_tapeAction_write`,
    `step_of_inputMoveAction`) and moves no head.
  - Its docstring says why no public row serves it: the step block is silent, and H2-L does not
    emit.
- **Promotion candidates** (list each in `REPORT.md`; notes only): the leaf, and any generic
  "block + leaf" round lemma.

### The route (binding where it names a row)

1. **The reset invariant.** For a live `c`, the block-control part of
   `forwardLoopCfg entry M c` is a `Rep` of `{c with output := []}`:
   - the summary cell is blank;
   - the unary state word is on tape `k + 1`;
   - both auxiliary heads are at `0`;
   - the physical output is unconstrained (`Rep` leaves it free, as the auditor notes).

   Prove this once, as a private lemma.
2. **One round.** `roundTM_effect` gives the block's first exit after `T`, at a `Rep` of
   `a.apply {c with output := []}`, silent before, with summary cell
   `summaryEmit none a.output = a.output` (`summaryEmit_none`). The block leaves the physical
   output as it was.
3. **The leaf.**
   - One step: read cell `0` of the summary tape (the head is there, by `Rep`), write a blank,
     and emit what was read: `a.output`. The live leaf then dispatches to `entry`; the halting
     leaf's step halts.
   - The result is **exactly** `forwardLoopCfg entry M (M.step c)`, output included: the block
     left the physical output `c.output` (silence), the leaf appended `a.output`, and the
     successor word is already empty on a halting transition.
4. **The lockstep fields.**
   - **`step`:** `cost c := T + 3` for a live successor (the block's `T`, the dispatch to the
     leaf, the leaf's step, the dispatch back) and `T + 2` for a halting one, with `T` the
     block's round time (unique, `roundTM_firstExit_unique`; choose it once per `c`). For a
     halted `c` the cost is arbitrary.
   - **`exit`:** the encoding of a halted `c` is halted, by `forwardLoopCfg`'s state.
   - **`inner`:** the block's cut and the leaf's.
5. **The bounds.**
   - `0 < cost c`, since `T > 0`.
   - `cost c ≤ 50 · (|table| + 1) + C`, with `C = 3` in the shape above.
   - The ledger: the mirrored heads visit only `M`'s cells (`roundTM_visited`, with the block's
     mirrored-head clause), and the auxiliary heads stay within the per-round bound. The leaf moves
     no head.

### Phases (for a partial; ground rule 9)

1. The reset invariant and the leaf's run lemma.
2. One round: the lockstep's `step`, `exit` and `inner`.
3. The bounds and the space ledger: the target complete.

A partial may leave only the target open. Insert a helper only once it is proved.

## Gate guidance (binding)

- **The U2 statement gate** (`audits/u2-statements-resolutions.md`): H2-F is the right public host
  boundary. Its control varies with `k` alone; the table, the state count and the input are data.
  Do not specialize the machine to a table.
- **The adversarial instances the auditor checked must stay true of your proof:**
  - `k = 0`: no mirrored tapes, the two auxiliary clauses substantive;
  - an already halted source;
  - an unreachable configuration with nonempty output: only the current emission's summary is
    reset, and the physical prefix survives.

## Cited infrastructure (public and proved at the issue commit; all in `H2FImportProbe.lean.txt`)

The probe's 41 names, in four groups:
- the target and its encoding;
- the step block;
- the lockstep and the run calculus;
- composition and leaves.

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in the target.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `Build/StepBlockForward.lean`. List every
   new declaration with its role.
2. **Statement freeze** over the target, `forwardLoopCfg` and every landed declaration: no renames,
   re-signatures, restatements or attribution edits.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated, including a cited contract that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged (`Build/StepBlock`, `Build/Contract/Basic`). No import may be added.
7. **One proof per shared argument.** Never re-walk `roundTM`'s phases; never write a second phase
   host, seam or lockstep iteration (`Lockstep.runFrom` is the iteration).
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 132 lines; 2 public, 0 private).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each with
   a literal "Proof sketch"), and the target's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base.**
    - Cite only declarations public at your base, and your file's own privates.
    - Do not rely on unfolding `roundTM`'s phase tables. Use its contracts. `phaseHostTM`'s
      two-line table is the exception, as `phaseHostTM_run`'s proof shows.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of `Build/Catalog`, `Build/StepBlock` or `Build/StepBlockLoop`.
    - Keep your new privates under the `fl_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 11 files (`audits/evidence/h2f-fill/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/StepBlock`, `Build/Contract/Basic`, `Build/Seam`,
    `Build/Embed`, `Simulation`, `Finite`;
  - the clocked loop form `Build/StepBlockLoop`, the model and the main hazard;
  - `CodeSimulator`, whose H1 hosted verdict also composes `roundTM`;
  - the consumers `UniversalK` and `SelfUniversal`.
- **The screen** is the declaration-keyed `audits/evidence/retrofit/copy-text-screen-v3.py`, on
  the repository paths.
- **The base**, at the issue tree, is `audits/logs/h2f-fill-screen-base.txt`: 404 declarations
  screened, 100 copy pairs, 20,861 characters reproduced (MEASURED). Two base pairs have your
  file on one side, `forwardLoopCfg` reproducing `Simulation`'s `rightCfg` and `leftCfg` at 52%:
  frozen, not yours, and not new.

```sh
P=audits/evidence/h2f-fill
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:**
  - **H2-L's loop proofs** (`Build/StepBlockLoop`: `loopTM_run`, `hostedLoopTM_run` and their
    privates). Follow their pattern for "block, then a phase, then the block again", and do not
    transcribe them. A pair at 90% or more is a copy: report it, and factor it if it is in your
    file.
  - **H1's hosted verdict** (`CodeSimulator`: `h1HostedVerdict_effect` and its family): the same
    caution.
  - the step block's own run lemmas: cite `roundTM_effect`; a pair with `StepBlock`'s privates
    means the block was re-walked.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor
  it. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/h2f-fill-forwardloop.txt` (**79 modules**: the upstream
  closure of your owned file and of every module downstream of it, without the root `TCSlib`; 3
  modules are downstream of it: `UniversalK`, `SelfUniversal` and the `TuringMachine` facade):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/h2f-fill-forwardloop.txt )
  ```

  **The base sorry-warning set has 37 entries in 16 modules**
  (`audits/logs/h2f-fill-base-sorries.txt`, one per declaration). Yours is
  `Build/StepBlockForward`'s one, the target. Record the base list by name first, and report any
  difference.
- **Final checks:**
  1. `Build/StepBlockForward`: zero errors, no sorry warning (for a partial, exactly the open
     declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours (**36** for a complete delivery).
  3. Re-run `H2FImportProbe.lean.txt`: 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for the target
  and every new private: within `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a
  complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 14 WARN over 36 files). No new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target (36 entries in 15 modules), among them:
- `UniversalK`'s three, which consume you: `exists_selfStartupTMK` (U2-S),
  `exists_selfUniversalK` (U2-U) and `universalK` (U2-E);
- `CodeSimulator`'s three, two of them private;
- `Build/ZoneRebalance`'s two (G4, in flight), `Build/RecordTable`'s four, `Build/InputDevice`'s
  three, `Build/NDHost`, `Build/InputWindow`, `NDCodeSimulator`'s two;
- the older specs in `Simulation`, `Composition`, `Build/Wrappers`, `Build/Loop`, `Encoding`,
  `Build/Primitives` and `ClassP/TimeConstructible`.

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] 1/1, or the phase reached; the base hash and the ancestor check.
- [ ] Every new declaration with its role; the leaf and why no row serves it; the flagged appendix.
- [ ] The constant `C` and the cost function, with the bound.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows and for private names of `StepBlock`/`StepBlockLoop`.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **`roundTM k`'s states are `Σ key, Ph k key`**; its entry is `⟨.entry, ()⟩` and its exits are
  `exit k b`, with **`exit k true = ⟨.entry, ()⟩`** (the composition bullet above). `roundTM_effect`
  takes `M.tr`, `c`, `q`, `hq`, the block configuration, the entry hypothesis and `Rep`; its
  conclusion opens with `let a := …` and nests `let e := …`. `roundTM_visited` restates the time,
  exit, `Rep`, cut and silence with the visited sets, as `loopOrbit_round` uses it.
- **The summary before the round is `outputSummary [] = none`**, so the round's summary cell is
  `summaryEmit none a.output = a.output`.
- **`L`'s control needs `Fintype` and `DecidableEq`:** index the phase host by `Bool` or a
  private two-constructor inductive with `deriving DecidableEq, Fintype`; the block phase's
  states `Unit ⊕ Σ key, Ph k key` have both (`instFintypePh`, `instDecidableEqPh`).
- **A blank is written as `some none`** (`Action.workTapes : Fin k → Option (Option Symbol) × SignType`);
  `none` writes nothing. The leaf's emission is the read cell itself, an `Option Bool`.
- **`Rep` leaves the physical output free.** Apply `roundTM_effect` to `{c with output := []}`, and
  keep the real output in the physical configuration (the auditor's point).
- **`forwardLoopCfg`'s state is `c.state.map (fun _ => entry)`:** `none` exactly when `c` is
  halted. The lockstep's exits are `{none}` on both sides.
- **`Fin.addCases` builds the `k + 2` tapes:** mirrored tapes are `Fin.castAdd 2 i`, the table is
  `Fin.natAdd k 0`, and the summary is `summaryTape k = Fin.natAdd k 1`. `simp` lemmas
  `Fin.addCases_left`/`_right` unfold them.
- **`phaseHostTM_run`** gives the prefix up to `T` and the dispatch at `T + 1`; its `hguard` must
  hold strictly before `T`.
- **A halted source has `M.step c = c`.** The lockstep's `step` field is only for live `c`.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
