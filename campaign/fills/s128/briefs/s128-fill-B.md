# §12.8 fill — stream B: constant writers and native-input sweeps (`Build/Scan.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 182e6f44c5135f07cb4965a42fc6865da720d553 HEAD` succeeds.
  That commit contains:
  - the §12.8 statement layer (PR #28, gate CLOSED in round 2:
    `audits/s12-8-statements-{findings,r2-findings,resolutions}.md`);
  - the trace promotion (`cd826a23`, PR #32), which makes `Turing.catalogTrace` and
    `Turing.catalog_trace_run` public;
  - the pre-issue shared layer (`5afed90b`, branch `s12-8/fill-preissue-2`). It makes
    `Turing.catalog_write_take` public and adds the one-step lemmas of the two Part 3
    actions: `Turing.step_of_tapeAction_move`, `Turing.step_of_tapeAction_write` and
    `Turing.step_of_inputMoveAction`;
  - this brief and its order list.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/s128-B`). Record the
  base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s128-B.zip`. It contains
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a
  git bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## What this is

Fill the **four audited-true contracts** of `Build/Scan.lean`. They are the §12.8 rows that
touch no G1-owned file (design §12.8a §3 and §8):

| Row | Target | Contract |
|---|---|---|
| R8.4 | `Turing.writeConstTM_run_ofCfg` | write the fixed word `w₀` from the head of tape `i`, return; exact `2\|w₀\| + 2` |
| R8.4′ | `Turing.writeAdvTM_run_ofCfg` | write `w₀`, leave the head after it, return to state `0` (cyclic); exact `\|w₀\| + 1` |
| R8.5a | `Turing.inputCopyTM_run_ofCfg` | copy the native input onto tape `i`, both heads back; exact `2\|x\| + 2` |
| R8.5d | `Turing.inputFoldTM_run_ofCfg` | fold the native input, verdict in `done`, input head back at `1`; exact `2\|x\| + 2` |

The statement gate closed with all four true as stated, in both rounds. Read in full:

- the four rows' findings in `audits/s12-8-statements-findings.md` (21–24) and
  `audits/s12-8-statements-r2-findings.md` (2, 22–25), quoted below;
- `audits/s12-8-statements-resolutions.md`;
- `machine-library-design.md` §12.6, §12.8 and §12.8a (§8 and §9 especially);
- `policy.md` (construction reuse, duplication);
- `workflow.md` §4;
- `audits/TEMPLATE.md` failure mode 5;
- `audits/duplication-ledger.md`, the "§12.8 statement layer" section.

**The central rule.** Three of the four rows are two-pass sweeps: a forward pass, a turn,
a return, an entry. Each of the three is an **instance of the public
`Turing.catalog_trace_run`**, with its own forward family `F`, return family `R` and exit
`D`. The fourth, `writeAdvTM`, is cyclic and is one forward induction (route 2). No second
trace is written. This is the promise of the statement layer ("one trace per routine
family", decision 12.8.5; the ledger: "The fills must use the one shared trace that the
sketches promise"), and `catalogTrace`'s promoted docstring names exactly these rows as its
instances.

**Pre-ship check (maintainer, executed).** `audits/evidence/s12-8/S128FillBProbe.lean.txt`
(output `.out`) gives 0 errors, 0 warnings, 0 `sorry`. It was run read-only against the
pre-issue olean tree (`5afed90b`) with the **real** names. It proves all four contracts to
their full statements, copied verbatim, by the routes below:
- the trace is `catalogTrace`/`catalog_trace_run`, and the write fact is `catalog_write_take`;
- Part 6 proves the shared write step at the `M.step` level, a writer's forward step and
  turn, the copier's turn, and the fold's forward step, all through the three step lemmas;
- its axiom prints are all within `[propext, Classical.choice, Quot.sound]`.

Its `probe*` names are the probe's own families and contracts. Write Scan's own private
helpers, and cite the real names.

## Owned files and targets (modify these and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `TuringMachine/Build/Scan.lean:115` | `Turing.writeConstTM_run_ofCfg` | `catalog_trace_run`, `L = \|w₀\|` | S |
| 2 | `TuringMachine/Build/Scan.lean:162` | `Turing.writeAdvTM_run_ofCfg` | one forward induction + one stationary step | S |
| 3 | `TuringMachine/Build/Scan.lean:215` | `Turing.inputCopyTM_run_ofCfg` | `catalog_trace_run`, `L = \|x\|` | S |
| 4 | `TuringMachine/Build/Scan.lean:265` | `Turing.inputFoldTM_run_ofCfg` | `catalog_trace_run`, `L = \|x\|` | — |

"S" is the shared write step (route 0). Fill in any order. **The only owned file is
`Build/Scan.lean`.** Catalog belongs to another batch in this issue, so nothing in it may
change. The facade and every other module are not yours.

## Proof routes (binding; executed in the pre-ship probe)

Notation: `n` is `w₀.length` or `x.length`; `p_j := d.workTapePos j`; "`W w r`" is the tape
map `fun j q => if j = i ∧ p_j ≤ q ∧ q < p_j + (r : ℤ) then FinTM.bufferTape w (q - p_j)
else d.workTapes j q`. Make each family total in `r` with `min` (`⟨min r n, _⟩`,
`⟨min r n + 1, _⟩`), since `catalog_trace_run` takes `ℕ →` families. Only `r ≤ n` is ever
used. Suggested private names are given; any private names are fine, but list them.

**Steps are citations.** Every single step of every route has one of three table shapes:
`tapeAction i inp none m q'`, `tapeAction i inp (some s) m q'` or `inputMoveAction inp q'`.
Each such step is a citation of `Turing.step_of_tapeAction_move`,
`Turing.step_of_tapeAction_write` or `Turing.step_of_inputMoveAction`. The table hypothesis
`htr` is discharged by unfolding the machine and the read: `simp only [M, hs]`, plus
`dif_pos`/`if_neg` for the writers. **Never unfold `MultiTapeTM.step` or `Action.apply`
for these shapes.** After the citation only `Cfg.ext` bookkeeping remains.

0. **The shared write step.** One private def and one private lemma, for the three writing
   rows:
   - `scanWriteCfg i w d q p r := { d with state := some q, inputPos := p, workTapes := W w r,
     workTapePos := fun j => p_j + if j = i then (r : ℤ) else 0 }`;
   - `scan_write_step`, at the `M.step` level, for any machine `M`, state type, `inp`, `q`,
     `q'`, `p` and `r < w.length`: from
     `htr : M.tr q (scanWriteCfg i w d q p r).inputSymbol (scanWriteCfg i w d q p r).workTapeSymbols = tapeAction i inp (some (some w[r])) .pos q'`
     conclude `M.step (scanWriteCfg i w d q p r) = scanWriteCfg i w d q' (moveInputPos p inp) (r + 1)`.

   The proof:
   - `rw [step_of_tapeAction_write M _ i inp _ .pos rfl htr]`;
   - the `workTapes` case is `catalog_write_take (d.workTapes i) (d.workTapePos i) w r hr`;
   - `workTapePos` is arithmetic.

   Every forward write step of routes 1–3 is a citation of `scan_write_step`. No route
   re-proves a one-cell write.

1. **`writeConstTM` — an instance, `L := n`.** Start with `have h0 : F 0 = d` (from
   `hstate`), then `conv_lhs => rw [← h0]` and `apply catalog_trace_run`, as
   `catalog_copy_trace` does.
   - The families:
     - `F r := scanWriteCfg i w₀ d (.wr ⟨min r n, _⟩) d.inputPos r`;
     - `R r := { scanWriteCfg i w₀ d (.bk ⟨min r n, _⟩) d.inputPos n with workTapePos := fun j => p_j + if j = i then r else 0 }`;
     - `D :=` the target's finish, verbatim (`{ d with state := some .done, workTapes := W w₀ n }`). Both this and `{ d with state := some .done, workTapes := (F n).workTapes }` were executed.
   - The equations:
     - `hF` (`r < n`): `scan_write_step` at `inp = 0`, then `moveInputPos_zero`. Its `htr` is `rw [dif_pos]`, then `min r n = r`, then the state index (`Fin.ext`).
     - `hturn`: `step_of_inputMoveAction` at `.wr n` (the table's `inputMoveAction 0 (.bk n)`).
     - `hR` (`r < n`): `step_of_tapeAction_move` at `.bk (r + 1)` (`tapeAction i 0 none .neg (.bk r)`). The head goes from `p_i + r + 1` to `p_i + r`.
     - `hentry`: `step_of_inputMoveAction` at `.bk 0` (`inputMoveAction 0 .done`).
     - `hD`: `step_of_inputMoveAction` at `inp = 0`, with `moveInputPos_zero`.
   - The three clauses from the trace:
     - time: `2n + 2` falls in `catalogTrace`'s `D` branch;
     - no earlier exit: `F` and `R` states are `wr` and `bk`;
     - trajectory: the head is `p_i + r`, `r ≤ n`.
2. **`writeAdvTM` — cyclic, one induction (no trace instance).** `catalog_trace_run` does
   **not** apply. Its `hD : M.step D = D` is false at the exit anchor `0`, which is the start
   state, so for `w₀ ≠ []` the writer writes again. Its conclusion is about every `t`.
   - Prove one private `∀ r ≤ n, (writeAdvTM k i w₀).runFrom d r = F r`, with
     `F r := scanWriteCfg i w₀ d ⟨min r n, _⟩ d.inputPos r`. Each step is `scan_write_step`.
   - Then take one stationary step at state `n`: `step_of_inputMoveAction` (`inputMoveAction 0 0`).
   - Finish: `workTapePos` is `Function.update d.workTapePos i (p_i + n)`, by `funext` and
     `by_cases j = i`.
   - No return: for `0 < t ≤ n` the state is `⟨min t n, _⟩ ≠ 0`.
   - Trajectory: split `t ≤ n` from `t = n + 1`.

   **This is the one time induction permitted in Scan.** A shared helper with `writeConstTM`
   is warranted only for the write step (route 0). No generic "forward run" lemma is needed,
   since this is Scan's only single-pass row.
3. **`inputCopyTM` — an instance, `L := n = |x|`.**
   - The families:
     - `F r := scanWriteCfg i x d .sweep ⟨min r n + 1, _⟩ r`;
     - `R r := { scanWriteCfg i x d .rewind ⟨min r n, _⟩ n with workTapePos := fun j => p_j + if j = i then (r : ℤ) - 1 else 0 }`;
     - `D :=` the target's finish, verbatim.
   - `F 0 = d` uses `hstate` and `hin`.
   - The equations:
     - `hF`: position `r + 1` reads `x[r]` (`inputSymbolInner r`, `h₁ : val = 1 + r`). Then cite `scan_write_step` at `inp = 1`, and compute the position by `moveInputPos_pos_of_ne_right`.
     - `hturn`: position `n + 1` reads `none` (unfold `Cfg.inputSymbol`). Then `step_of_tapeAction_move` with `tapeAction i (-1) none .neg .rewind`: the input goes to `n` and the head to `p_i + n - 1`.
     - `hR`: position `r + 1` reads `x[r]`. Then `step_of_tapeAction_move`: both heads move left.
     - `hentry`: position `0` reads `none`. Then `step_of_tapeAction_move` with `tapeAction i 1 none .pos .done`: the input goes to `1 = d.inputPos` (by `hin`) and the head to `p_i`.
     - `hD`: `step_of_inputMoveAction` at `inp = 0`.
   - The trajectory's lower end `p_i - 1` is reached exactly at `R 0`.
4. **`inputFoldTM` — an instance, `L := n = |x|`.**
   - The families:
     - `F r := { d with state := some (.fwd ((x.take r).foldl δ a₀)), inputPos := ⟨min r n + 1, _⟩ }`;
     - `R r := { d with state := some (.bwd (x.foldl δ a₀)), inputPos := ⟨min r n, _⟩ }`;
     - `D := { d with state := some (.done (x.foldl δ a₀)) }`, the target's finish verbatim.
   - The equations:
     - `hF`'s state: `List.take_succ`, `List.getElem?_eq_getElem`, `List.foldl_append`.
     - `hturn`'s state: `x.take n = x` (`List.take_length`, which `simp` applies).
     - All five steps are `step_of_inputMoveAction`. The input moves are those of route 3.
   - Every family member keeps `d.workTapes` and `d.workTapePos`. That **is** the third
     clause: the fold moves no work head (round-2 finding 2).

## Cited infrastructure (public and proved at the issue commit)

- **The trace.** `Turing.catalogTrace` (`Build/Catalog.lean:335`) and `Turing.catalog_trace_run`
  (`:349`). `k`, `Symbol`, `x` and `S` are implicit, and the five hypotheses come in the order
  `hF`, `hturn`, `hR`, `hentry`, `hD`.
- **The write fact.** `Turing.catalog_write_take` (`Build/Catalog.lean:418`).
- **The step lemmas.** These are all in `Build/Catalog.lean`, and each takes
  `(M) (c) (hq : c.state = some q) (htr : M.tr q c.inputSymbol c.workTapeSymbols = …)`, with
  `{q q'}` implicit:
  - `Turing.step_of_tapeAction_move` (`:11358`) gives
    `M.step c = { c with state := some q', inputPos := moveInputPos c.inputPos inp, workTapePos := Function.update c.workTapePos i (c.workTapePos i + m) }`;
  - `Turing.step_of_tapeAction_write` (`:11384`, write `some s`) additionally gives
    `workTapes := Function.update c.workTapes i (Function.update (c.workTapes i) (c.workTapePos i) s)`;
  - `Turing.step_of_inputMoveAction` (`:11412`) gives
    `M.step c = { c with state := some q', inputPos := moveInputPos c.inputPos inp }`.
- **Tables.** `Turing.tapeAction` (`:11341`) and `Turing.inputMoveAction` (`:11348`).
  `Turing.SweepPhase` (`:148`) and `Turing.ScanPhase` (`:11813`); `Turing.WritePhase` is
  `Scan.lean:76`.
- **The model.**
  - `Configuration.lean`: `Cfg` (`@[ext]`; the case names are the fields),
    `Cfg.inputSymbol`, `inputSymbolInner` (`@[simp]`), `Cfg.workTapeSymbols`,
    `moveInputPos` with `_zero`, `_leftBoundary`, `_rightBoundary`, `_neg_of_ne_left` and
    `_pos_of_ne_right`.
  - `Deterministic.lean`: `MultiTapeTM.runFrom`, `runFrom_zero`, `runFrom_succ_eq_step'`,
    `runFrom_add`.
  - `Simulation.lean`: `FinTM.moveInputPos_neg_val` (generic), `FinTM.bufferTape` with
    `_nat` and `_left`.
- **Do not cite** (`Bool`-only: `x : List Bool`, `S : Type`, so they do not typecheck at the
  generic rows): `FinTM.inputSymbol_at`, `rewind_scan`, `rewind_from_any`, `timed_rewind`,
  `controlAction`, `emit_run`.

Every cited declaration is proved, and the pre-ship probe prints the axioms of the old
ones (Part 5): `[propext, Classical.choice, Quot.sound]` or fewer. **The "proved modulo" set is empty**,
and a complete delivery has no `sorryAx`.

## Inherited audit contracts (verbatim; binding on the fill)

**Round 1** (`audits/s12-8-statements-findings.md`), the four rows:

> | 21 | note | Build/Scan.lean · `WritePhase`, `writeConstTM_run_ofCfg` | The constant writer overwrites exactly its word interval and returns in `2*w₀.length + 2` steps. | The finite state counter performs w₀.length writes/right moves, one stationary phase change, w₀.length left moves, and one stationary exit. It never reads the old cells, so arbitrary old contents and exterior frames are preserved as stated, with the head confined to the declared interval. Checks: empty pattern takes two steps, singleton takes four, and a displaced overwrite into a nonblank interval leaves both exterior cells untouched. | No statement change. |
>
> | 22 | note | Build/Scan.lean · `writeAdvTM_run_ofCfg` | The advancing writer has a first positive return to state 0 at w₀.length + 1. | States 0 through w₀.length count the writes; the last stationary transition returns to 0. For a nonempty pattern all intermediate states are nonzero, and the head advances exactly by the pattern length. Checks: empty pattern is one stationary round, singleton is a two-step round, and two consecutive rounds write two contiguous copies. The empty-pattern cut is correctly over strictly positive intermediate times. | No statement change; retain the cyclic convention as in recommendation 43. |
>
> | 23 | note | Build/Scan.lean · `inputCopyTM_run_ofCfg` | The native-input copier restores both heads and has exact time `2*x.length + 2`. | From input position 1, x.length lockstep writes copy the input; the right marker turns both heads left; x.length left moves and the left-marker right move restore their entry positions. The work-tape return is guided by the native input, so it needs no destination delimiter and overwrites only the prescribed interval. Checks: empty input gives two steps, singleton gives four, and a nonblank destination frame at start − 1 is preserved despite being visited. | No statement change. |
>
> | 24 | note | Build/Scan.lean · `inputFoldTM_run_ofCfg` | The native fold returns the left fold verdict, restores input position 1, and moves no work head. | The forward input scan accumulates `x.foldl δ a₀`; the backward scan preserves that accumulator. The same marker accounting gives `2*x.length + 2` and excludes an earlier `done`. Checks: empty input, zero work tapes, and a foreign symbol in the middle of a rich input. The latter is seen as an ordinary nonblank rich symbol by this validator, so it can set a persistent rejection flag. | No statement change; this supports O6. |

**Round 2** (`audits/s12-8-statements-r2-findings.md`), the overview minor and the four rows:

> | 2 | minor | `Build/Scan.lean` · module documentation, “The input sweeps” | The overview incorrectly attributes work-head movement to the input fold. | It says the input sweeps move the native head “in lockstep with the work heads.” For `inputFoldTM`, every transition uses `inputMoveAction`, which fixes all work heads. On a singleton input, its first step moves the input head from 1 to 2 while every work head remains fixed. The definition and theorem are correct. | Restrict the lockstep description to `inputCopyTM`; say that `inputFoldTM` moves only the input head. |
>
> | 22 | note | `Build/Scan.lean` · `WritePhase`, `writeConstTM_run_ofCfg` | The constant writer has the stated overwrite interval, return, and exact time. | Its finite index counts `w₀.length` writes, one stationary turn, that many left moves, and one stationary exit: `2*w₀.length + 2`. No old contents are read, and no exterior cell is written. Checks: empty pattern, singleton, and displaced overwriting of a nonblank interval. | No statement change. |
>
> | 23 | note | `Build/Scan.lean` · `writeAdvTM_run_ofCfg` | The advancing writer satisfies the first-positive-return discipline. | States count writes from zero through the pattern length; the final stationary step returns to zero after `w₀.length + 1` steps. Intermediate positive times have nonzero states, and the head advances by precisely the pattern length. Checks: empty pattern, singleton, and two successive rounds producing adjacent copies. | No statement change. |
>
> | 24 | note | `Build/Scan.lean` · `inputCopyTM_run_ofCfg` | Native-input copying has exact time `2*x.length + 2` and restores both heads. | The forward pass copies in lockstep; the right input marker turns both heads, and the left input marker supplies the final right move. The return is guided by input, so destination delimiters are unnecessary. Checks: empty input, singleton, and a nonblank destination cell immediately left of entry, which is visited but preserved. | No statement change. |
>
> | 25 | note | `Build/Scan.lean` · `inputFoldTM_run_ofCfg` | Native folding produces the stated verdict with stationary work heads. | The forward scan accumulates `x.foldl δ a₀`; the backward scan preserves it, and marker accounting gives `2*x.length + 2`. Every action fixes work heads and contents. Checks: empty input, zero work tapes, and a foreign rich symbol that sets a persistent rejection flag. | No theorem change; correct only finding 2’s overview sentence. |

Round 2, finding 2's disposition (`audits/s12-8-statements-resolutions.md`):

> | 2 (minor): `Scan.lean`'s overview says both input sweeps move the work heads in lockstep | **Swept** (comment-only). Only `inputCopyTM` moves its destination head in lockstep; `inputFoldTM` moves only the input head. The code is identical with comments stripped, and the file elaborates at 0 errors with its 4 sorries |

The validator role (round-1 note 33 and round-2 note 32, *proposed-fix* column):

> Round 1, note 33: Retain O6; input validation alone does not repair the missing valid-input workspace contracts.
>
> Round 2, note 32: Retain O6 and the dedicated-digit-tape discipline.

The shared-trace promise (round-1 and round-2 note 38, *proposed-fix* column):

> Round 1, note 38: No new debt major. Record the same-file similarities, preserve the existing ledger acknowledgments, and enforce the promised shared trace at fill; do not treat a text-screen zero as a semantic no-duplication proof.
>
> Round 2, note 38: No debt major. Preserve the existing acknowledgments and enforce the promised shared traces during fill.

The design decisions behind the rows' shapes (`machine-library-design.md`):

> §12.8, decisions 12.8.1–12.8.6 (2026-10-10), item 5:
>
> 5. **Fold and seek live in Catalog, after the G1 gate** (user), sharing the
>    R3/G2 trace, one trace per routine family.
>
> §12.8a §8, changes from the draft, items 3 and 6:
>
> 3. **`writeAdvTM` is cyclic** over `Fin (|w₀|+1)`. It returns to its start state
>    `0`, so it is a counter-loop round as it stands. A seam caller that runs it
>    once uses `seamReleaseTM`.
>
> 6. **No new copier phase type.** The input copier reuses `SweepPhase`, and the
>    input fold reuses `ScanPhase`.
>
> §12.8a §9, decision 3:
>
> 3. `writeAdvTM` stays **cyclic**. One-shot callers use `seamReleaseTM`.

The promoted trace's own contract (`Build/Catalog.lean`, `catalog_trace_run`'s docstring):

> /-- **Local transition equations determine the sweep trace** (design §12.6; public
> since the §12.8 fill). If one step takes each forward configuration to the next for
> `L` steps, turns the last into the return family's start, takes each return
> configuration to the previous one, enters `D` from the return's end, and leaves `D`
> fixed, then the run from `F 0` is `Turing.catalogTrace F R D L` at every time,
> including all stationary steps after the exit. Every two-pass row (the R3 sweeps, the
> framed compare, the scan, the writers and the native-input sweeps) is an instance.
> 
> **Proof sketch.** Induct on elapsed time; split at the forward endpoint, return
> endpoint, and stationary tail. -/

## Gate guidance (binding)

The gate closed with all four statements true as stated, with degenerate and adversarial
checks. Its notes bind the fill as follows:

- **No statement change.** All four rows are "No statement change" in both rounds. A row
  that resists is an escalation, never a restatement.
- **Edge cases are in scope** and the routes cover them: `w₀ = []` and `x = []` (`L = 0`,
  so `hF` and `hR` are vacuous); a nonblank destination cell at `p_i - 1` (visited by the
  copier, never written); a nonblank interval overwritten by a writer; `k = 0` for the fold;
  a foreign rich symbol for the fold (just a symbol to `δ`).
- **The copier's return is input-guided.** The destination needs no delimiter. Do not add
  or assume one.
- **The fold fixes every work head** (round-2 finding 2). The module overview is already
  swept at the issue commit. Do not reintroduce "lockstep" wording for the fold.
- **The writers never read the tape.** Their proofs must not branch on old cell contents.
- **Shared trace, enforced** (note 38, both rounds): routes 1, 3 and 4 cite
  `catalog_trace_run`. Route 0 is the only write-step proof, and every single step is one
  of the three step-lemma citations.
- **Downstream, hands off.** `writeAdvTM_run_ofCfg` is `expandTM_run_ofCfg`'s round
  hypothesis (CounterLoop), and `inputCopyTM_run_ofCfg` is `exists_inputCallTM`'s first leg
  (InputCall). Their statements are therefore load-bearing exactly as frozen.

## Ground rules (binding)

1. **File ownership.** Only `Build/Scan.lean`: the four targets' bodies plus new `private`
   helpers placed before their first use. List every new declaration with its role.
2. **Statement freeze** over the four targets **and every landed definition** (`WritePhase`,
   `writeConstTM`, `writeAdvTM`, `inputCopyTM`, `inputFoldTM`). Each must be byte-identical:
   no renames, re-signatures, restatements or attribution edits. Docstrings stay. Flagged
   sketch appendices are allowed.
3. **Status text.** Only the module docstring's "**Status: statements.**" paragraph and the
   "(statements)" tag in `## Main results` may change, to "proved"; flag each.
   **New exports: none.** If a helper looks shared beyond Scan, *request* it in the report.
4. **Escalation** on anything unprovable as stated, including a table defect: stop on that
   item, record the obstruction, and continue with the rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports unchanged.** Scan imports only `Build/Catalog`, and every cited name is in its
   closure. A Mathlib import only if a needed lemma requires it; flag it. No TCSlib import
   may be added.
7. **One proof per shared argument.** One trace (`catalog_trace_run`, cited), one write step
   (route 0), the three step lemmas (cited), and one time induction (route 2's). Never a
   second copy of any of them.
8. **Size.** Report file sizes; no new files.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states:
   - which targets are proved;
   - which `private` helpers remain `sorry` (partial delivery only, each with a
     "Proof sketch");
   - which proved targets are proved modulo them.

## Duplication governance (binding)

Run the text-level screen **before and after**. The population is that of
`audits/logs/s12-8-statements-r2-copytext.txt`. The base at the pre-issue tree (`5afed90b`;
`audits/logs/s12-8-fill-B-screen-base.txt`) is **550 declarations, 415 pairs, 121,938 characters**: the round-2 log's 535 / 408 /
120,748 plus the pre-issue layer's own pairs. Scan's only base pair is
`writeConstTM` ← `writeAdvTM`, 58%. If `182e6f44c5135f07cb4965a42fc6865da720d553` differs from `5afed90b` in any screened
file, take the "before" run as the base.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/{Scan,Catalog,Seam,CounterLoop,Embed,InputCall,CfgRecord}.lean \
  TCSlib/Complexity/TuringMachine/{Simulation,SymbolLift}.lean \
  TCSlib/Complexity/ClassPSPACE/TQBF.lean
```

- **Forbidden outright**:
  - any re-derivation of the two-pass trace: a private lemma inducting on elapsed time over
    a forward pass and a return, or a private variant of `catalogTrace` or
    `catalog_trace_run`;
  - any re-proof of a step of the shapes above: unfolding `MultiTapeTM.step`/`Action.apply`
    where `step_of_tapeAction_move`, `step_of_tapeAction_write` or `step_of_inputMoveAction`
    applies, or re-proving `catalog_write_take`;
  - any copy or adaptation of Catalog's private `catalogCopyF`, `catalogCopyR`,
    `catalogTransferR`, `catalogClearF`, `catalogClearR`, `catalog_copy_forward`,
    `catalog_copy_trace`, `catalog_transfer_trace` or `catalog_clear_trace`;
  - any proof derived from EmitIterBody's private `copy_step`, `rwTape_*`, `rwInput_*` or
    `body_start` (CH7-D2 re-derives *those* from `inputCopyTM` in 12.2c T2, never the reverse).
- **Cross-file pairs.** Exactly **one** new cross-file pair is expected and allowed:
  `scanWriteCfg` ↔ `catalogCopyF`, at about 55%, in both directions. These are two
  definitions, framed configuration records of different machines, with no proof between
  them. Justify it in one line in `REPORT.md`. **Any other new cross-file pair is
  forbidden**, whatever its percentage.
- **In-file pairs.** List every new in-file pair with a one-line justification. A pair at
  ≥ 90% is a copy: factor it. A maintainer prediction, written before the step lemmas
  existed, had eight at 53–69%: the four contracts' clause derivations, and the trace
  lemmas against each other and against the write step.
- **Advisory screen** (record it; it has no base in the logs). Its base is 283 declarations,
  230 pairs, 71,309 characters, unchanged at `5afed90b`, since none of its four files
  changed. No new cross-file pair is allowed.

  ```sh
  python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
    TCSlib/Complexity/TuringMachine/Build/{Scan,EmitIterBody,Primitives}.lean \
    TCSlib/Complexity/TuringMachine/Simulation.lean
  ```
- Quote all outputs in `REPORT.md`, which carries **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/s128-fill-B.txt`. It has 74 modules: the upstream
  closure of `Build/Scan` and of every module downstream of it. The downstream modules are
  `Build/CounterLoop`, `Build/InputCall`, `Build/CfgRecord` (which imports InputCall since
  `5afed90b`), `ClassPSPACE/TQBF`, and the `ClassPSPACE` and `TuringMachine` facades. The
  root `TCSlib` is excluded.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/s128-fill-B.txt )
  ```

  Bootstrap fresh: an olean tree predating `cd826a23` has the trace names private.

  Base sorry-warning set, **37**:
  - yours: `Build/Scan` 4;
  - upstream: `Build/Seam` 1, `Build/Catalog` 12, `NDCodes` 1, `Constructible` 2,
    `ConfigGraph` 3, `Inclusions` 2;
  - downstream: `Build/CounterLoop` 1, `Build/InputCall` 2, `Build/CfgRecord` 5,
    `ClassPSPACE/TQBF` 4.

  Every other module in the list has 0.
- **Final checks:**
  1. `Build/Scan`: zero errors, zero sorry warnings.
  2. Downstream: zero errors, and sorry warnings exactly the base's: `Build/CounterLoop` 1,
     `Build/InputCall` 2, `Build/CfgRecord` 5, `ClassPSPACE/TQBF` 4, and the two facades 0.
  3. The upstream modules are untouched: the sweep reproduces their base counts.
  4. The total is 33.
- **Axiom prints** for the four targets: within `[propext, Classical.choice, Quot.sound]`,
  with no `sorryAx`.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL. Every new `private` declaration carries a docstring; a partial delivery needs a
  literal "Proof sketch" before each remaining `sorry`.

## Out-of-scope sorries you will see (leave every one untouched)

- **Downstream** (another batch or a later one fills them):
  - `Turing.expandTM_run_ofCfg` (`Build/CounterLoop`), which consumes your target 2;
  - `Turing.FinTM.exists_inputCallTM` (which consumes your target 3) and
    `Turing.exists_inputSeekTM` (`Build/InputCall`);
  - `Build/CfgRecord`: `cfgRecord_inj`, `recordValid_iff`, `exists_recordStepTM`,
    `exists_recordEqTM`, `exists_recordTestTM`;
  - `ClassPSPACE/TQBF`: `exists_adjacency_codec_cnf`, `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`,
    `TQBF_PSPACEComplete`.
- **Upstream, in the order list:**
  - `Build/Catalog`, Part 3 (stream A of this issue): `fieldsTape_field`,
    `compareTM_run_ofCfg`, `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg`,
    `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg`, `scanTM_run_ofCfg`,
    `scanResult_fold`, `scanResult_map`, `scanResult_shiftRight`,
    `scanResult_shiftLeft`, `scanResult_carry`;
  - `Build/Seam`: `seamCompTM₂_run_ofCfg`;
  - `NDCodes`: `exists_effectiveNDMachineCode` (plan C1);
  - `SpaceComplexity`: `spaceConstructible_logSpace`, `spaceConstructible_linear`
    (`Constructible`); `NSPACE_subset_exp_dtime`, `NL_subset_P`,
    `polyTimeReducible_of_mem_NL` (`ConfigGraph`); `NP_subset_PSPACE`, `SAT3_mem_PSPACE`
    (`Inclusions`).

If a proof seems to *need* one of these, that is an escalation, not a license. None of the
four routes uses any of them.

## REPORT.md checklist

- [ ] 4/4, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role: the write family and step (route 0), each row's
      families, its trace instance or induction. Each step's step-lemma citation.
- [ ] For each two-pass row, the `catalog_trace_run` citation and its `F`/`R`/`D`. For
      `writeAdvTM`, the one induction and why the trace does not apply.
- [ ] Imports and requested shared lemmas, or "none"; escalations, or "none"; status-text
      updates and appendices, each flagged.
- [ ] Duplication: both screens before and after; the one allowed cross-file pair
      (`scanWriteCfg` ↔ `catalogCopyF`) justified in one line; every new in-file pair
      justified; "new copies: none".
- [ ] File sizes (no new files); the final sweep tail; four axiom prints; the lint line. The
      diff touches only `Build/Scan.lean`.

## Known pitfalls at this pin (hard-won; all hit in the pre-ship probe)

- **The step lemmas' implicit `q'`.** When `htr` is proved by `simp only [M, hs]`, `q'`
  cannot be inferred: pass it, as in `step_of_inputMoveAction _ _ 1 rfl (q' := .fwd …) (by
  simp only [inputFoldTM, hs])`. `hq` is `rfl` on a family whose state is a literal `some q`.
- **The step lemmas update `workTapePos` by `Function.update`.** Add `Function.update_apply`
  to the `simp` set in the `workTapePos` case, then `omega`. `step_of_tapeAction_write`'s
  `workTapes` is a nested `Function.update`. After `by_cases j = i`, the `i` branch is
  `catalog_write_take` (`simpa [scanWriteCfg] using …`).
- **`SignType` literals versus constructors.** The tables pass the input move as `0`, `1`,
  `-1` and the work move as `.pos`/`.neg`. `moveInputPos_pos_of_ne_right`,
  `moveInputPos_neg_of_ne_left` and `FinTM.moveInputPos_neg_val` are stated at
  `.pos`/`.neg`. Rewrite `← SignType.pos_eq_one` / `← SignType.neg_eq_neg_one` first.
  `simp [moveInputPos]` leaves a `dite` over `Int.toNat` that `omega` cannot read.
- **`min` in dependent positions.** In `writeConstTM`/`writeAdvTM` the bound proof of
  `w₀[j]` depends on the `dif` condition. `rw [dif_pos (show min r n < n by omega)]` first,
  then `simp only [show min r n = r by omega, show min (r + 1) n = r + 1 by omega]`.
- **`Cfg.ext <;> simp` closes an unpredictable subset of goals,** so bullets after it
  misfire. After the step-lemma rewrite, write `apply Cfg.ext`, then
  `case state/inputPos/workTapes/workTapePos/output => …`, then `all_goals simp […]`.
- **`simp [List.take_succ]` hits the maximum recursion depth.** In the fold's state goal use
  `rw [List.take_succ, List.getElem?_eq_getElem hr, List.foldl_append]; rfl`.
- **The table hypothesis.** `htr` is about `(F r).inputSymbol` and `(F r).workTapeSymbols`.
  Prove `hs : (F r).inputSymbol = …` first, then `simp only [M, hs]`. For a writer's
  `scan_write_step`, state `F r` through `scanWriteCfg` (or unfold the family name first),
  or the rewrite pattern is not found.
- **`inputSymbolInner` wants `inputPos.val = 1 + p`** (`1 + p`, not `p + 1`). The two blanks
  are `simp [Cfg.inputSymbol, F]`. `hin`'s `1` is a `Fin (x.length + 2)` literal:
  `apply Fin.ext; simp` closes `⟨min 0 n + 1, _⟩ = 1`.
- **`writeAdvTM`'s no-return goal.** `simp only [F, scanWriteCfg, ne_eq, Option.some.injEq,
  Fin.ext_iff, Fin.val_zero]` reduces it to `¬min t n = 0`, which `omega` closes.
- **Give `D` as the target's finish verbatim.** Then the time clause is
  `simp [catalogTrace, show ¬2 * n + 2 ≤ n by omega]`, and the other two are
  `simp only [catalogTrace]; split_ifs <;> simp […] <;> omega`
  (`Finset.mem_Icc` for the trajectories). The negative coordinates stay in `ℤ`
  (`q - p_j`); never route through `Int.toNat`.
- `inputFoldTM`'s `A` is `Type` (not `Type*`); `Γ` is `Type*`. The linter requires a literal
  "Proof sketch" before every `sorry` (partial delivery only).
