# §12.8 fill, stream A: Catalog Part 3 and the two-exit seam (`Build/Catalog.lean`, `Build/Seam.lean`)


## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 182e6f44c5135f07cb4965a42fc6865da720d553 HEAD` succeeds. That
  commit contains:
  - the §12.8 statement layer (PR #28: Catalog Part 3, the Seam row R8.8) and its closed
    gate (`audits/s12-8-statements-{findings,r2-findings,resolutions}.md`);
  - the trace promotion (PR #32), which makes `Turing.catalogTrace` and
    `Turing.catalog_trace_run` **public**;
  - the pre-issue shared layer `5afed90b`: the public action-step lemmas, the layout facts and
    `catalog_write_take`, which you cite;
  - the order list.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested `fill/s128-A`). Record the
  base hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s128-A.zip`, containing
  `REPORT.md`, the full modified sources, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`. Catalog and Seam are G1-owned
  files, so the maintainer lands your series by a PR the user merges, followed by the §12.8
  fill gate (design §12.8a §8, Governance).

## What this is

Fill the **thirteen audited-true statements of stream A**: the alphabet-generic rows of
Catalog Part 3 (design §12.8a) and the two-exit seam (R8.8). The statement gate closed at
round 2 (PASS, 0 blockers, 0 majors, 2 minors, 36 notes). Both rounds found every one of
these statements true as stated (round 1 notes 9–20 and 31; round 2 notes 10–21 and 30).

| Layer | Targets | Home |
|---|---|---|
| field layout | `fieldsTape_field` | Catalog, Part 3 |
| R8.2 scan identities (pure lists) | `scanResult_fold`, `_map`, `_shiftRight`, `_shiftLeft`, `_carry` | Catalog, Part 3 |
| R8.2 two-pass scan, the G2 core | `scanTM_run_ofCfg` | Catalog, Part 3 |
| R8.1 framed compare | `compareTM_run_ofCfg`, plus re-deriving the canonical compare rows | Catalog, Part 3 and the R3 section |
| R8.3 one-pass seeks | `skipTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg` | Catalog, Part 3 |
| R8.8 two-exit seam | `seamCompTM₂_run_ofCfg` | Seam |

**One trace per routine family** (design §12.6, §12.8a §3; audit note 38 of both rounds).
- Every two-pass row (the scan and the compare) is one instance of the public
  `Turing.catalog_trace_run`.
- The four one-pass rows share **one** private corollary of that trace (route 5).
- The compare **generalizes** its existing private trace in place. It does not add a second
  one.
- The single steps of every row go through the **public** action-step lemmas of the
  pre-issue layer, which are shared with the other §12.8 streams. Never re-prove them
  privately.

Read in full:
- design `machine-library-design.md` §12.6 and §12.8a, especially §3's R8.1–R8.3 rows, §8
  (landed names) and §9 (decisions 1–2: skip back is the inverse of skip, and tables carry a
  header);
- the gate records, whose notes for these targets are quoted below and are **binding**;
- `policy.md` (construction reuse, duplication, proof sketches);
- `workflow.md` §4;
- `audits/duplication-ledger.md` §12.8 and its acknowledgment table.

**Pre-ship check (maintainer, executed).** The probe is
`audits/evidence/s12-8/S128FillAProbe.lean.txt`, with its output in `.out`. Run read-only
against the pre-issue olean tree at `5afed90b`, it gives **0 errors and 0 warnings**, and has
no `sorry` of its own. It checks:
- `#check` of the 13 targets and of every public name cited below, including
  `catalogTrace`, `catalog_trace_run` and the pre-issue lemmas;
- route steps as `example`s:
  - the one-pass helper `catalog_pass_contract` (route 5), derived from the real
    `catalog_trace_run`;
  - anchor stationarity, by `step_of_inputMoveAction` at `0`;
  - a skip step through `step_of_tapeAction_move`;
  - the scan's forward write through `step_of_tapeAction_write`;
  - the canonical compare from the framed row on the non-aliased branch;
  - `catalog_compare_stop`'s body, verbatim, at a generic alphabet;
  - the Mealy facts `mealyRun_keep`, `scanResult_keep`, `mealyRun_append` and
    `mealyRun_length`;
  - the list identity behind `scanResult_shiftLeft`;
  - the table's end blanks, from `length_joinFields_add_one`;
  - **both branches of `seamCompTM₂_run_ofCfg`**, from the cited public lemmas.

Two companion files record supporting checks:
- `S128FillAProbe-private.lean.txt`, the visibility check: both trace names resolve.
- `S128FillAProbe-lint.lean.txt`: the linter and syntax behaviour behind pitfalls 1 and 4.
  Its warnings and errors are expected and listed in its header.

Re-run all three at the issue commit before you start.

## Owned files and targets (modify these and nothing else)

Lines are at `5afed90b`. Re-confirm them at `182e6f44c5135f07cb4965a42fc6865da720d553` with `grep -n '^theorem <name>'`.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `Build/Catalog.lean:11533` | `Turing.fieldsTape_field` | layout induction through `fieldsTape_cons_shift` | layout facts |
| 2 | `Build/Catalog.lean:11914` | `Turing.scanResult_fold` | keep reduction + one `mealyRun` induction | H-scan |
| 3 | `Build/Catalog.lean:11924` | `Turing.scanResult_map` | likewise | H-scan |
| 4 | `Build/Catalog.lean:11935` | `Turing.scanResult_shiftRight` | likewise | H-scan |
| 5 | `Build/Catalog.lean:11949` | `Turing.scanResult_shiftLeft` | 4 on `w.reverse`, plus one list identity | 4, H-scan |
| 6 | `Build/Catalog.lean:11964` | `Turing.scanResult_carry` | keep reduction + one induction | H-scan |
| 7 | `Build/Catalog.lean:11859` | `Turing.scanTM_run_ofCfg` | one `catalog_trace_run` instance, Mealy families | H-scan, step lemmas |
| 8 | `Build/Catalog.lean:11558` | `Turing.compareTM_run_ofCfg` | the generalized private compare trace | H-cmp |
| 9 | `Build/Catalog.lean:11617` | `Turing.skipTM_run_ofCfg` | one-pass helper | H-pass, step lemmas |
| 10 | `Build/Catalog.lean:11663` | `Turing.skipBackTM_run_ofCfg` | one-pass helper | H-pass, step lemmas |
| 11 | `Build/Catalog.lean:11713` | `Turing.seekEndTM_run_ofCfg` | one-pass helper + layout | 1, H-pass, H-lay, step lemmas |
| 12 | `Build/Catalog.lean:11768` | `Turing.seekStartTM_run_ofCfg` | one-pass helper + layout | 1, H-pass, H-lay, step lemmas |
| 13 | `Build/Seam.lean:625` | `Turing.seamCompTM₂_run_ofCfg` | promoted prefix lemma + right lockstep | — |

**Authorized proved-body changes (flag each in `REPORT.md`).** Round 1 note 10 and design
§12.8a's R8.1 row ask you to "generalize the existing compare trace and derive the canonical
row at fill". Concretely:

- **Public, body swaps.** `Turing.compareTM_run` (`Catalog:1492`) and
  `Turing.compareTM_spaceUsedByTape` (`Catalog:1523`) get new bodies. Each body cites the
  generalized trace at `d := Cfg.ofWords .run w`, the way `transferTM_spaceUsedByTape`
  (`:1314`) already cites `catalog_transfer_trace`. Their statements stay
  **byte-identical**.
- **Private, in-place generalizations.** These are replacements, not additions, so the net
  private count is unchanged. Update their docstrings with them (policy §3, synchronization):
  - `catalog_compare_stop` (`Catalog:680`): types only, the body verbatim;
  - `catalogCompareF` (`:710`) and `catalogCompareR` (`:715`): canonical to framed;
  - `catalog_compare_trace` (`:724`): canonical to framed.
- **Why not "cite `compareTM_run_ofCfg`"?** The canonical `compareTM_run` has **no
  `fst ≠ snd` hypothesis**: the aliased case is part of its audited statement. The framed
  public row assumes `hne`, so it cannot carry the canonical row alone. The generalized trace
  needs no `hne` (route 4), so all three compare rows cite it (decision D2, approved).

Fill in the table's order: 1–6 are pure, then 7, 8, 9–12; 13 is independent. The
`TuringMachine` facade is not yours.

### Proof routes (binding; the landed sketches, amplified)

**Public pre-issue lemmas you cite** (`Build/Catalog.lean`, Part 3; never re-prove them):
- **Action steps.** If the machine's table at the current state and reads is the named action,
  then one step does the following.

  | Lemma | Line | Action | Effect of one step |
  |---|---|---|---|
  | `step_of_tapeAction_move (M c) {q q'} (i inp m) hq htr` | `:11358` | `tapeAction i inp none m q'` | moves the input head by `inp` and head `i` by `m`; enters `q'` |
  | `step_of_tapeAction_write (M c) {q q'} (i inp s m) hq htr` | `:11384` | `tapeAction i inp (some s) m q'` | as above, and rewrites the scanned cell of tape `i` to `s` |
  | `step_of_inputMoveAction (M c) {q q'} (inp) hq htr` | `:11412` | `inputMoveAction inp q'` | moves the input head by `inp` only |

  Every seek step and the scan's writes and turns are the first two. Every anchor's
  stationarity (`hD`) is `step_of_inputMoveAction … 0` followed by `moveInputPos_zero`
  (probe).
- **Layout facts.**
  - `joinFields_cons_cons` (`:11444`);
  - `fieldsTape_cons_shift` (`:11454`): past the first field and its separator, from relative
    position `-1` on;
  - `fieldOffset_succ` (`:11471`) and `fieldOffset_cons_succ` (`:11478`);
  - `length_joinFields_add_one` (`:11487`): `(joinFields fs).length + 1 = fieldOffset fs |fs|`
    for `fs ≠ []`;
  - `fieldOffset_add_length_le` (`:11505`).
- **The write fact.** `catalog_write_take` (`:418`), public. The private `catalogTape`
  (`:406`) and `catalog_write_middle` (`:844`) are in-file citations.

**New private helpers** go in Part 3. The names are suggestions; list every one in
`REPORT.md`.

- **H-pass, the one-pass instance of the shared trace.** Its proof is in the probe; it derives
  from the real `catalog_trace_run`.

  ```lean
  private theorem catalog_pass_contract {k : ℕ} {Symbol : Type*} {x : List Symbol} {S : Type*}
      (M : MultiTapeTM k Symbol S) (F : ℕ → Cfg k Symbol S x) (D : Cfg k Symbol S x) (L : ℕ)
      (hF : ∀ r < L, M.step (F r) = F (r + 1)) (hexit : M.step (F L) = D) (hD : M.step D = D)
      (P Q : Cfg k Symbol S x → Prop) (hP : ∀ r ≤ L, P (F r)) (hQ : ∀ r ≤ L, Q (F r))
      (hQD : Q D) :
      M.runFrom (F 0) (L + 1) = D ∧ (∀ t < L + 1, P (M.runFrom (F 0) t)) ∧
        ∀ t ≤ L + 1, Q (M.runFrom (F 0) t)
  ```

  It **cites** `catalog_trace_run M F (fun _ => D) D L hF hexit (fun _ _ => hD) hD hD`.
  With a constant return family, `catalogTrace F (fun _ => D) D L t` reduces to
  `if t ≤ L then F t else D` by `simpa [catalogTrace]`. It never re-inducts on time.
  - Take `P` to be "state `≠ some .done`", and `Q` to be the statement's trajectory clause
    with `j` quantified inside.
  - Without this helper the four seek rows would be four near-copies of one time induction
    and three-clause closing. Their tables already pair at 50–100% in the base screen (ledger
    §12.8).
- **H-scan, the Mealy facts** (all four are proved in the probe):
  - `mealyRun_keep : mealyRun scanKeep a l = (a, l)`;
  - `scanResult_keep : scanResult δf scanKeep a₀ w = mealyRun δf a₀ w`;
  - `mealyRun_append`, the split over `l₁ ++ l₂`;
  - `mealyRun_length : (mealyRun δ a l).2.length = l.length`.
- **H-lay, the one A-only layout fact.** For a list of nonempty fields there are no two
  adjacent blank cells at `z, z + 1` with `0 ≤ z` and `z + 1 < fieldOffset ws |ws|`. Prove it
  by induction on `ws` through `fieldsTape_cons_shift`. Everything else comes from the public
  facts and target 1:
  - for `ws ≠ []` with nonempty fields, cell `0` is nonblank (target 1 at `j = 0`);
  - for `ws ≠ []`, every cell from `D - 1` on is blank, where `D = fieldOffset ws |ws|`
    (`length_joinFields_add_one`; probe, R-FIELD).
- **H-cmp.** The generalized compare items of the previous section.

1. **`fieldsTape_field`.**
   - Induct on `j`, generalizing `fs`. In the step, `fs' ≠ []`, so `fieldOffset_cons_succ` and
     `fieldsTape_cons_shift` reduce the claim to the induction hypothesis.
   - At `j = 0`, read the first field with `List.getElem?_append_left`/`_right` after
     `joinFields_cons_cons`. A lone field has no separator: its cell `|u|` lies beyond the
     list.
   - The empty layout supplies no index (round 2 note 10).
2. **The five identities.** Each target rewrites with `scanResult_keep`, except shiftLeft.
   - fold, map, shiftRight and carry: one `mealyRun` induction each, generalizing the
     accumulator. Carry also needs the private fact
     `mealyRun (scanCarry top next) false l = (false, l)`.
   - **shiftLeft does not re-induct.** Its forward pass is `mealyRun_keep`. Its backward pass
     `mealyRun (scanShift get set) b₀ w.reverse` is read off **target 4 at `w.reverse`**
     through `scanResult_keep`. Then `List.map_reverse` and `List.getLast?_reverse` give the
     final state. The word is the probe's list identity `shiftLeft_list` (proved there by
     `List.zipWith_append` and `List.reverse_zipWith`).
   - No setter laws: the identities hold for arbitrary `get`/`set`/`top`/`next` (round 1
     notes 18 and 20).
3. **`scanTM_run_ofCfg`.** One `catalog_trace_run` instance with `L = |w|`.
   - **Notation.** Write `f := mealyRun δf a₀ w`, `rev := f.2.reverse`, and
     `b r := mealyRun δb f.1 (rev.take (|w| - r))`.
   - **The families.**
     - Forward family `F r`: state `fwd (mealyRun δf a₀ (w.take r)).1`; head `i` at
       `pos + r`; tape `i` is `catalogTape (d.workTapes i) pos (f.2.take r ++ w.drop r)`.
     - Return family `R r`: state `bwd (b r).1`; head `i` at `pos + r - 1`; tape `i` is
       `catalogTape … (f.2.take r ++ (b r).2.reverse)`.
     - Everything else is `d`'s. The exit is the statement's finish.
   - **The steps.**
     - Forward write: `step_of_tapeAction_write`, then `catalog_write_middle` with
       `pre := f.2.take r`, `a := w[r]` and `b := f.2[r]`, and `mealyRun_append` on
       `List.take_succ`. Alternatively, state the forward tape as a written prefix over
       `d`'s cells and cite the public `catalog_write_take`.
     - Turn: the right delimiter (`hw` at `|w|`, never written) gives `R |w|`, via
       `step_of_tapeAction_move`.
     - Return write: `step_of_tapeAction_write` and `catalog_write_middle`, with
       `a := f.2[r]` and `b` the new backward output.
     - Entry: cell `pos - 1` (`hw` at `-1`, never written) gives the exit.
     - The exit is stationary.
   - **The finish.** `mealyRun_length` and `List.length_reverse` make the written word's
     length `|w|`, so `catalogTape`'s interval is the statement's.
   - **The clauses.** The cut holds because the family states are `fwd`/`bwd`. The trajectory
     is `pos + r ∈ [pos - 1, pos + |w|]`.
   - **One trace for both passes.** A forward and a separate backward induction is the
     `Sweep.lean` `sweep_run`/`sweep_run_reverse` shape (97%, extended screen); do not
     reproduce it.
4. **The compare (generalized in place, at `Catalog:680–813`).**
   - (a) `catalog_compare_stop` becomes
     `{Symbol : Type*} [DecidableEq Symbol] (u v : List Symbol)`, with the body verbatim
     (probe).
   - (b) The framed families:
     - `catalogCompareF fst snd d r :=`
       `{ d with state := some .run, workTapePos := fun j => d.workTapePos j + if j = fst ∨ j = snd then (r : ℤ) else 0 }`;
     - `catalogCompareR fst snd d v r` is the same with `.rewind v` and `(r : ℤ) - 1`.

     Bind `{x : List Symbol}` explicitly. The section's `variable {x : List Bool}`
     (`:169`) is in scope there.
   - (c) The framed `catalog_compare_trace fst snd u v d hstate hu hv δ hδ hp hs he t`
     concludes
     `(compareTM k fst snd).runFrom d t = catalogTrace (catalogCompareF fst snd d) (catalogCompareR fst snd d (decide (u = v))) { d with state := some (.done (decide (u = v))) } δ t`.
     It takes **no `fst ≠ snd`**. When the indices alias, `hu` and `hv` describe the same
     cells, every read agrees, and the old proof's case analysis goes through unchanged.
     compareTM's table is written with literal actions, so its steps keep the existing
     `Action.apply` proofs.
   - **The three rows.**
     - `compareTM_run_ofCfg` is (c) plus the three clauses, as in `transferTM_run_ofCfg`.
       Consume the frozen, now unused `hne` with `have _ := hne`, commented that the shared
       trace covers aliasing (D2; pitfall 1).
     - `compareTM_run` and `compareTM_spaceUsedByTape` apply (c) at `u := w fst`,
       `v := w snd`, `d := Cfg.ofWords .run w`. Both delimited-word hypotheses close by
       `intro p _ _; simp [Cfg.ofWords]`, and the finish is the canonical seam by `rfl`
       (probe, R-CMP).
   - **The old canonical families and trace are replaced, never kept beside the new ones.**
     Keeping both would be a second trace of the family.
5. **The seeks.** H-pass with these families. `pos` is `d.workTapePos i`, and only head `i`
   moves. "Blank" refers to `d`'s cells, transported by `hw`. Every step is
   `step_of_tapeAction_move`, or `step_of_inputMoveAction` at a stationary stop.
   - **skip**: `L = |w|`. `F r` is `d` with the head at `pos + r`, in state `run`. The right
     delimiter takes `F L` to `done` at `pos + |w| + 1`.
   - **skip back**: `L = |u| + 2`.
     - `F 0 = d`; `F 1` is `gap` at `pos - 1`; `F r` is `back` at `pos - r` for
       `2 ≤ r ≤ |u| + 2`.
     - The left delimiter (`pos - |u| - 2`) takes `F L` to `done` at `pos - |u| - 1`.
     - Its first two steps are unconditional: no cell is read (round 1 note 12).
   - **seek end**: `L = D`. `F r` sits at `pos + r`, in `gap` iff `r > 0` and cell
     `pos + r - 1` is blank. `F D` is `gap` on the second blank and steps in place to `done`.
     The no-early-exit obligation is H-lay.
   - **seek start**: `L = D + 3`.
     - `F r` sits at `pos - r` for `r ≤ D + 2`, in `gap` iff `r > 0` and cell `pos - r + 1`
       is blank. `F (D + 3)` is `back` at `pos - D - 1`. The exit is `done` at `pos - D`.
     - No early turn:
       - at `r = 1` and `r = D + 1`, by `hcur` and the nonblank first cell;
       - in between, by H-lay;
       - for `ws = []`, `D = 0` and the run takes 4 steps.
   - **Do not strengthen or weaken any hypothesis.** `ws ≠ []` is necessary (round 1 note
     13). A head on `seekEndTM`'s stopping blank is not a `seekStartTM` entry; consumers
     reposition (round 1 note 14).
6. **`seamCompTM₂_run_ofCfg`.** No new induction (round 1 note 31, round 2 note 30). Both
   branches are closed in the probe from public lemmas.
   - **Branch `e₁`.**
     - The outer seam's cut: the inner composite never shows `Sum.inl e₂`.
       - Before `T₀`, by `hcut` through `seamCompTM_runFrom_left`.
       - At `T₀`, by `he`.
       - After `T₀`, its states are `Sum.inr`, by the inner right lockstep.
     - Then `seamCompTM_runFrom_left` on the outer seam at `T₀ + 1 + t`, followed by the
       inner right lockstep.
   - **Branch `e₂`.**
     - The inner prefix reaches `Sum.inl e₂` at `T₀`, never having met `e₁`.
     - Then the outer right lockstep finishes.
     - Finally, `(c₁.mapState Sum.inl).mapState (fun _ => entry₂) = c₁.mapState (fun _ => entry₂)`
       by `Cfg.ext`.
   - **The right lockstep** is Seam's private `seamComp_right` (`Seam:216`), or equivalently
     `seamCompTM_run_ofCfg` (`:539`) at `h₂ := rfl` (the probe's form, since it cannot see
     the private lemma).
   - Seam's new `phaseHostTM` (`:774`) is not involved.

## Gate guidance (binding; `audits/s12-8-statements-resolutions.md`)

The gate closed with every stream-A statement true as stated, and no statement change. Its
notes bind the fill:

- **Compare** (round 1 note 10, round 2 note 11). Generalize the existing trace and derive
  the canonical row from it. Route 4 is that derivation, adjusted for the canonical row's
  aliased case.
- **Two-exit seam** (round 1 note 31, round 2 note 30). Reuse the promoted prefix lemma and
  the existing right lockstep.
- **Duplication** (note 38 of both rounds). "enforce the promised shared trace at fill"; a
  text-screen zero is not a semantic no-duplication proof.
- **Seeks** (round 1 notes 13–14; round 2 notes 14–15). The `ws ≠ []` exclusion is necessary,
  and the end-to-start adapter belongs to consumers.
- **Scan** (round 1 notes 15–20; round 2 notes 16–21). The accumulator may be any type (the
  scan's `A : Type`). The identities need no setter laws.

## Cited infrastructure (public and proved at the issue commit)

- **`Build/Catalog`:**
  - `catalogTrace` (`:335`) and `catalog_trace_run` (`:349`);
  - `catalog_write_take` (`:418`);
  - the pre-issue Part 3 lemmas listed above (`:11358`–`:11505`);
  - `compareTM` (`:262`) and `FlagPhase` (`:160`);
  - the R3 framed rows as patterns: `transferTM_run_ofCfg` (`:1025`), `clearTM_run_ofCfg`
    (`:1110`);
  - Part 3's frozen definitions: `tapeAction` (`:11341`), `inputMoveAction` (`:11348`),
    `joinFields` (`:11426`), `fieldsTape` (`:11431`), `fieldOffset` (`:11439`), `SeekPhase`,
    the four seek machines (`:11597`–`:11737`), `mealyRun` (`:11794`), `scanResult`,
    `ScanPhase`, `scanTM` (`:11829`), and the five step functions (`:11884`–`:11904`).
- **Same-file private helpers to cite:** `catalogTape` (`:406`), `catalog_write_middle`
  (`:844`), and `catalog_space_bound`/`catalog_space_one` (`:384`/`:396`, for the compare
  space row).
- **Machine model:**
  - `MultiTapeTM.step`, `runFrom`, `runFrom_zero`, `runFrom_succ_eq_step(')` and
    `runFrom_add` (`Deterministic`);
  - `Action.apply`, `Cfg.ext`, `Cfg.workTapeSymbols` and `moveInputPos_zero`
    (`Configuration`);
  - `FinTM.bufferTape` with `_nat`, `_left` and `_nil` (`Simulation`);
  - `Cfg.ofWords` (`Build/Convention`).
- **`Build/Seam`:**
  - `seamCompTM` (`:125`), `seamCompTM₂` (`:600`), `seamCompTM_runFrom_left` (`:198`) and
    `seamCompTM_run_ofCfg` (`:539`);
  - in-file privates `seamComp_right` (`:216`), `seamComp_step_left`/`_right` and
    `seamComp_dispatch`;
  - `Cfg.mapState` (`StateRenaming`).
- **Lean core, names checked in the probe:** `List.zipWith_append`, `List.reverse_zipWith`,
  `List.getLast?_reverse`, `List.head?_reverse`, `List.getLast?_cons`, `List.map_reverse`,
  `List.take_succ`, `List.take_succ_cons`, `List.getElem?_append_left`/`_right`,
  `List.intersperse_cons₂`, `List.flatten_cons`, `List.takeWhile_cons`,
  `List.dropWhile_cons`, `List.zipWith_cons_cons`, `ite_self`, `SignType.pos_eq_one`,
  `SignType.coe_one`. There is no `List.intercalate_cons_cons` at this pin; use
  `joinFields_cons_cons`.

Every module upstream of Catalog (14 modules) and Seam (7) is sorry-free, so the **"proved
modulo" set is empty**, and a complete delivery has no `sorryAx`. The internal dependencies
are the table's "Uses" column. Catalog and Seam do not import each other: neither may cite
the other.

## Inherited audit contracts (verbatim; binding on the fill)

From `audits/s12-8-statements-findings.md` (round 1):

> | 10 | note | Build/Catalog.lean · `compareTM_run_ofCfg` | The framed comparison returns the correct verdict at exactly `2*δ + 2`, restoring the entire configuration except control. | Choose δ as the first unequal index or the first exhausted word length. The table takes δ matching right moves, one left turn carrying the verdict, δ left moves across the intact common prefix, and one right move from the left delimiter. These phases exclude every `done` state before the stated time and keep both heads between their start minus 1 and start plus δ. Checks: two empty words, first-symbol disagreement, and a proper prefix; displaced heads and arbitrary exterior cells do not affect these reads. | No statement change; generalize the existing compare trace and derive the canonical row at fill. |

> | 13 | note | Build/Catalog.lean · `seekEndTM`, `seekEndTM_run_ofCfg` | The nonempty-table end seek has the stated `D + 1` time and head displacement D. | Here D is the sum of field lengths plus one delimiter per field. Every cell through the first terminal blank costs one right move, and the second terminal blank costs one stationary move into `done`; nonempty fields prevent an earlier double blank. Checks: one singleton field, several unequal-length nonempty fields, and arbitrary nonblank framing beyond the second terminal blank. For an empty table the actual machine instead takes two steps and moves right once, explaining the necessary `ws ≠ []` hypothesis. | No statement change; settle the empty-table layout as in recommendation 42. |

> | 14 | note | Build/Catalog.lean · `seekStartTM`, `seekStartTM_run_ofCfg` | The start seek is true on its stated entry domain, with exact time `D + 4`. | The current nonblank cell and preceding field layout give D + 2 left moves to the second blank before the table; two right moves finish at its start. This proves the cut and stated trajectory. Checks: no preceding fields gives four steps; one preceding singleton gives six; several preceding fields add exactly their lengths and separators. A head on the blank returned by `seekEndTM` does not satisfy `hcur` and must first be repositioned. | No statement change; make the end-to-start adapter explicit in table consumers. |

> | 15 | note | Build/Catalog.lean · `mealyRun`, `scanResult`, `ScanPhase`, `scanTM_run_ofCfg` | The two-pass semantics and exact `2*w.length + 2` contract are correct. | `mealyRun` threads the accumulator while producing one symbol per input symbol. `scanResult` applies the backward transducer to the reversed forward output, starting from the forward final accumulator, then reverses the output back. The machine performs w.length forward writes, a delimiter turn, w.length backward writes, and the left-delimiter return; it writes only inside the word and reaches `done` only on the final step. Checks: empty word, singleton word, and forward/backward Boolean negation (the backward pass must read the rewritten cell, giving the original word again). | No statement change. Finite-state consumers must instantiate the accumulator with a finite type. |

> | 31 | note | Build/Seam.lean · `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | Both branches have exactly one dispatch step and support arbitrarily long continuations. | The definition nests the e₁ seam inside the e₂ seam. On e₁, the outer exit `Sum.inl e₂` is avoided before the host exit by hcut, at the exit by e₁ ≠ e₂, and afterwards because the inner continuation lives in the other summand (or is halted). On e₂, the inner seam stays on its host prefix and the outer seam dispatches directly. Checks: T₀ = 0, an immediately halting continuation, and a continuation run longer than the host time; all give the displayed state embeddings and `T₀ + 1 + t`. | No statement change; reuse the promoted prefix lemma and the existing right lockstep. |

> | 38 | note | Build/Catalog.lean · action helpers/seek family; Build/Scan.lean · writers; copy-text evidence | No new wholesale duplication of proved material is established by the twelve new pairs. | … The seek machines have different stop/return behavior, so 100% tiled coverage of the short skip text is not equality of transition tables; the two writers likewise have different return control. These are small related definitions, with no copied new proofs. … | No new debt major. Record the same-file similarities, preserve the existing ledger acknowledgments, and enforce the promised shared trace at fill; do not treat a text-screen zero as a semantic no-duplication proof. |

The round-1 claims for the other targets (no statement change in each case):

- note 9: "The layout and framed-field statement are true, including empty fields."
- note 11: "Skip is a read-only forward traversal ending one cell beyond the right delimiter."
- note 12: "Skip back is the position inverse of skip, with time u.length + 3."
- note 16: "The fold instance returns `(w.foldl δ a₀, w)`."
- note 17: "The map instance returns `(a₀, w.map f)`."
- note 18: "The right-shift identity is true for arbitrary get/set functions." (proposed fix:
  "instantiate get/set with the actual mark projection and update")
- note 19: "The left-shift identity has the correct order and boundary value."
- note 20: "The carry identity describes exactly the top prefix, first non-top digit, and
  unchanged suffix."

From `audits/s12-8-statements-r2-findings.md` (round 2):

- note 11 (compare): "Comparison has the stated verdict, restoration, first-exit time, and
  trajectory." Proposed fix: "No statement change; generalize the existing trace at fill."
- note 30 (two-exit seam): "The two-exit composition and its one-step dispatch bound are
  correct." Evidence: "The promoted prefix theorem follows the source until and including
  the first exit time. At `e₁`, the inner seam dispatches into its right summand, which can
  never equal the outer exit `Sum.inl e₂`; at `e₂`, the outer seam dispatches directly."
- note 38 (duplication), proposed fix: "No debt major. Preserve the existing acknowledgments
  and enforce the promised shared traces during fill."

## Ground rules (binding)

1. **File ownership.** Only `Build/Catalog.lean` and `Build/Seam.lean`. **No new files.**
   - In Catalog: the twelve Part 3 bodies, plus new `private` helpers. Put them in Part 3,
     except the compare items, which stay at their current location. Add the two
     authorized body swaps and the four authorized private generalizations.
   - In Seam: one body, plus `private` helpers if any (none expected).
   - List every new declaration with its role.
2. **Statement freeze.**
   - **What is frozen:**
     - the 13 targets;
     - every landed Part 3 definition: `tapeAction`, `inputMoveAction`, `joinFields`,
       `fieldsTape`, `fieldOffset`, `SeekPhase`, `skipTM`, `skipBackTM`, `seekEndTM`,
       `seekStartTM`, `mealyRun`, `scanResult`, `ScanPhase`, `scanTM`, `scanKeep`,
       `scanFold`, `scanMap`, `scanShift`, `scanCarry`;
     - the pre-issue public lemmas (the three step lemmas, the six layout facts,
       `catalog_write_take`), together with their bodies;
     - the R3 public surface, including `compareTM` and the statements of `compareTM_run`
       and `compareTM_spaceUsedByTape`;
     - `catalogTrace` and `catalog_trace_run`;
     - `seamCompTM₂`, `seamCompTM_runFrom_left`, `phaseHostTM` and the rest of Seam's public
       surface.
   - **What is not allowed:** renames, re-signatures, restatements, and attribution edits.
   - **Exceptions:** only the authorized compare items above.
   - **Docstrings stay true (D3).** If your proof would make a docstring sentence
     inaccurate, correct that sentence in one sentence and flag it. Example: R8.1's "The
     canonical `Turing.compareTM_run` re-derives from this form" under route 4, where both
     rows re-derive from the same framed trace. Otherwise docstrings stay. Flagged sketch
     appendices are allowed.
3. **Status text.** Only these may change, from "sorried / pending" to "proved"; flag each:
   - Catalog's module-docstring `Status` paragraph (its "Part 3 below is the exception"
     sentence);
   - the `## Part 3 … (statement layer)` labels and Part 3's section docstring;
   - the `## Main results` label "Part 3 (statements)";
   - Seam's "**Status: proved, except the §12.8 row**" paragraph.

   New exports: none.
4. **Escalation** on anything unprovable as stated: stop on that item, record the
   obstruction, and continue with the rest.
5. **No touching other sorries.** Cite proved material, the pre-issue lemmas included; never
   re-prove it.
6. **Imports unchanged.**
   - Catalog imports `Build.Loop`, `Encoding`, `Mathlib.Data.Nat.Size` and
     `Mathlib.Tactic.DeriveFintype`.
   - Seam imports `Build.Convention`, `StateRenaming` and, since the pre-issue commit,
     `Build.Embed`.

   A Mathlib import is allowed only if a needed lemma requires it; flag it. No TCSlib import
   may be added.
7. **One proof per shared argument**:
   - one compare trace, generalized and not added;
   - one scan trace instance covering both passes;
   - one one-pass helper for all four seeks;
   - one A-only layout fact (H-lay), the rest cited;
   - one keep reduction for the identities, with shiftLeft citing shiftRight;
   - the public step lemmas for every single step;
   - no new induction in Seam.
8. **Size.** Report the final line counts of both owned files. (Catalog is 11,970 lines at
   `5afed90b` and Seam 815; Catalog's split belongs to 12.2c.)
9. **Continuation budget.** If your budget runs out, deliver a partial zip. Its `REPORT.md`
   states:
   - which targets are proved;
   - which `private` helpers remain `sorry` (partial delivery only, each with a "Proof
     sketch");
   - which proved targets are proved modulo them.

## Duplication governance (binding)

Run the text-level screen **before and after**. The population is the statement gate's
round-2 population. Its base at `5afed90b` (`audits/logs/s12-8-fill-A-screen-base.txt`) is **550
declarations, 415 pairs, 121,938 characters**. The round-2 log's 535 / 408 / 120,748, plus
the pre-issue commit's 15 declarations and 7 pairs, accounts for every difference.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/{Catalog,Seam,CounterLoop,Embed}.lean \
  TCSlib/Complexity/TuringMachine/{Simulation,SymbolLift}.lean \
  TCSlib/Complexity/ClassPSPACE/TQBF.lean \
  TCSlib/Complexity/TuringMachine/Build/{Scan,InputCall,CfgRecord}.lean
```

Also run the **extended watch population**: the same files plus
`TuringMachine/{Sweep,StateRenaming}.lean`. Its base is **568 / 421 / 123,669** (D6:
quote both).

- **No new cross-file pair** with an owned-file declaration on one side.
- **Catalog already carries acknowledged copied material** (ledger §12.8: 318/459 = 69.3%).
  Under `workflow.md` §4, any new copy in Catalog forces a mandatory `backlog.md` §1
  human-review item, so **"new copies: none" is binding** here (D5). Seam has no members;
  keep it that way.
- **Known hazards:**
  - (1) The generalized compare trace beside a surviving canonical one. Replace; never keep
    both.
  - (2) The framed compare's three-clause closing against `transferTM_run_ofCfg`,
    `copyTM_run_ofCfg` and `clearTM_run_ofCfg`, and the swapped compare rows against the R3
    space rows. These pairs are expected, inside the acknowledged R3 sibling family (ledger,
    12.2c item 5): list and justify them; do not factor them in this batch (D4).
  - (3) The scan's forward and return steps against each other and against
    `catalog_increment_trace` (the same `catalogTape` and `catalog_write_middle`
    bookkeeping). Use one trace instance and cite the helpers.
  - (4) The four seek rows' closings: H-pass exists to prevent these pairs.
  - (5) The scan trace against `Sweep.lean`'s `sweep_run`/`sweep_run_reverse`, and the
    Mealy lemmas against `sweepFold_append` (extended population).
  - (6) Any private re-proof of the pre-issue lemmas, the step lemmas or the layout facts.
    The base already pairs `step_of_tapeAction_move ↔ _write` at 100%: that is the
    maintainer's landed pair, not yours to factor.
  - (7) Seam: no re-walk of `seamComp_right`'s or `seamCompTM_runFrom_left`'s inductions.
- **List every new or changed in-file pair** with a one-line justification. Outside hazard
  (2), a pair at 90% or more is a copy: factor it.
- **Quote both outputs** of each population in `REPORT.md`, which carries **"new copies:
  none"**.

## Environment and verification

- Lean 4 v4.25.0 with mathlib pinned; run `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/s128-fill-A.txt`. It lists 99 modules: the upstream
  closure of the two owned files and of every module downstream of them, with the root
  `TCSlib` and `TCSlib/ComputationalModels` excluded, recomputed at `5afed90b`.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/s128-fill-A.txt )
  ```

- **Base sorry-warning set: 41.**
  - **Yours (13):** `Build/Catalog` 12 and `Build/Seam` 1.
  - **Downstream (19):** `Build/CfgRecord` 5, `ClassPSPACE/TQBF` 4, `Build/Scan` 4,
    `Build/InputCall` 2, `Build/Zone` 2, `Build/CounterLoop` 1, `Codes2Tape` 1.
  - **Upstream (9):** `ClassOracle/Classes` 1, `SpaceComplexity/Constructible` 2,
    `SpaceComplexity/ConfigGraph` 3, `SpaceComplexity/Inclusions` 2, `NDCodes` 1.
- **Final checks:**
  1. **Owned modules:** zero errors and zero sorry warnings. No new linter warnings: compare
     each module's non-sorry output with your bootstrap.
  2. **The 15 downstream modules:** zero errors, and sorry warnings exactly the base's (19).
     The modules are `Build/{CfgRecord,Scan,CounterLoop,InputCall,Zone}`, `Codes2Tape`,
     `ClassPSPACE/TQBF`, `ClassPSPACE`, `CookLevin/Hardness`, `ClassNP/Tautology`,
     `ClassNP`, `ClassOracle/SATOracle`, `ClassOracle`, `CookLevin`, and the `TuringMachine`
     facade. Since the pre-issue commit Seam also reaches `InputCall`, `CfgRecord` and
     `TQBF`; the set of 15 is unchanged.
  3. **The probes:** re-run the pre-ship probe and its visibility check: 0 errors.
- **Axiom prints** for the 13 targets **and** the two swapped rows `compareTM_run` and
  `compareTM_spaceUsedByTape`: within `[propext, Classical.choice, Quot.sound]`, with no
  `sorryAx`.
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  must report 0 FAIL. The Catalog size WARN is pre-existing.

## Out-of-scope sorries you will see (leave every one untouched)

- **Downstream: other §12.8 streams and earlier work.**
  - `cfgRecord_inj`, `recordValid_iff`, `exists_recordStepTM`, `exists_recordEqTM`,
    `exists_recordTestTM` (`CfgRecord`);
  - `writeConstTM_run_ofCfg`, `writeAdvTM_run_ofCfg`, `inputCopyTM_run_ofCfg`,
    `inputFoldTM_run_ofCfg` (`Scan`);
  - `exists_inputCallTM`, `exists_inputSeekTM` (`InputCall`);
  - `expandTM_run_ofCfg` (`CounterLoop`);
  - `exists_zoneShiftInTM`, `exists_zoneShiftOutTM` (`Zone`);
  - `exists_uniformMachineCode2` (`Codes2Tape`);
  - `exists_adjacency_codec_cnf`, `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`
    (`TQBF`).
- **Upstream, in the order list:**
  - `POracle_eq_P_of_mem_P` (`ClassOracle/Classes`);
  - `spaceConstructible_logSpace`, `spaceConstructible_linear` (`Constructible`);
  - `NSPACE_subset_exp_dtime`, `NL_subset_P`, `polyTimeReducible_of_mem_NL` (`ConfigGraph`);
  - `NP_subset_PSPACE`, `SAT3_mem_PSPACE` (`Inclusions`);
  - `exists_effectiveNDMachineCode` (`NDCodes`).

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 13/13, or the partial frontier (rule 9); the base hash and the ancestor check; the
      re-run probes.
- [ ] Every new declaration with its role: H-pass, H-scan, H-lay, the scan and seek
      families, and the carry-clear fact.
- [ ] The authorized compare items, each flagged:
  - [ ] the two body swaps, with statements byte-identical (comment-stripped diff);
  - [ ] the four private generalizations and their synchronized docstrings;
  - [ ] the `hne` consumption.
- [ ] Any one-sentence docstring correction (D3), flagged.
- [ ] Imports, requested shared lemmas, escalations, or "none"; appendices and status updates,
      each flagged.
- [ ] Duplication:
  - [ ] both screens of both populations, before and after;
  - [ ] every new or changed pair justified, with hazard (2)'s pairs named;
  - [ ] "new copies: none".
- [ ] File sizes; the final sweep tail; fifteen axiom prints; the lint line; no new linter
      warnings. The diff touches only the two owned files.

## Known pitfalls at this pin (hard-won, probe-observed)

1. **A sorried body suppresses `linter.unusedVariables`; a filled body does not**
   (`S128FillAProbe-lint`). Under route 4, `compareTM_run_ofCfg`'s frozen `hne` is unused.
   `clear hne` does **not** count as a use; `have _ := hne` does.
2. **`linter.unusedSimpArgs` is active.** After the compare swaps, drop `catalogCfg` and the
   other dead simp arguments. Do not leave new warnings.
3. **`variable` scope.** Catalog's `variable {k : ℕ} {x : List Bool}` (`:169`) ends at
   `end Turing` (`:1738`). Part 3 reopens `namespace Turing` (`:11333`) without it, so bind
   `{k : ℕ}` in every Part 3 helper. In the R3 section, generic helpers must bind
   `{x : List Symbol}` explicitly, as `catalog_clear_trace` does.
4. **Structure updates.** A field continued on the next line, to the left of the first
   field's column, fails to parse ("expected '}'"; `S128FillAProbe-lint`). Use the newline
   layout of the landed statements: `{ d with`, then one field per line.
5. **The step lemmas' state arguments are implicit** (`{q q'}`). Pass them by name when
   unification cannot see them, e.g. `(q' := .fwd (δf a γ).1)` (probe).
   - Their results carry `inputPos := moveInputPos c.inputPos inp`: close it with
     `moveInputPos_zero`.
   - In your own proofs, `by_cases hj : j = i <;> simp [hj]` leaves `Function.update … j`
     goals: `subst hj` first.
6. **Sign casts.** `push_cast` does not reduce `↑SignType.pos`: use
   `SignType.pos_eq_one, SignType.coe_one`, or `SignType.cast` as the R3 proofs do.
7. **Summand types.** `Cfg.mapState` chains in the Seam row need explicit summand types,
   e.g. `(Sum.inl : S₀ → S₀ ⊕ S₁)`, or elaboration stalls on a metavariable.
8. **ℕ/ℤ coercions.** `fieldOffset` is `ℕ` and the statements cast it, so supply `Int.toNat`
   facts explicitly before `omega`, as `fieldsTape_cons_shift`'s proof does.
9. **The degenerate return family.** `catalogTrace F (fun _ => D) D L` reduces by
   `simpa [catalogTrace]` (probe). The exit `D` must be stationary: every `done` anchor here
   is `inputMoveAction 0`.
10. **The canonical compare admits `fst = snd`.** Its `catalogCompareF`/`R` move one tape
    once when the indices alias, so do not assume two distinct tapes anywhere in route 4.
11. **`ScanPhase A` needs `A : Type`**, not `Type*`. `scanTM` reads only tape `i`, so the
    other tapes' cells are arbitrary and untouched.
12. **The linter needs a literal "Proof sketch" before every `sorry`.** This matters only
    for a partial delivery.
