# Ch3–4 fill campaign — C1, wave 1, R continuation 2: the interpreter core for nondeterministic codes (`Turing.exists_ndInterpreterCore`, `NDCodeSimulator.lean`)

> **Megafill A, item 1 of 3** (cover brief `megafill-A.md`; addendum v2.4, Part 3). The
> preflight, the toolchain, the clone and the cache are done once for the whole queue. For this
> item: create its branch from the shared base (below), make your first edit, **re-bootstrap your
> order list**, then follow this brief. **Budget: 4 hours** from your branch's creation; then
> deliver this item's zip, partial if need be, and start item 2.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (the C1 host-contracts gate,
    `campaign/gates/12-c1-hosts-statements/findings.md`, PASS 0/0/11; resolutions
    `campaign/gates/12-c1-hosts-statements/resolutions.md`; the prefix clause is the repaired one
    of its minor M4);
  - C1's design (`campaign/items/c1/C1-design.md`; `R` is §3.6, the replay route is the user's
    decision 3) and C1's fill plan (`campaign/items/c1/C1-fill-plan.md`; you are wave 1's R);
  - **the hosts:** H1's hosted counter loop over H2's step block (`Build/StepBlockLoop`, PR #94),
    Z1 (`Build/VirtualInput`), the prefix canonizer (`UniversalStartup`), the install call
    (`Build/Loop`), the replay machine (`ChoiceReplay`), R1′'s returning embedding
    (`Build/Embed`);
  - **the seam layout** (PR #124; statement gate passed in round 2,
    `campaign/gates/43-seam-layout-statements/`): `Turing.exists_seamLayoutTM`
    (`Build/SeamLayout`), sorried at the base (its fill was delivered complete on 2026-10-22 and
    lands after your base);
  - **the window copier** `Turing.exists_inputWindowCopyTM` (`Build/InputWindow`), proved at
    the base (PR #137);
  - **the rewind row** (PR #138, the user's ruling of 2026-10-18 on the last round's gap 2):
    `Turing.rewindTM` and its framed run `Turing.rewindTM_run_ofCfg` (`Build/Rewind`), and its
    API gate `campaign/gates/55-rewind-row/`;
  - **the API PRs** (the user's "Everything" rule, 2026-10-16): #112, #116, #118, #119 and #122
    (**`Turing.counterValue_eq`** and `codeBitsNat_eq`);
  - **the earlier rounds:** round 1's report and review
    (`campaign/fills/c1/reports/core-1-REPORT.md`,
    `campaign/fills/c1/reviews/core-1/REVIEW.md`); continuation 1's three rounds, the last of which
    delivered 16 unelaborated drafts (`campaign/fills/c1/reports/core-3-REPORT.md`) and **its
    review** `campaign/fills/c1/reviews/core-cont1-r3/REVIEW.md`, which elaborated them, repaired
    8 sites and verified the result (`out/overlay-verified.lean.txt`, `out/repairs.diff`);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.4**: Part 1, the resources and the cache for the Mathlib roots only; **Part 3, the
    megafill**, under which this session runs), and the copy-text screen v3
    `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/c1/inputs/c1-fill-core-cont2/`): the overlay (your
    file with the four imports, the four supplied drafts and the 16 verified ones), the import
    probe and the screen population. Also the order list
    `campaign/fills/c1/orders/c1-fill-core-cont2.txt`, the base sorry set, the screen base and the
    pre-ship log (`campaign/fills/c1/logs/c1-fill-core-cont2-*`).
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of
  `campaign/standards/fill-environment-addendum.md` and its Part 3): the preflight, the
  toolchain, the clone and the cache for the whole queue's Mathlib roots. If Lean cannot start,
  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-core-cont2 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-core-cont2.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** After each phase below, commit and write `fill-c1-core-cont2-cp<N>.zip`
  with the same contents as of that commit (the final sweep may be your module's check only), so
  that a lost workspace loses at most one phase. Deliver the latest if the session ends early.
- **If Lean never runs** (E-RES after the preflight's retry), do not draft proofs blind: the last
  round's 16 unchecked drafts had 7 errors and one rule-10 failure. Deliver the environment
  report only.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #137** (`2ff214c5`, #137's merge; #140,
  #138, #133, #134 and #136 merged before it). `NDCodeSimulator.lean` there is #94's file with its
  module docstring (147 lines); no round's work was landed.
- **Your first edit makes your file equal to the overlay**
  (`NDCodeSimulatorOverlay.lean.txt`, 769 lines): the four imports after line 8, and the 20
  private declarations after the replay canonizer's `sorry`. It is the last round's review's
  `out/overlay-verified.lean.txt` with the import of `Build/Rewind` added after the other three,
  so **its line numbers are the review's plus one**. Every probe and measurement below was run on
  the overlay, against the olean snapshot `oleans-lg4c2` (the tip's merged-tree replay, whose
  `Build/InputWindow` is the statement-identical build before #137's proof).
- **In flight, merging after your base and invisible to it:** #139 (`Build/StepClock`), #143
  (`Build/ZoneRebalance`), the seam layout's landing (`Build/SeamLayout`), MIG-12's fill
  (`Build/CfgRecord`); later in this session, on their own branches, UN
  (`Diagonalization/NTimeHierarchy`, downstream of your file) and the canonizer (`CodeSimulator`,
  upstream of it); on another host, U2-S (`UniversalK`), F5 (`Build/InputDevice`) and G4
  (`Build/ZoneRebalance`). Cite nothing they add.
- **Your file's other stub,** the replay canonizer `exists_replayCanonizer` (line 95), is wave
  2's and stays sorried: you cite its statement.

## Parallel batches this round

None in `NDCodeSimulator.lean`. The seam-layout fill has proved the contract you cite; its
proof lands after your base. Your consumers come later: UN (the universal NDTM) and the
diagonalizer's
middle rung (C1-E).

## What this is

**C1's interpreter core `R`** (C1's design §3.6): one deterministic machine, uniform over codes,
that runs the coded NDTM's branch along a guessed stream at linear overhead. One target, frozen:
1. **`Turing.exists_ndInterpreterCore`** (line 750): for every effective scheme `c`, a machine
   `R` with a stream tape `j` and verdicts `accept ≠ reject`, such that for every code `α` there
   is `C`: from `entry` on `z = ⟨⟨bits t, α⟩, x⟩` with a stream `s` (`t ≤ |s|`) on tape `j`, `R`
   reaches `accept` iff the decoded machine's branch on `x` along `s.take t` halted with output
   `[true]`, at a time `T ≤ C·(t + 1)` with no earlier verdict, and
   `T ≤ C·(t' + |x| + |bits t| + 1)` whenever the branch along `s.take t'` already halted (the
   prefix clause).

**Where it stands.** The 20 privates of the overlay elaborate and pass the seal test, the probe,
the screen and lint at continuation 1's base and at the tip of 2026-10-18 (the review's (b)–(d)).
They cover every piece of the route except **the startup's assembly and the final assembly**:
- the header: one prefix pass captured with a first live return (`ic_header_capture`);
- the table: the canonizer through the install interface (`ic_table_call`), the layout
  (`ic_layout_call`), and `Rep` from the layout's end (`ic_replay_rep`);
- the window: `ic_input_suffix`, `ic_window_call`;
- the loop and the verdict: `ic_loop_replay`, `ic_verdictTM`, `ic_verdictTM_run`, the phase
  family `ic_loopPh`/`ic_loopPh_fintype`/`ic_loopPiece`/`ic_loopRedirect`, `ic_loopHost`,
  `ic_loopHost_run`, and `ic_replay_tail` (the represented start to the first verdict, both
  clauses);
- the semantics `ic_replay_window`, and the arithmetic `ic_time_ledger` (both clauses, one
  per-code `C`).

**What is open:** the two passes joined; the counter copy; the window placed; the input and
work-tape rewinds; the install and layout placed; the represented start established at the
loop's entry; the whole machine assembled; the target. The review's gaps 1–3 are resolved in the
route below.

**Proved modulo, exactly:** `Turing.exists_replayCanonizer` (your file, wave 2) and
`Turing.exists_seamLayoutTM` (the seam layout, sorried at your base). Cite their statements; never
their bodies.

**Keep the 20 privates** (you may restate any of them; report each change and its reason).

**The published lemmas your route reads** (ground rule 10), the last round's list plus the
rewind:
- **the header** (`UniversalStartup`): `prefixCanonTM`, `prefixCanonTM_eq`,
  `prefixCanon_complete`; `FinTM.pairExtractTM_fst`, `_snd`; `pairDecode_pairEncode`,
  `length_pairEncode`, `pairEncode_eq`;
- **the input rewind** (`Simulation`): `FinTM.rewind_heads` (or `FinTM.timed_rewind`), over a
  private leaf table of yours built from `controlAction` (`controlAction_apply`);
- **the work-tape rewind** (`Build/Rewind`): `rewindTM`, `rewindTM_run_ofCfg`;
- **the counter copy** (`Build/Catalog`): `copyTM`, `copyTM_run_ofCfg` (its heads end where they
  started);
- **the capture** (`Build/Embed`): `embedSilentRetTM`, `embedSilentRetTM_run`, `embedSilentCfg`
  and `embedSilentCfg_cap`, `embedSilentCfg_*`; `MultiTapeTM.exists_first_halt`,
  `MultiTapeTM.initCfg_eq`, `Cfg.init`'s fields;
- **the installation** (`Build/Loop`): `FinTM.exists_installCallTM`, `stateWord`, stated through
  `Cfg.ofWords` seams (`Cfg.ofWords_state`, `_inputPos`, `_workTapes`, `_workTapePos`,
  `_output`);
- **the layout** (`Build/SeamLayout`): `exists_seamLayoutTM`, with `serializeK_eq`,
  `unaryFin_eq`, `FinTM.bufferTape_of_neg`;
- **the window:** `Turing.exists_inputWindowCopyTM`, with `counterValue_eq` and
  `counterValue_bits`;
- **the loop** (`Build/StepBlockLoop`): `StepBlock.hostedLoopTM_run`, `StepBlock.hostedLoop_read`,
  `StepBlock.Rep_iff`, `exit_true`, `exit_false`, `summaryTape_eq`, `tableTape_eq`,
  `outputSummary_nil`, `outputSummary_true`, `summaryCells_eq`, `vhostCfg`'s fields and
  `vhostBank_eq`, `counter_cfg_eq`;
- **the code and its replay:** `serializeK_eq`, `tableBitsK` read opaquely,
  `CodeNDTM.serialize_eq_tableBitsK` (proved, your file), `CodeNDTM.toFinNDTM_k`, `_State`,
  `_tm`, `NDTM.replayTM_runFrom`, `replayTM_q₀`, `_tr`, `withChoiceTape`'s fields,
  `NDTM.runWith_initCfg_take`, `NDTM.initCfg_eq`;
- **composition:** `seamCompTM_run_ofCfg`, `seamReleaseTM_firstReturn`, `phaseHostTM_run`,
  `embedSilentTM_runFrom` and `embedSilentCfg_*`;
- **the model:** `MultiTapeTM.step_of_some`, `step_of_halt`, the run algebra, `Action.apply`'s
  fields, `Cfg.mapState`'s fields, `FinTM.computesInTime_iff`; `length_bits_le_self`.

**Read first:**
- the target's docstring, whose proof sketch is binding where this brief does not refine it;
- the last round's review, **(f)**: the three route gaps and the pitfalls, resolved below;
- `rewindTM_run_ofCfg`'s statement, and its gate's probe
  (`campaign/gates/55-rewind-row/evidence/RewindProbe.lean.txt`): its first example derives your
  form (a word at the origin, the head just past it, the empty word included) from the contract
  alone. **It is a reference, not a citation**;
- `StepBlock.hostedLoopTM_run`, `hostedLoop_read`, `exists_seamLayoutTM`, and the seam-layout
  gate's consumer probe (`campaign/items/c1/seam-layout/r2/SeamLayoutConsumerR2.lean.txt`,
  derivation 3), as in the last brief;
- `UniversalStartup`'s `prefixCanon_complete` and the chapter-1 startup it serves
  (`universalCanonTM`, `universalCaptureTM`): the model, not a citation of their privates.

**Pre-ship check** (maintainer, at the base, against `oleans-lg4c2`;
`campaign/fills/c1/logs/c1-fill-core-cont2-preship.log`):
- **The overlay** elaborates with exactly your file's two sorry warnings (lines 95 and 750) and
  nothing else. The 20 privates' axioms: within `[propext, Classical.choice, Quot.sound]`, with
  `sorryAx` reaching only `ic_table_call`, `ic_layout_call` and `ic_window_call`, through the cited
  stubs. The snapshot's window copier is its build before #137's proof, so the window copier's
  `sorryAx` shows there; at your base it is proved. No import cycle: none of the four imports'
  closures contains your file.
- **The seal** of the last round's review, re-run on the overlay: 0 errors; its eight controls
  fail, each as intended.
- **The import probe** (`C1CoreCont2ImportProbe.lean.txt`, 220 `#check`s: the review's
  211, and the rewind row, the input rewind's lemmas and `controlAction`, and the counter copy):
  0 errors, 0 warnings. Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line (overlay) | Target |
|---|---|---|
| 1 | `NDCodeSimulator.lean:750` | `Turing.exists_ndInterpreterCore` |

Your regions:
- **(a) the imports**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.Build.InputWindow`,
  `import TCSlib.Complexity.TuringMachine.UniversalStartup`,
  `import TCSlib.Complexity.TuringMachine.Build.SeamLayout` and
  `import TCSlib.Complexity.TuringMachine.Build.Rewind`, after line 8. No other import.
- **(b) one home**, for your `private` declarations: the overlay's lines 99–717, between the
  replay canonizer's `sorry` and your target's docstring, holding the 20 privates first. `private`
  only, and no `section`, `open` or `variable` that leaks past one.
- **(c) the body**, the `sorry` on line **767**.
- **(d) for a partial only, a paragraph headed `**Implementation status.**` at the end of the
  target's docstring**, before its closing ` -/` (line 749). It is public-facing library text:
  what is proved and what is open, in mathematical terms, with no campaign labels (brief, gate,
  finding or escalation names), no dates and no session narrative. The same holds for the
  docstrings of your new declarations; provenance goes in `REPORT.md`.

Frozen: the module header and docstring, the bridge, **the replay canonizer's statement and its
`sorry`**, your target's statement and its docstring before (d), and every other file. The
maintainer updates the module's status text at integration.

### Route (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

The docstring's route, as refined by the last two briefs and by the last round's review. Never
write a second host, seam, embedding, loop, clock or layout machine. The 20 privates are its
pieces; what follows fixes the order of the startup and the three things the review found
missing.
- **The startup's order (the review's gap 1).** The install seam fixes the native input head at
  `1` at both ends (`FinTM.exists_installCallTM` runs from and to `Cfg.ofWords …`, whose
  `inputPos` is `1`), while the window copy needs it at `2|u| + 3`, `u = pairEncode (bits t) α`.
  So run the startup in this order:
  1. **pass 1** (`ic_header_capture` at `first := true`): `bits t` on its capture tape, the
     native head at the suffix;
  2. **an input rewind** (the head to `1`; your leaf through `FinTM.rewind_heads`, which keeps
     every work head);
  3. **pass 2** (`first := false`): `α` on its capture tape, the native head at the suffix again;
  4. **a work-tape rewind of `bits t`'s tape** (below), then **the counter copy**
     (`copyTM_run_ofCfg`, onto a blank tape at head `0`; both heads end where they started): the
     window copy consumes one counter, the loop needs the other;
  5. **the window** (`ic_window_call`): the input head is at the suffix, as its contract wants;
  6. **an input rewind** (the head to `1`);
  7. **a work-tape rewind of `α`'s tape**, then **the install** (`ic_table_call`, its bank
     embedded so that its tape `0` holds `α` at cell `0`, head `0`, and every other bank tape is
     blank, which is exactly `Cfg.ofWords … (stateWord C.k α)`);
  8. **the layout** (`ic_layout_call`, `src` the installed tape);
  9. **a work-tape rewind of the window**, then **the loop's entry**: `Rep` (`ic_replay_rep`),
     Z1's configuration through `vhostCfg`'s fields, and `ic_replay_tail`. The loop's native head
     `p` is arbitrary.

  Rewinds 4, 7 and 9 may move, as long as each precedes its consumer. Join the phases by
  `seamCompTM_run_ofCfg` (each phase's live exit anchor) or `phaseHostTM_run`, as
  `ic_loopHost` does; embed each phase's tapes by R1′/R1 (`embedSilentRetTM`, `embedSilentTM`)
  where its tape count differs. **Do not run the canonizer through `prefixCanonTM`**'s time
  bound: it is a function of `|u|`, which grows with `bits t`.
- **The work-tape rewinds (the review's gap 2), by `Turing.rewindTM_run_ofCfg`** (PR #138; the
  user's ruling). Each consumer needs a head at the start of its word, and three producers leave
  it just past the end:
  - `ic_header_capture` leaves the capture tape's head at `|w|` (`w = bits t` or `α`);
  - `ic_window_call` leaves the window's head at `|x.take t|`;
  - and the counter copy (`copyTM_run_ofCfg`, whose hypothesis reads the source from relative
    `-1` to `|w|`), the installer (head `0`) and Z1 (the buffer head at `inputPos − 1 = 0`) need
    it at the start.

  Instantiate the contract at `n = |w|`: a tape holding `bufferTape w` with its head at `|w|`
  satisfies its hypothesis, and the run ends at head `0` in exactly `|w| + 2` steps, every other
  tape and head and the input head unchanged, the head within `[−1, |w|]` before (the probe's
  first example). `w = []` is allowed (`t = 0`: `bits 0 = []`, and an empty window). **Do not
  write a private rewind:** the row is published for this.
- **The decoded machine (the review's gap 3).** The target speaks of
  `(c.decode α).toFinNDTM.tm : NDTM (…).k Bool (…).State`; the privates speak of
  `(c.decode α).tm : NDTM 2 Bool (Fin (numStates + 1))`. Identify them with
  `simp only [CodeNDTM.toFinNDTM_tm, CodeNDTM.toFinNDTM_k, CodeNDTM.toFinNDTM_State]`, which the
  review checked sealed (`out/26-decode-transport-notes.txt`, S3). **`rw [CodeNDTM.toFinNDTM_tm]`
  alone fails sealed** (it closes only by unfolding `CodeNDTM.toFinNDTM`, S1/S2).
- **The table and the summary**, the window's length, the loop and the verdict, the semantics:
  as in the last brief (`campaign/fills/c1/briefs/c1-fill-core-cont1.md`, Route), now carried by
  `ic_table_call`, `ic_layout_call`, `ic_replay_rep`, `ic_window_call`, `ic_loop_replay`,
  `ic_replay_tail` and `ic_replay_window`. **`Cfg.Halted`** is a reducible `abbrev` for
  `state = none`; reading `¬ Cfg.Halted c` as `c.state ≠ none` is allowed.
- **The ledger** (`ic_time_ledger`, `C = a + b + w + 50(L + 1) + 10`). The startup is
  `a + b·|bits t| + w·(min(t, |x|) + 1)`: the two passes (`16|bits t| + 8|α| + 25` each), the two
  input rewinds (each at most the input head plus `2`; at the second, the head is
  `2|u| + 3 + |x.take t|`, so this rewind costs `O(|bits t| + |α| + min(t, |x|))`), the three
  work-tape rewinds (`|bits t| + 2`, `|α| + 2`, `|x.take t| + 2`), the counter copy
  (`2|bits t| + 2`), the window, the install and the layout (per-code constants), and the
  phases' seams. Put every per-code term in `a`, every `|bits t|` term in `b`, and every window
  term in `w`; then `ic_time_ledger` gives both clauses.
- **Promotion candidates** (list each in `REPORT.md`; notes only): the two-pass header split
  (`ic_header_result`); the first-halt R1′ capture (`ic_capture_return`); your input-rewind leaf
  (a published input-rewind machine would retire several private ones).

## Gate guidance (binding)

- **The C1 host-contracts gate** fixed the statement, including the repaired prefix clause (its
  minor M4). **The design's ledger** (C1's design §3.6) is the intended one; a coarser bound that
  loses the prefix clause is a statement failure, not an option.
- **The seam-layout gate** (round 2, PASS): the layout's time is chosen before the
  configuration, depending on the word and the source head's start only; cite it as stated.
- **The rewind row's gate** (`campaign/gates/55-rewind-row/`): cite the contract as stated.
- **Edge cases that must stay true of your proof:**
  - `t = 0`: `bits 0 = []`, the window is empty, both rewinds of empty words take `2` steps, the
    loop runs no round, and `R` rejects, since an initial configuration is live;
  - `|x| < t`: the window copy stops early; locality still applies, since `x.take t = x`;
  - `|s| > t`: only `s.take t` matters;
  - a code `α` whose decoding is any machine: `c.decode` is total.

## Cited infrastructure (public and proved at the issue commit, except the cited stubs; all in `C1CoreCont2ImportProbe.lean.txt`)

The probe's names: the review's 211 (round 1's 77, the drafts' citations, and everything the 20
privates name or reach), then the rewind row, the input rewind's lemmas and `controlAction`, and
the counter copy. The target, the replay canonizer and the bridge are in your file.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `NDCodeSimulator.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and continue with every item that does not depend on
   it.
5. **No touching other sorries** (the replay canonizer's stays). Cite proved material; never
   re-prove it.
6. **Imports.** Exactly the four in region (a).
7. **One proof per shared argument.** Never write a second loop, step block, Z1, seam, phase
   host, embedding, prefix parser, layout machine or **work-tape rewind**. Never re-walk
   `UniversalStartup`'s or `CodeSimulator`'s privates. A leaf table for the input rewind (two
   `controlAction` states, run by `FinTM.rewind_heads`) is allowed; it is a leaf, as
   `ic_verdictTM` is.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (overlay: 769 lines; 3 public, 20 private).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each
   with a literal "Proof sketch") and the target's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and no definitional closure either (a `rfl`,
      `exact`, `show`, `decide` or `simp` step that closes only because another file's definition
      reduces). Read every definition through its published lemmas. In particular read
      `prefixCanonTM` only through `prefixCanonTM_eq` and `prefixCanon_complete`, `counterValue`
      only through `counterValue_eq`, `rewindTM` only through `rewindTM_run_ofCfg`, and
      `CodeNDTM.toFinNDTM` only through its three field equations.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`, `NDTM.stepWith`, `NDTM.runWith`) are read through their lemmas. The coded
      machine is arbitrary: read it only through the replay lemma and the replay machine's
      fields. Unfold `step` and `Action.apply` only for a leaf defined in your own file.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check:** a seal test (a scratch copy of your module with `attribute [local
      irreducible]` on every other-file definition your proofs mention, which must still
      elaborate, with a control that fails under the seal) and an inspection of every
      `rw`/`simp`/`simpa`/`unfold` argument in your diff. The last round's review lists its seal
      set (`out/11-seal-set.txt`, 38 definitions, and the 4 simp-unfoldable ones in
      `out/11-simp-seal-set.txt`); extend it with every new one you reach.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows (`copyTM_run`, `transferTM_run`, `clearTM_run`,
      `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`); the framed
      `copyTM_run_ofCfg` is not one of them.
    - Cite no private declaration of another file.
    - Keep your new privates under the `ic_` prefix.

### Phases (for a partial; ground rule 9)

1. The startup's header: the two passes and the input rewind between them, joined.
2. The counter: the rewind of `bits t`'s tape and the copy; the window.
3. The table: the input rewind, the rewind of `α`'s tape, the install and the layout.
4. The loop's entry: the window's rewind, `Rep` and Z1's configuration; the assembled machine.
5. The target: the semantics and the ledger, both clauses.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). Run the before
screen **after your first edit** (the overlay's state): it must equal the screen base.
- **The population** is 12 files
  (`campaign/fills/c1/inputs/c1-fill-core-cont2/screen-population.txt`): the last round's 11
  (your file; `CodeSimulator`, the main hazard; `Build/StepBlockLoop`; `UniversalStartup`;
  `UniversalK`; `ChoiceReplay`; `Build/InputWindow`; `Build/SeamLayout`; `Build/Embed`;
  `Build/Loop`; `Build/CertShell`) and `Build/Rewind`.
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/c1/logs/c1-fill-core-cont2-screen-base.txt`, measured on the
  overlay: **460 declarations, 118 pairs, 43,576 characters** (MEASURED).

```sh
P=campaign/fills/c1/inputs/c1-fill-core-cont2
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:** the chapter-1 startup (`universalCaptureTM` and its run); U2's startup
  (`UniversalK`); `CodeSimulator`'s H1 assembly; the inline first-halt captures
  (`Build/CertShell`'s `certCore_run`); and the private input-rewind leaves elsewhere in the
  library (for example `SpaceComplexity/Inclusions`' `b2b_rewindTM`, outside the population):
  follow their pattern, never transcribe it. A pair at 90% or more is a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only** (addendum v2.4, items 2–4,
  fetched once for the queue);
  **never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check.
- **Your Mathlib roots** are the Mathlib modules that the order list's modules import directly:
  41 of them at the overlay (the queue's union, which the session fetched, is 41).
- **Re-bootstrap** (addendum Part 3, item 3.2) from
  `campaign/fills/c1/orders/c1-fill-core-cont2.txt` (118 modules:
  the upstream closure of your owned file, with the four imports, and of every module downstream
  of it, without the root `TCSlib`), after your first edit.

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < campaign/fills/c1/orders/c1-fill-core-cont2.txt )
  ```

  **The base sorry-warning set has 38 entries in 17 modules**
  (`campaign/fills/c1/logs/c1-fill-core-cont2-base-sorries.txt`). Yours is `NDCodeSimulator`'s
  `exists_ndInterpreterCore`; its other entry, the replay canonizer, stays. Record the base list
  by name first, and report any difference.
- **Final checks:**
  1. `NDCodeSimulator`: zero errors, exactly the replay canonizer's sorry warning (for a partial,
     plus the open declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours.
  3. Re-run `C1CoreCont2ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the target and every new private: within
  `[propext, Classical.choice, Quot.sound]` plus the `sorryAx` of the cited stubs (the replay
  canonizer, the seam layout), and nothing else.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL
  (base: 0 FAIL, 63 WARN over 82 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The session's shared preflight and cache numbers (quoted from its logs), and this item's
      bootstrap.
- [ ] The target proved (or the phase reached), modulo exactly the cited stubs; the base hash and
      the ancestor check; the checkpoint zips written.
- [ ] The four imports and the 20 privates as the first edit (the overlay, byte for byte), and
      nothing else outside regions (b)–(d); any private restated, with the reason.
- [ ] Every new declaration with its role; the status paragraph, if a partial.
- [ ] The tapes chosen for each phase, the startup's order as run, and each rewind's `n`.
- [ ] The per-code constant `C`, and the ledger of both clauses.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file, the probe re-run, the seal test with
      its control, and the inspection. Rule 11: a grep of your diff for the six R3 rows and for
      other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **`Cfg.inputPos` is shifted by one.** In `pairEncode u x` the suffix `x` starts at index
  `2|u| + 2`, native position `2|u| + 3`, which is where `prefixCanon_complete` leaves the head.
- **`pairEncode` doubles its first component:** `u` takes `2|u|` cells, then the separator
  `[false, true]`.
- **The replay machine puts the choice tape last**, and the step block mirrors the source's tapes
  first: the stream is the replay machine's last tape.
- **The seam layout's three tapes must be distinct**, and it clears `src`: install the
  serialization on a scratch tape, not on a tape you still need.
- **The simps field equations are pointwise.** `Cfg.mapState_workTapes`/`_workTapePos`,
  `NDTM.withChoiceTape_*` and `Cfg.init_*` state `… .workTapes i a = …`, so they never fire on
  the unapplied field goals of `Cfg.ext`: `funext` first (`apply Cfg.ext <;> (try funext i) <;>
  (try funext p) <;> simp only […]`). Otherwise `simp`/`simpa` may close by unfolding, which the
  seal rejects (the review's R6, R8).
- **`prefix` is a reserved keyword** (the `prefix` notation command); do not name a hypothesis
  `prefix` (R3).
- **Aim `counter_cfg_eq` with its arguments** (`counter_cfg_eq _ e`): unaimed it instantiates on
  the first `counterLoopCfg`, the loop's start inside `runFrom` (R4).
- **Give `gcongr` a template** (`gcongr ?_ + ?_ * _ + …`): unguided it also splits the constant
  `C` itself (R5).
- **Phase-indexed configurations do not match by `rw`.** A configuration typed at
  `Cfg 7 _ (ic_loopPh false)` is not syntactically one at `Cfg 7 _ (CounterLoopState … × Bool)`,
  and `rw` will not unfold `ic_loopPh`: close by `exact` (R7).
- **`simp` does not see through a local `let`**; `rw` matches up to it (R2).
- **`rw [length_pairEncode] at h` may hit the input position's type** `Fin (… .length + 2)`
  first: name the pair (`length_pairEncode (Nat.bits t) α`) (R1).
- **`counterLoopOrbit` is an `abbrev`:** `rw` may not fire on it, while `exact` and `simp only`
  do.
- **`StepBlock.exit k live` is a sigma type:** rewrite it with `exit_true` and `exit_false`.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch"
  before every `sorry` (partial only).
