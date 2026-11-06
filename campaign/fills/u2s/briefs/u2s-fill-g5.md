# Ch3–4 fill campaign — G5, Hennie–Stearns on two work tapes (`two_work_tapes_run`)

> **Issued** (maintainer, 2026-11-06), after G5's API merged: #197 (the consumer side, gate 97),
> #202 (`Turing.Segment.iterate_seq`, gate 98) and #207 (`zoneRebalanceData_eq`,
> `zoneExtendData_eq`, gate 99). Its pre-ship ran on the merged tree
> (`campaign/fills/u2s/logs/u2s-fill-g5-preship.log`), and a review of the draft (2026-11-06;
> `campaign/fills/u2s/drafts/u2s-fill-g5/review/REVIEW.md`) is folded in. The questions the
> drafting raised are ruled (the user, 2026-11-05; G5's plan §8; the last section); the route
> marks where each enters, `[Q1]`–`[Q3]`.
> - **Decision G5-F1 (the user, 2026-11-05): API first.** #197 publishes the consumer side
>   (`Build/ZoneStep`, `ZoneRebalance`'s equations, `Contract.zero`); this fill writes the
>   controller, its invariant and the count bound.
> - **The agent: Claude** (the user, 2026-11-05, over the soft rule's Codex-first).
>
> **A single fill** (addendum v2.6, Parts 1 and 2; of Part 3 only its one-Lean rule and its
> no-stop rule, items 5 and 7). Deliver a checkpoint zip after each checkpoint: the session may
> end at any time.

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out branch
  **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor 335d31d408f1b4b4164f5b1b3a37d246a42b25cc HEAD`
  succeeds. If it fails, **stop**.
  That commit contains:
  - **your target as a gated statement** (PR #189, gate 92, `campaign/gates/92-g5-statements/`):
    `Turing.FinTM.two_work_tapes_run` in `TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean`,
    `sorry`; `Turing.FinTM.two_work_tapes_binary` beside it, proved from it; its consumer
    `Turing.universal_TlogT` (`TuringMachine/UniversalTlogT.lean`), proved from it;
  - **the alphabet reduction, run by run** (#189): `Turing.FinTM.alphabet_reduction_run`
    (`Robustness/AlphabetReduction`), with its image converse (the plan's decision D2);
  - **the zone layer, proved** (§13d G2–G4): `Build/Zone` (the pure contents, cascades, scan,
    extension and represented tape), `Build/ZoneTape` (the carrier `Turing.zonedTape` over
    `Turing.ZoneSym k`), `Build/ZoneRebalance` (the rows `exists_zoneRebalanceTM`,
    `exists_zoneExtendTM` and their endpoint lemmas);
  - **G5's consumer API** (#197, merged as `33ceeed1`; gate 97, `campaign/gates/97-zone-step-api/`):
    - `Build/ZoneStep` (new): `Turing.exists_zoneTrackStepTM`, `Turing.zoneTrackStepData` with
      `_of_lt` and `_of_not_lt`, `Turing.sum_two_pow_le_of_count`, `Turing.sum_cost_le_of_count`;
    - `Build/ZoneRebalance`: `zoneRowPre_iff`, `zoneRowPre_congr`, `zoneRowPre_mapState_iff`,
      `zoneRebalanceIndex_eq`, `zoneRebalanceIndex_le`, and the `simps` fields of
      `zoneRebalanceData`, `zoneExtendData`, `zoneRebalancePost` and `zoneExtendPost`;
    - `Build/Contract/Basic`: `Turing.Contract.zero` and its five equations;
  - **the contract layer and its hosts**: `Build/Contract/Basic` (contracts, segments, rounds,
    `Turing.Lockstep`), `Build/Contract/Seam` (`Contract.seq`, `Contract.inPhase`,
    `Contract.branch`, `Cfg.bindState`), the phase host `Turing.phaseHostTM` (`Build/Seam`), R1
    (`Turing.embedEmitTM`, `Build/Embed`);
  - the fill-environment addendum `campaign/standards/fill-environment-addendum.md` (**v2.6**) and
    the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/u2s/inputs/u2s-fill-g5/`):
    - the overlay (your file with region (a)'s import): `TwoTapesOverlay.lean.txt`;
    - the import probe: `G5ImportProbe.lean.txt` (217 `#check`s, every name this brief cites);
    - the route probe with its seal and controls: `G5Route.lean.txt`, `G5RouteSealed.lean.txt`,
      `G5RouteCtl_unsealed.lean.txt`, `G5RouteCtl_sealed.lean.txt` (re-run on the merged tree;
      its notes in `G5Route-README.md`);
    - the semantic-duplication probe: `G5RouteExact.lean.txt`;
    - the screen population `screen-population.txt` (22 files);
    - the order list `campaign/fills/u2s/orders/u2s-fill-g5.txt`, the base sorry set, the screen
      base and the pre-ship log (`campaign/fills/u2s/logs/u2s-fill-g5-*`).
- The design records: `campaign/items/u2/G5-statements-plan.md` (§1–§3, §6–§8);
  `campaign/items/u2/U2-design.md` §1 and §4; `machine-library-design.md` §13d (G3–G5) and §14.
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule. Fetch
  the cache for your roots only (42 Mathlib roots); never the unfiltered
  `lake exe cache get`. If Lean never runs, do not draft proofs blind: deliver the environment
  report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/u2s-g5 335d31d408f1b4b4164f5b1b3a37d246a42b25cc
  git rev-parse HEAD        # must print 335d31d408f1b4b4164f5b1b3a37d246a42b25cc
  git rev-parse HEAD:TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean
  # must print cc35767342620a3be6331c57239e5eafa5ea4c45
  # (git rev-parse at the ancestor)
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip** (`workflow.md` §4): `fill-u2s-g5.zip`, pushed to the branch
  `exchange/pass-shelat-ch5-8` at `arora-barak-ch3-4/inbox/` (you have push access;
  `git pull --rebase` first, add only your zips, never force-push, no PR), containing:
  - `REPORT.md`, the full modified source, a `git format-patch` series against your base and a
    git bundle whose only prerequisite is your base;
  - the environment logs (`evidence/logs/`), the bootstrap and final sweep logs with each
    module's time and maximum memory, and the axiom log;
  - the seal test's source, its controls and both outputs;
  - both screen outputs and `SHA256SUMS`.

  **Checkpoint zips** `fill-u2s-g5-cp<N>.zip`, one per checkpoint below, with the same contents
  as of that checkpoint's commit (the final sweep may be your module's check only).

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign after #191, #202 and #207 merged** (`d43a1374`; the
  ancestor adds records only). Lines in this brief are your base's (after region (a)'s import
  every later line moves down by one: the home at 50, the target's docstring end at 64, its `sorry`
  at 71). `TwoTapes.lean` is #189's landing, 86 lines, 2 public and 0 private declarations,
  unchanged since (blob `cc35767342620a3be6331c57239e5eafa5ea4c45`):
  - the imports, lines 6–8 (`Mathlib.Data.Nat.Log`, `Robustness.AlphabetReduction`,
    `Build.ZoneRebalance`); the module docstring, lines 14–46; `namespace Turing.FinTM`, line 48;
  - `two_work_tapes_run`: docstring 50–63, statement 64–69, its `sorry` on line 70;
  - `two_work_tapes_binary`: docstring 72–77, statement 78–81, proof 82–84; `end`, line 86.
- **In flight, merging after your base and invisible to it:** #208, the deepening fill's landing
  (`SavitchARM/Deepen`, `Savitch`; outside your order list). It is replayed on the merged tree
  before it merges. Cite nothing it adds.
- **Parallel batches this round:** none in your file. The deepening fill (`SavitchARM/Deepen`,
  `Savitch`) shares no file with you.
- **Your consumers:** `two_work_tapes_binary` (already proved from your statement),
  `Turing.universal_TlogT` (`UniversalTlogT`, through `universalK 2`), and later the `f log f`
  time hierarchy (U2 design §6 item 7).

## What this is

**Two work tapes suffice, run by run** ([HS66]; [AB09, §1.7], the proof of Theorem 1.9): every
binary machine `M` has a binary two-work-tape `M'` that reproduces each halting run of `t` steps
within `c · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of `M'` is one of `M`'s.

- **The construction** (`machine-library-design.md` §13d, G5; decisions 13d.1–13d.5): a machine
  `HS` over `Turing.ZoneSym M.k` with two work tapes. Tape `0` carries `M`'s `k` work tapes as
  tracks of one zoned tape (`Turing.zonedTape`), with every simulated head at the home cell;
  tape `1` is the rows' blank scratch tape. One simulated step reads the home tuple and the input
  symbol, applies `M`'s transition in finite control, writes the home tuple, moves the input
  head, emits, and then runs one track step (`Turing.exists_zoneTrackStepTM`) per moving head.
  `Turing.FinTM.alphabet_reduction_run` then makes `HS` binary, keeping two work tapes.
- **The amortization** is published (`Turing.sum_cost_le_of_count`): what is yours is the count
  hypothesis (the fullness invariant) and the level bound `L ≤ log₂ T + O(1)`.

**Where it stands.**
- `two_work_tapes_run` is `sorry`; everything below it is proved: the rows (`ZoneRebalance`, no
  `sorry`), the track step and the arithmetic (#197, on the standard three axioms), the alphabet
  reduction.
- `universal_TlogT` reaches `sorryAx` only through `two_work_tapes_run` (gate 92's axiom prints;
  `universalK` is admission-free).

**Proved modulo, exactly:** none. **A complete delivery has no `sorryAx` in
`two_work_tapes_run`**, and then `two_work_tapes_binary` and `universal_TlogT` have none either.

**Read first:**
- the target's docstring, whose proof sketch binds where this brief does not refine it;
- `Build/ZoneStep` whole (326 lines): its module docstring and the three theorems;
- `ZoneRebalance`'s module docstring (*How the assembly consumes the rows*) and its public
  statements from `exists_zoneRebalanceTM` on (do not read its 15k lines of private proofs);
- `Build/Zone`'s and `Build/ZoneTape`'s module docstrings (`## Main results`);
- `Contract.inPhase` and `phaseHostTM_run` (`Build/Contract/Seam`, `Build/Seam`), the segment
  layer (`Turing.Segment`, `Build/Contract/Basic`);
- the route probe (`G5Route.lean.txt`): `tt_zero_tapes` (step 1), `tt_frame` (step 0) and
  `tt_route` (the case split), proved; copy them into your home as they are.

## Owned regions and targets (modify these and nothing else)

| # | File:line (base) | Target |
|---|---|---|
| 1 | `Robustness/TwoTapes.lean:64` | `Turing.FinTM.two_work_tapes_run` (frozen statement) |

Your regions, all in `TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean`:
- **(a) the imports**, as your first edit: add exactly
  `import TCSlib.Complexity.TuringMachine.Build.ZoneStep` after line 8 (the overlay). No other
  import: `Build/Embed` (R1) is already in your closure, and the import probe resolves every cited
  name through these four.
- **(b) your home**, the blank line 49, between `namespace Turing.FinTM` (48) and the target's
  docstring (50): your `private` declarations, under the prefix `tt_` (unused at the drafting base
  on the campaign and on all 201 PR heads). Section comments (`/-! ### … -/`) are allowed; no
  `section`, `open` or `variable` that leaks past one declaration (`open … in` is fine).
- **(c) the body**, the `sorry` on line 70.
- **(d) for an open target only**, a paragraph headed `**Implementation status.**` at the end of
  the target's docstring, before its closing ` -/` (line 63): what is proved and what is open, in
  mathematical terms.

**No new file and no facade edit.** The plan's homes (§3, decision D1) put the reduction in
`TwoTapes`; file size is not a driver (`campaign/maintainer/WORKFLOW.md` §2): report the size.
**Frozen:** the module docstring (14–46; the maintainer updates it at integration), both
statements and docstrings (except (d)), `two_work_tapes_binary`'s proof (82–84), and every other
file.

**Public-facing text** (WORKFLOW §2): every new declaration has a docstring, citing only
mathematical sources (`[AB09, §1.7]`, `[HS66]`) and library declarations; no campaign labels
(G5, gate, finding or round names, ledger family labels), no `campaign/` or `audits/` paths, no
dates. Every proof over 20 lines carries a literal `**Proof sketch.**`.

### The pinned statement (binding; frozen verbatim at the base)

```lean
theorem two_work_tapes_run (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  sorry
```

`two_work_tapes_binary` (lines 78–84) is already proved from it, in two lines: do not touch it.
**No new public declaration.**

## Hosts (binding; `policy.md` §1, *Hosts come first*)

- **Dispatch over a simulated step's phases, and the machine of the loop:** the phase host
  `Turing.phaseHostTM` (`Build/Seam`) and its contract form `Turing.Contract.inPhase`
  (`Build/Contract/Seam`). Registered: `machine-library-design.md` §14 item 0 (sequencing, the
  phase host, R1, as structure-to-structure theorems), landed with MIG-0a/0b (§16a); the phase
  host itself is §12.8's.
- **Composition inside a phase or a round:** `Contract.seq`, `Contract.branch`
  (`Build/Contract/Seam`), `Contract.trans`, `Contract.zero` and the segment layer
  (`Contract.segment`, `Segment.trans`, `Segment.mono`, `Contract.ofSegment`;
  `Build/Contract/Basic`). Registered: §14 item 0; §16a.
- **One track's step:** `Turing.exists_zoneTrackStepTM` (`Build/ZoneStep`; gate 97), a composite
  of §13d G4's rows, not a host.
- **Zero work tapes** (`[Q1]`, ruled *separate*): R1, `Turing.embedEmitTM` (`Build/Embed`).
  Registered: §12 R1; §14 item 0.
- **The binary finish:** `Turing.FinTM.alphabet_reduction_run` (`Robustness/AlphabetReduction`;
  gate 92), a conversion theorem, not a host.
- **The iteration of simulated steps:** `Turing.Segment.iterate_seq` (`Build/Contract/Basic`;
  #202, gate 98), a lemma, not a host (`[Q2]`, ruled API first).

**Rules for the route's machines:**
- **The one leaf you may write: the transition step**, one transition of `HS` that reads the
  home tuple and the input symbol, writes the home tuple, moves the input head, emits and changes
  state. Its docstring says that no public row applies a finite-state transition to the home cell
  of the zoned tape and the input head in one step. Any further leaf, loop, seam or host is an
  escalation (ground rule 4).
- **Never write a second track step** (a branch or sequence of `exists_zoneRebalanceTM` and
  `exists_zoneExtendTM`), a second phase host, seam, embedding or input device.
- **`[Q2]`, the iteration (ruled: API first).** `Round.iterate_seq` and `RoundContract` need one
  anchor, and `Turing.Lockstep` needs an encoding that is a function of the source configuration.
  `HS` keeps `M`'s state in finite control (both tapes are fixed by `zoneRowPre`), and its zone
  contents depend on the run's history, so neither fits. #202 publishes
  `Turing.Segment.iterate_seq`: a sequence of segments with arbitrary starts composes into one
  segment over the summed time (`Round.iterate_seq` is its corollary). Cite it (route step 5);
  never write your own induction over rounds.
- **`[Q3]`, the controller.** Decision G5-F1 assigns the controller to this fill, and it stands.
  `policy.md` §1 counts "an interpreter or simulation step block" as a host, so note the round over
  the zoned carrier as a promotion candidate in `REPORT.md`.

## The published API you cite (binding)

All public and proved at `335d31d408f1b4b4164f5b1b3a37d246a42b25cc`; the import probe checks every
name (217). Cite these; never re-prove one, and never restate one as a private.

- **The track step and the amortization** (`Build/ZoneStep`): `Turing.exists_zoneTrackStepTM`
  (per `k`, one constant `A`; per direction and track a machine with `Fintype` and `DecidableEq`
  states, an entry and live exits `X`, `none ∉ X`; its contract has precondition
  `Turing.zoneRowPre`, time at most `A · (2^{zoneRebalanceIndex dir t D} + 1)`, and an endpoint
  satisfying `zoneRowPre` at `Turing.zoneTrackStepData dir t D`, with the scratch head, the input
  head and the output unchanged); `Turing.zoneTrackStepData_of_lt`, `_of_not_lt`;
  `Turing.sum_cost_le_of_count` (and, inside it, `Turing.sum_two_pow_le_of_count`).
- **The rows' data and precondition** (`Build/ZoneRebalance`): `Turing.ZoneData`,
  `Turing.zoneRowPre_iff`, `Turing.zoneRowPre_congr`, `Turing.zoneRowPre_mapState_iff`,
  `Turing.zoneRebalanceIndex_eq`, `Turing.zoneRebalanceIndex_le`, `Turing.zoneRebalanceData_eq`,
  `Turing.zoneExtendData_eq` (#207: the data maps as whole values),
  `Turing.zoneRebalanceData_of_short`, `Turing.zoneRebalanceIndex_extend_of_short`. **Read the maps
  through `zoneRebalanceData_eq` and `zoneExtendData_eq`, never through the pointwise fields
  `zoneRebalanceData_snd` and `zoneExtendData_snd`**: those sit at the map's own level, so under the
  seal their rewrites leave goals that differ in a hidden level (pitfall 9).
- **The carrier** (`Build/ZoneTape`): `Turing.ZoneSym`, `Turing.ZoneCell`, `Turing.zonedTape`,
  `Turing.zonedTape_zero`, `Turing.zonedTape_homeWrite`, `Turing.zonedTape_blank_outside`,
  `Turing.zoneStart_eq`, `Turing.zoneCellOfCell` with `_inr`, `_inl`, `_none`.
- **The pure layer** (`Build/Zone`):
  - the contents: `Turing.ZoneContents`, `ZoneContents.empty` (`_home`, `_left`, `_right`),
    `ZoneContents.words_true`, `_false`, `ZoneContents.extend_words_castSucc`, `_last`,
    `Turing.zoneCapacity_eq`, `Turing.zoneHomeWrite` (`_home`, `_left`, `_right`);
  - the scan: `Turing.zoneShiftIndex_le`, `_empty`, `_nonempty`, `_eq`, `_eq_length_iff`,
    `_extend`, `_extend_of_lt`;
  - the rebalance: `Turing.zoneRebalance_of_lt`, `_of_le`, `_frame`, `Turing.zoneCascade_true`,
    `_false`, `Turing.zoneCascadeRight_lengths`, `Turing.zoneCascadeLeft_lengths`;
  - the represented tape: `Turing.zoneTrackTape_zero`, `_empty`, `_homeWrite`, `_extend`,
    `_rebalance_right`, `_rebalance_left`.
- **Contracts** (`Build/Contract/Basic`, `Build/Contract/Seam`): the fields of `Turing.Contract`;
  `Contract.live`, `Contract.segment`, `Contract.ofSegment` (`_pre` … `_hi`),
  `Contract.time_envelope`, `Contract.zero` (`_pre`, `_time`, `_post`, `_lo`, `_hi`),
  `Contract.trans` (its `simps` fields); `Turing.Segment`, `segment_iff`, `Segment.one`,
  `Segment.trans`, `Segment.iterate_seq` (#202), `Segment.mono`, `Segment.cons`, `Segment.live`;
  `Contract.inPhase`, `seq` and
  `branch` with their `simps` fields (`inPhase_pre`, `inPhase_time`, `inPhase_post`, …),
  `Contract.seq_positive`, `Contract.branch_positive`, `Contract.inPhase_positive`;
  `Turing.Cfg.bindState` and its fields (`Cfg.bindState_state`, `_inputPos`, `_workTapes`,
  `_workTapePos`, `_output`).
- **The phase host** (`Build/Seam`): `Turing.phaseHostTM`, `phaseHostTM_q₀`,
  `phaseHostTM_tr_of_red_none`, `phaseHostTM_tr_of_red_some`, `phaseHostTM_run`,
  `phaseHostTM_run_le`. With them (`CfgFacts`): `Cfg.mapState_eq_of_fields`,
  `Cfg.mapState_const_eq_mapState_sigma`, `Cfg.mapState_sigma_state_ne`.
- **The machine model**: `MultiTapeTM.step_of_some`, `step_of_halt`, `runFrom_zero`,
  `runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_of_halt`, `MultiTapeTM.initCfg_eq`
  (`Deterministic`); `Action.apply_state`, `_inputPos`, `_workTapePos`, `_output`,
  `Cfg.workTapeSymbols_eq`, `Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end`,
  `Turing.inputSymbolInner`, `Cfg.init_state`, `_inputPos`, `_workTapes`, `_workTapePos`,
  `_output` (`Configuration`); `Action.apply_workTapes` (`Simulation`); `Cfg.mapState_state`,
  `_inputPos`, `_workTapes`, `_workTapePos`, `_output` (`StateRenaming`);
  `MultiTapeTM.exists_first_halt`, `MultiTapeTM.runFrom_state_ne_none_of_le`,
  `MultiTapeTM.initCfg_with_q₀`, `MultiTapeTM.runFrom_with_q₀`, `FinTM.computesInTime_iff`,
  `FinTM.ComputesInTime.mono`, `FinTM.ComputesInTime.output_unique`,
  `FinTM.not_computesInTime_zero` (`Finite`).
- **R1, for `[Q1]`'s separate option** (`Build/Embed`): `Turing.embedEmitTM`, `embedEmitTM_tr`,
  `embedEmitTM_runFrom`, `embedEmitTM_frame`, `embedEmitCfg_eq`, `embedEmitCfg_state`,
  `embedEmitCfg_output`.
- **The finish** (`Robustness/AlphabetReduction`): `Turing.FinTM.alphabet_reduction_run`.
- **Mathlib and core:** `Function.Embedding.inl` (`_apply`), `Nat.log`, `Nat.pow_log_le_self`,
  `Nat.lt_pow_succ_log_self`, `Nat.log_mono_right`, `Nat.log2_eq_log_two`, `List.length_map`,
  `List.getElem_map`, `Fin.castLEEmb`.

### What you never re-prove or unfold (rule 10; ground rule 10 below)

- **The zone rows**: never re-compose `exists_zoneRebalanceTM` or `exists_zoneExtendTM`; their
  contracts reach you only through `exists_zoneTrackStepTM`'s five clauses.
- **`Turing.zoneRowPre`** only through `zoneRowPre_iff`, `zoneRowPre_congr` (across a
  `Cfg.bindState` redirect or any change of state type) and `zoneRowPre_mapState_iff` (across a
  `Cfg.mapState` start). Never `unfold zoneRowPre` or `simp [zoneRowPre]`.
- **The contracts only through their equations**: `Contract.inPhase`, `seq`, `branch`, `trans`,
  `zero` and `ofSegment` through their `simps` fields (`inPhase_time`, `zero_post`, …); a
  `Contract`'s behaviour through its fields `run`, `exit_mem`, `cut`, `env`.
- **The data maps and endpoints** (`zoneRebalanceData`, `zoneExtendData`, `zoneTrackStepData`,
  `zoneRebalanceIndex`) only through their equations (`zoneRebalanceData_eq`, `zoneExtendData_eq`,
  `zoneTrackStepData_of_lt`/`_of_not_lt`, `zoneRebalanceIndex_eq`); `ZoneContents.*`,
  `zoneHomeWrite`, `zonedTape`, `zoneShiftIndex`, `zoneRebalance`, `zoneCascade`, `zoneTrackTape`
  and `zoneCapacity` only through the lemmas listed above.
- **The machine model's primitives**: `MultiTapeTM.step` through `step_of_some`/`step_of_halt`,
  `Action.apply` through its fields, `MultiTapeTM.initCfg` through `initCfg_eq` and the
  `Cfg.init_*` fields, `Cfg.mapState` and `Cfg.bindState` through their fields,
  `FinTM.ComputesInTime` through `computesInTime_iff`, `phaseHostTM` through its five lemmas.

## The route (binding where it names a row; the rest is the recommended shape)

### 0. The frame (binding)

1. **The cases** (`[Q1]`, ruled *separate*): `M.k = 0` by step 1; `M.k ≥ 1` by `HS`.
2. **The finish.** For the zone machine `HS : FinTM (ZoneSym M.k)` with `HS.k = 2`, apply
   `alphabet_reduction_run (Function.Embedding.inl : Bool ↪ ZoneSym M.k) HS`, which gives
   `M'` with `M'.k = 2` and a constant `c₂`. It reduces the target to **two properties of `HS`**
   (state them as `tt_` lemmas, generic in the track-step family of step 2 below):
   - **forward** (then `c := c₂ · c₁`):

     ```lean
     M.ComputesInTime x o t →
       HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
         (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1)))
     ```
   - **converse** (with `alphabet_reduction_run`'s image converse, `∀ v, o' = v.map e → v = w`,
     it gives `M.ComputesInTime x w t`; gate 92's D2 analysis: `HS` emits only images of bits, so
     the image form suffices):

     ```lean
     HS.ComputesInTime (x.map Sum.inl) o' t' → ∃ t v, M.ComputesInTime x v t ∧ o' = v.map Sum.inl
     ```
3. `x.map ⇑Function.Embedding.inl` is `x.map Sum.inl` by `Function.Embedding.inl_apply` (a Mathlib
   definition: `rfl`/`show` allowed, never `simp [Function.Embedding.inl]`).

### 1. Zero work tapes (`[Q1]`, ruled *separate*)

- **Separate** (plan §2, gate 22's minor 1, and the frozen sketch's last sentence: "With no
  work tapes, `M` is run directly beside two idle tapes"): `M'` is R1 of `M.tm` on two tapes,
  `embedEmitTM σ M.tm` with `σ : Fin M.k ↪ Fin 2` (for instance `Fin.castLEEmb`), blank frame,
  heads `0`, prefix `[]`, as a `FinTM Bool` with `c = 1`. No alphabet reduction. Read it through
  `embedEmitTM_runFrom` and `embedEmitCfg_eq` (the initial configuration, with `Cfg.init_*` and
  `MultiTapeTM.initCfg_eq`), both directions. `embedEmitTM` has no published `q₀` equation: build
  `{ embedEmitTM σ M.tm with q₀ := M.tm.q₀ }` and read it through `MultiTapeTM.initCfg_with_q₀`
  and `MultiTapeTM.runFrom_with_q₀` (needed: with `embedEmitTM` sealed, no lemma gives its `q₀`
  or `initCfg`). The bound: `t ≤ (t + 1) · (Nat.log 2 (t + 1) + 1)`. The route probe's
  `tt_zero_tapes` is this step, proved.
  **Never copy `Robustness/SingleTape`'s private zero-tape embedding** (`unusedTapeTM`,
  `unusedTape_step`, `unusedTape_computes`): R1 is its public form.

### 2. The machine `HS` (recommended shape; the hosts are binding)

- **Tapes** (decision 13d.5, §13d G3): `HS : FinTM (ZoneSym k)` with `k := M.k`, `HS.k = 2`;
  tape `0` the zoned tape, tape `1` the scratch tape, which is blank at every round boundary.
  The input is `x.map Sum.inl`, read directly: no copy of the input, no input device.
- **The track-step family.** `obtain`/`choose` from `exists_zoneTrackStepTM k` the constant `A`
  and, per `(dir, t)`, the state type, its instances, the machine, the entry, the exits `X`,
  `none ∉ X`, and per input the contract with its five clauses. State every controller lemma
  **generically over such a family** (a `tt_` structure or explicit hypotheses), and instantiate
  it once in the body.
- **The leaf** (the one authorized leaf; your own definition, which you may unfold):
  - from a leaf state at `q`, one transition: read the home cell, decoded per track as
    `(zoneCellOfCell (w 0) t).join` (a blank home reads as all virtual blanks, so the first
    round needs no initialization), and the input symbol, decoded through `Sum.inl`; apply
    `M.tm.tr q`; write the new home tuple `some (.inr fun t => some (v' t))` with
    `v' t := (a.workTapes t).1.getD (v t)`; move the input head by `a.inputTape`; emit
    `a.output.map Sum.inl`; keep both work heads;
  - go to a leaf exit carrying the successor state and the move vector, or halt (`none`) when
    `a.state = none`: `HS` halts exactly when `M` does, in the same transition.
- **The phases** (the phase host, binding): the leaf, and one phase per pending step and track,
  indexed by `(q', m, t)` (the successor state, the move vector `m : Fin k → SignType`, the
  track) with the track machine of direction `m t` (`true` for a right move). **Recommended:
  every track has a phase in every round, a stay being a zero-time phase (`Contract.zero`)**, so
  that each redirect targets another phase, as `Contract.inPhase` requires (`q.1 ≠ p`). A stay
  phase's machine is that track's track machine of either direction, entered at its `entry`, with
  `Contract.zero` at that entry; it is not a new leaf. The
  redirects are classical (`if some s ∈ X then … else none`, gate 97's note 7): leaf exit →
  track `0`; track `t` → track `t + 1`; track `k - 1` → the leaf at `q'`.
- **The state type** `Σ i, Ph i` is finite: the index type is finite (`M.State`, `SignType` and
  `Fin k` are), and each phase's states are `Fintype` (`exists_zoneTrackStepTM` exports it). The
  initial state is the leaf at `M.tm.q₀` (`phaseHostTM_q₀`).

### 3. One round (binding where it names a lemma)

A round runs from the leaf at `q` to the leaf at `q'` (or halts at the leaf). **Binding:** state
it as a **`Turing.Segment`** of `HS` against `{none}` (live before its end; a segment's cut
includes time `0`, so the forbidden set cannot contain the round's own start state), from the
round's start to its end, so that rounds compose by `Segment.trans`:
- each phase through `Contract.inPhase` (its run, exit and time, `inPhase_time = C.time + 1`), or
  through `phaseHostTM_run`; a track phase's start through `zoneRowPre_mapState_iff` and its
  redirected end through `zoneRowPre_congr` (`Cfg.bindState`'s fields);
- inside a phase the host is the tagged phase run (`phaseHostTM_run_le`), live by the phase
  contract's `Contract.live`; its redirect guard (no redirect before the phase's end) follows from
  the phase contract's cut and `red` being `none` off `X`; a tagged configuration is at no state
  of another phase (`Cfg.mapState_sigma_state_ne`);
- **the halting round**: the leaf's last transition halts, so `Contract.inPhase` (live exits only,
  `none ∉ X`) does not apply; read it through `phaseHostTM_run_le` and `step_of_some`.
- **Positivity:** every round takes at least the leaf's step and its dispatch, read from
  `inPhase_time` (`C.time + 1`) or the leaf's own step. Do not use `Contract.inPhase_positive`,
  `seq_positive` or `branch_positive`: they return `Contract.Positive`, a definition with no
  equation, which the seal rejects. Read `Turing.Segment` through `segment_iff`, never by
  projection. Do not try to prove `some entry ∉ X` for a track step: it is not exported.
- **The round's time**: `1` for the leaf, `1` per dispatch, and per track at most
  `A · (2^{idx} + 1)` with `idx` the scanned index at that track's start (`0`, and time `0`, for a
  stay). So the round costs at most `B + A · Σ_t (2^{idx t s} + 1) + k` with a constant `B` (the
  leaf and its dispatch), which is `sum_cost_le_of_count`'s step hypothesis.

### 4. The simulation invariant (recommended formula; its lemmas are binding)

At the start of round `s`, with `c := M.tm.runFrom (M.tm.initCfg x) s` and data `D`:
1. **the carrier:** `zoneRowPre D d` (tape `0` is `zonedTape D.2` with its head at `0`, tape `1`
   blank), by `zoneRowPre_iff`, for `s ≥ 1`; at `s = 0` it holds off cell `0` only (the first
   round, below); head `1` stays at `0` (the leaf keeps it, and every track step
   keeps `workTapePos 1`);
2. **the represented tapes:**
   `∀ t p, zoneTrackTape (D.2 t) p = c.workTapes t (c.workTapePos t + p)`;
3. **input and output:** `d.inputPos.val = c.inputPos.val` (both inputs have length `|x|`,
   `List.length_map`; the reads agree through `inputSymbolInner` and `List.getElem_map`, and the
   ends through `Cfg.inputSymbol_of_zero`/`_of_end`), and `d.output = c.output.map Sum.inl`;
4. **the state:** `d` is at the leaf at `q` exactly when `c.state = some q`;
5. **fullness** (the classical invariant, gate 97's note 8): for every track and level `i < D.1`,
   `|L_i| + |R_i| = zoneCapacity i`, and each side holds `0`, `2^i` or `zoneCapacity i` cells.

**Preservation by a round**, track by track:
- the leaf's write: `zonedTape_homeWrite`, `zoneTrackTape_homeWrite`;
- a right move (`dir = true`) or left move (`dir = false`): `zoneTrackStepData_of_lt`/`_of_not_lt`;
  the represented tape moves by `zoneTrackTape_rebalance_right`/`_left`, whose hypotheses (the
  lower opposite zones full, room for one pass) come from fullness and the scan
  (`zoneShiftIndex_empty`, `_nonempty`);
- fullness after the rebalance: `zoneRebalance_of_lt`, `zoneCascade_true`/`_false`,
  `zoneCascadeRight_lengths`/`zoneCascadeLeft_lengths` below and at the index,
  `zoneRebalance_frame` above it;
- an extension (`zoneTrackStepData_of_not_lt`): invisible (`zoneTrackTape_extend`), the new level
  half full on both sides (`ZoneContents.extend_words_last`), the old ones kept
  (`extend_words_castSucc`); the retried rebalance scans to the new level
  (`zoneRebalanceIndex_extend_of_short`, `zoneShiftIndex_extend`), and a later track's index is
  unchanged by an earlier track's extension when below the old level
  (`zoneShiftIndex_extend_of_lt`);
- the other tracks: after `rw [zoneRebalanceData_eq]`, `Function.update_of_ne` keeps every track
  but `t`.

**The first round** starts from `HS.tm.initCfg (x.map Sum.inl)`, whose tape `0` is blank, not a
zoned tape: it agrees with `zonedTape` of the empty contents at level `0` off cell `0`
(`zonedTape_blank_outside`, `zoneStart_eq`), and the leaf's write makes it the zoned tape of the
home-written contents (`zonedTape_homeWrite`); the represented tapes start blank
(`zoneTrackTape_empty`). **State the round lemma so that the first round is an instance:** its
start's tape `0` agrees with `zonedTape D.2` off cell `0`, and its cell `0` is either blank (with
every home blank) or `zonedTape D.2 0`. The leaf's decoded read `(zoneCellOfCell (w 0) t).join`
is the same on both (`zoneCellOfCell_none`, `_inr`), and the lemma ends exactly at
`enc (step c) D'`.

### 5. The run and the forward bound

- **The iteration** (`[Q2]`): from the round lemma of step 3 and the invariant of step 4, the run
  of `HS` through the first `s` rounds, for every `s` such that `M`'s run is live at every time
  `< s` (so every `s ≤ t₀` when `M` first halts at `t₀`, `MultiTapeTM.exists_first_halt`, and every
  `s` when it never halts: one lemma serves this step and step 6), as one segment against
  `{none}`, by `Turing.Segment.iterate_seq` (`[Q2]`, ruled API first). **Its starts are explicit
  encodings, not the run itself:** `cs 0` is `HS`'s initial configuration, and `cs (r + 1)` is
  `enc (c_{r+1}) (D_{r+1})`: the leaf at `c_{r+1}`'s state, tape `0` the zoned tape `zonedTape
  D_{r+1}.2` with its head at `0`, tape `1` blank with its head at `0`, `c_{r+1}`'s input
  position, and output `c_{r+1}.output.map Sum.inl`, with `c_r := M.tm.runFrom (M.tm.initCfg x) r`
  and `D_r` the data orbit. Each round of step 3 is then one segment from `cs r` to `cs (r + 1)`.
  Defining `cs r` as `HS`'s run at the summed times would need the induction over rounds; never
  write it yourself.
- **The data orbit.** The data at each round is a function of `M`'s run (its head moves); define
  it once by recursion (a `tt_` definition) and read `idx t s` off it: the scanned index of track
  `t` at its step in round `s`, `0` for a stay.
- **The side totals** (the quantity both bounds below rest on): per track and level `i`, the
  number of stored cells on one side over the levels `≤ i`. Under fullness it changes by exactly
  `±1` per move whose scanned index is `≤ i`, is `2^{i+1} − 1` after a move whose index is `> i`,
  and is unchanged by an extension, which adds only higher levels (`zoneCascadeRight_lengths`,
  `zoneCascadeLeft_lengths` below and at the index, `zoneRebalance_frame` above it,
  `extend_words_*`). For the level bound also state its global form: the side total minus
  `2^{D.1} − 1` is the track's net displacement.
- **The count hypothesis** (gate 97's note 8, the book's argument): after a step of track `t`
  that scans beyond level `i`, its levels `0, …, i` are half full on both sides; each later step
  changes the number of cells on one side of those levels by at most one; so two such steps are
  at least `2^i` steps apart, and `#{s < T | i < idx t s} ≤ T / 2^i + 1`.
- **The level bound:** an extension at level `ℓ` needs every feeding zone empty, a displacement of
  at least `2^ℓ − 1` cells from the balanced layout, which an extension does not change; so the
  level after `s` steps is at most `Nat.log 2 s + 1`, and `L := Nat.log 2 t₀ + 1` bounds every
  `idx` (`zoneRebalanceIndex_le`). **Within round `s`, bound `idx t s` by the level after `s + 1`
  rounds, not after `s`:** an earlier track can extend mid-round. Since `s + 1 ≤ t₀` this is still
  at most `L`.
- **The cost:** `sum_cost_le_of_count k t₀ L A B idx cost` gives
  `Σ_{s < t₀} cost s ≤ B · t₀ + k · (A · ((L + 2) · t₀ + 2^L) + t₀)`; then
  `2^L ≤ 2 t₀` (`Nat.pow_log_le_self`, with `t₀ ≠ 0` from `FinTM.not_computesInTime_zero`) and
  `Nat.log_mono_right` give
  `≤ c₁ · ((t₀ + 1) · (Nat.log 2 (t₀ + 1) + 1))`, and `t₀ ≤ t` with `ComputesInTime.mono`. Any
  constant per `M` serves. **Never re-prove the layer cake or the geometric sums.**
- **The output:** at the halting round `HS` has halted with `c.output.map Sum.inl`
  (`FinTM.computesInTime_iff`).

### 6. The converse

If `HS` halts on `x.map Sum.inl` at some `t'`: while `M` is live, every round is live and takes
positive time (step 3), so `HS` is live through the first `s` rounds for every `s`; a source
that never halts would keep `HS` live past `t'`. So `M` halts at some `t₀`, `HS` halts at the end
of round `t₀ - 1` with `(M's output).map Sum.inl`, and its completed output is unique
(`FinTM.ComputesInTime.output_unique`). Step 0 finishes through `alphabet_reduction_run`.

## Edge cases that must stay true

- `k = 0` (`[Q1]`), and `k = 1` (one track: the scratch tape is still tape `1`).
- `t = 0` is impossible (`FinTM.not_computesInTime_zero`); `t = 1`: `c · 2 · (Nat.log 2 2 + 1)`
  covers the first round and the alphabet reduction's factor.
- A source that halts at its first transition: one leaf step, no track step.
- Stays: no rebalance, `idx = 0`, never counted.
- The first move of a track at level `0`: a short scan, the extension, and the retry (time at most
  `2A`, gate 97's note 7).
- Several tracks extending in one step: each extension lays out a level on every track.
- An input head at either end of `x` (clamped moves, `moveInputPos`), and `x = []`.
- A source write of a blank (`some none`) and no write (`none`): `Action.apply_workTapes`.
- A source that emits at its halting transition: `HS` emits in the same transition.
- A source that never halts: no completed output of `M'` (the converse).

## Gate guidance (binding)

- **Gate 92** (the statements): true as stated for every `M`, `k = 0` and `k = 1` included
  (note 6); the image converse is adequate for G5 because the simulator writes only bit images
  (finding 3); the docstrings are frozen. `two_work_tapes_binary` reads `ComputesFunInTime` only
  through `computesFunInTime_iff` (finding 1): you do not touch it.
- **Gate 97** (the API):
  - note 7: the abstract exit set with `none ∉ X` is what `Contract.inPhase` needs; a round's
    positivity comes from its own seams;
  - note 8: `sum_cost_le_of_count` is sound at `k = 0`; the count form is satisfiable with this
    layout (`zoneCapacity i = 2^{i+1}`);
  - note 9: the track step's constant is `A = 2C + C' + 2` (`4737` at the landed rows); you need
    only its existence;
  - note 10: the envelopes are not exported; your bound is on time (`Contract.time_envelope` if a
    head bound is ever needed);
  - minor 5 (published as `zoneRowPre_congr`, `zoneRowPre_mapState_iff`): cite them; never
    re-derive the precondition's independence of the state.
- **Gate 22's two carried minors** are met by #197: do not rebuild the fit probe's
  `trackStep_fit`, `amortized_le` or `run_cost_le`.

## Ground rules (binding)

1. **File ownership:** only regions (a)–(d). List every new declaration with its role.
2. **Statement freeze** over the target and every landed public declaration.
3. **No new public declaration.** Privates only, under `tt_`.
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and continue with every item that does not depend on
   it. A host, row or published fact that the route needs and this brief does not name is an
   escalation: name the contract or lemma you need. Checkpoint 2 (the leaf), checkpoint 6 (pure
   arithmetic over the data orbit) and checkpoint 7's arithmetic do not depend on the controller;
   checkpoints 5 and 8 depend on 3 and 4.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports:** exactly region (a)'s.
7. **One proof per shared argument.** Never write a second track step, phase host, seam,
   embedding, loop or input device; never re-walk `ZoneRebalance`'s `zr_` or `ZoneStep`'s
   privates, `SingleTape`'s zero-tape embedding or sweep simulation, or `AlphabetReduction`'s
   `arTM_computes` and `arCfg_*`.
8. **Size:** no cap; report the line counts (base: 86 lines; 2 public, 0 private).
9. **Continuation budget:** a partial is expected and fine; an unreported gap is not. A partial
   zip states the checkpoints reached, every open declaration with its literal "Proof sketch",
   and the target's axiom walk.
10. **The pinned base, and no unfolding** (user, 2026-10-16; scope 2026-10-23):
    - other files' TCSlib definitions are read only through their published equations, as listed
      above; core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step, but are
      never passed to `simp`, `rw` or `unfold`;
    - your own file's definitions (the leaf, the controller, the invariant, the data orbit) may be
      unfolded. For your leaf, read `MultiTapeTM.step` through `step_of_some` and `Action.apply`
      through `Action.apply_*` and `Action.apply_workTapes`; unfold only your own transition
      function (both are in the seal);
    - **self-check by both methods** (neither alone is complete):
      - a **seal test**: a scratch copy of your module with `attribute [local irreducible]` on
        every other-file TCSlib definition your proofs mention (start from the route probe's
        seal, 15 definitions, and extend: at least `zoneRowPre`, `zoneRebalanceIndex`,
        `zoneRebalanceData`, `zoneExtendData`, `zoneTrackStepData`, `zonedTape`,
        `zoneHomeWrite`, `zoneTrackTape`, `zoneShiftIndex`, `zoneRebalance`, `zoneCascade`,
        `ZoneContents.extend`, `ZoneContents.words`, `zoneCapacity`, `zoneCellOfCell`,
        `Contract.inPhase`, `Contract.zero`, `Contract.Positive`, `Turing.Segment`,
        `Turing.HeadBox`, `Cfg.bindState`, `Cfg.mapState`, `phaseHostTM`,
        `MultiTapeTM.runFrom`, `MultiTapeTM.initCfg`, `Cfg.init`, `FinTM.ComputesInTime`), and
        `attribute [-simp]` on the `@[simp]` definitions among them (`Action.apply`,
        `MultiTapeTM.initCfg`, `Cfg.init`, …), which must still elaborate, **with controls**: per
        sealed definition, a goal that closes by `rfl` unsealed and fails sealed;
        `ZoneSym` and `ZoneCell` are reducible `abbrev`s through which the alphabet gets its
        `Fintype` and `DecidableEq`: Lean cannot seal them, and they stay out (the route probe's
        `README.md`);
      - an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
        argument in your diff, each other-file name classified (a theorem, or a definition: a
        finding).
      - **Ship the raw outputs** of the seal and its controls, with their commands and exit
        statuses. A seal not run, or one without controls, is a checklist failure.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`), and no private declaration of another file.

## Checkpoints

1. Region (a), the bootstrap, and the frame: the reduction of the target to `HS`'s two properties
   through `alphabet_reduction_run` (step 0), with the zero-tape case by R1 (step 1).
2. The leaf: its machine and its one-step lemma (reads, home write, input move, emission, exit or
   halt), through `step_of_some`, the `Action.apply_*` fields and `zonedTape_homeWrite`.
3. The controller `HS` (phases, redirects, finiteness), generic in the track-step family, and one
   round as a segment with its time bound (step 3), the halting round included.
4. The invariant (step 4) except fullness: its preservation by a round, and the first round.
5. The iteration to the source's first halt (step 5, by `Segment.iterate_seq`); `HS`'s output
   there.
6. Over the data orbit (pure arithmetic on the data maps): fullness and the side totals, then
   the count and level bounds.
7. The cost through `sum_cost_le_of_count`, and the forward property of `HS`.
8. The converse property of `HS`.
9. `two_work_tapes_run` proved; for a construction that departs from the frozen sketch, a
   proposed `**Implementation.**` paragraph in `REPORT.md`.

**Add no new admission:** a helper is inserted only once proved. The freeze check for a partial is
the axiom walk: `sorryAx` reaches the target only through its own open body.

## Duplication governance (binding)

- Run the v3 screen **before and after**, one run at a time, under `nice -n 10`, each on a
  frozen copy of its commit (`git worktree add <dir> HEAD`). The before screen, after your first
  edit, must equal the screen base (the overlay changes only an import).
- **The population** is 22 files
  (`campaign/fills/u2s/inputs/u2s-fill-g5/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/ZoneStep`, `Build/ZoneRebalance`, `Build/ZoneTape`,
    `Build/Zone`, `Build/Contract/Basic`, `Build/Contract/Seam`, `Build/Seam`, `Build/Embed`,
    `Robustness/AlphabetReduction`, `CfgFacts`, `StateRenaming`, `Configuration`,
    `Deterministic`, `Finite`, `Simulation`;
  - the known hazards: `Robustness/SingleTape` (the zero-tape embedding and the sweep
    simulation), `UniversalTlogT`, `Build/StepBlockForward` (H2-F's forwarding loop),
    `Universal` (gate 92's stationarity pair), `SymbolLift` and `Build/Contract/Lift`.
- **The base** is `campaign/fills/u2s/logs/u2s-fill-g5-screen-base.txt`: 1,210 declarations,
  819 pairs, 281,024 characters (MEASURED at your base), with 0 pairs on your file.

```sh
P=campaign/fills/u2s/inputs/u2s-fill-g5
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with a declaration of your file on one side. Nothing is
  pre-disclosed.
- **Semantic duplication (required).** For **every** private lemma you add, search for a published
  declaration that states it or a generalization: in the tree and on every open PR branch, by
  name and by statement (`git grep`), and by an `exact?`/`apply?` probe. `REPORT.md` lists, per
  private, the search and its result. The pre-ship probe `G5RouteExact.lean.txt` poses the route
  probe's three lemmas to `exact?`: no library lemma closes any of them.
- **Search inline steps, not only statements** (WORKFLOW §3): sweep your proofs for
  `Nat.exists_eq_add_of_le` with `runFrom_add` and `runFrom_of_halt`, `lt_trichotomy` or
  `Nat.find` over runs, and five-line `Cfg.ext` blocks, and test each hit against the published
  API.
- **The acknowledged families you may touch** (`campaign/duplication-ledger.md`); a find inside
  one is an accounting minor, outside every one a major:
  - **ZP-1**, the zone row's precondition under a change of state: canonical
    `zoneRowPre_congr`, `zoneRowPre_mapState_iff`. Cite them at every phase start and redirect.
  - **RN-1**, renamed configurations converted field by field: canonical
    `Cfg.mapState_eq_of_fields`. No five-line `Cfg.ext`/`Cfg.mapState_*` block.
  - **WS-1**, one step keeps a configuration in a window, and window monotonicity: canonical
    `Cfg.InWindow.apply_iff`, `Cfg.InWindow.mono` (`Build/CfgRecord`, merged with #196). They are
    at your base but not in your imports, and no import may be added. Your bound is on time, so
    expect no member; for a head bound use `Contract.time_envelope`.
  - **RI-1** (retired), the round iteration along a sequence: canonical `Round.iterate_seq`.
    Your iteration cites its generalization `Segment.iterate_seq` (#202).
  - **FH-1**, the first halting time: canonical `MultiTapeTM.exists_first_halt`; never `Nat.find`
    over runs.
  - **RS-1**, the restart identity (a relabelled initial state): cite `initCfg_eq`,
    `phaseHostTM_q₀` and the `with q₀` equations rather than a `Cfg.ext` block.
  - **RO-1**, `M.runFrom c 1 = M.step c`: no public form; use `runFrom_succ_eq_step'` and
    `runFrom_zero`, and report each inline use.
- **Known hazards** (private proofs to cite around, never to copy): `ZoneRebalance`'s
  `zr_exitsContract` and `zr_singletonContract` (an exit set restated by an equality: compose your
  round as segments instead, step 3); `ZoneStep`'s `zs_rowPre_rebalancePost`; `SingleTape`'s
  `unusedTapeTM` family; `AlphabetReduction`'s `arCfg_run`; H2-F's `fl_*`. A pair at 90% or more
  is a copy. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists
  each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache for your roots only (42 roots, addendum v2.6
  Part 1); **never `lake build`**; `scripts/lean_check_tree.sh` for every check, one Lean process
  at a time.
- **Bootstrap** from `campaign/fills/u2s/orders/u2s-fill-g5.txt` (105 modules, computed on the
  overlay), after your first edit, logging each module's start and end time and maximum memory.
  **The base sorry-warning set** has 22 entries in 9 modules
  (`campaign/fills/u2s/logs/u2s-fill-g5-base-sorries.txt`); yours is `TwoTapes`' one. Record the
  base list by name first, and report any difference.
- **Final checks:**
  1. `TwoTapes`: zero errors, no sorry warning (for a partial, exactly the open target's), and no
     other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours.
  3. Re-run the import probe (`G5ImportProbe.lean.txt`), extended by every further name you cite: 0
     errors.
- **Axiom prints** (a scratch copy of your module with `#print axioms` appended) for
  `two_work_tapes_run`, `two_work_tapes_binary` and every new private, and for
  `Turing.universal_TlogT` (in a probe importing `UniversalTlogT`): within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL
  (base: 0 FAIL, 71 WARN over 92 files), and the policy linter on your file (base: 0 findings).
  No new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target: 21 entries in 8 modules, `Simulation` 1,
`Composition` 3, `Build/Wrappers` 2, `Build/Loop` 5, `Encoding` 1, `ClassP/TimeConstructible` 2,
`Build/Primitives` 3 and `Build/RecordTable` 4. If a proof seems to *need* one of
them, that is an escalation, not a license.

## Known pitfalls at this pin

1. **The `simps` field equations are pointwise** (`Cfg.mapState_workTapes`, `Cfg.init_workTapes`,
   `Cfg.bindState_workTapes`, …): `funext` before `rw`, or the step closes by unfolding and the
   seal rejects it.
2. **`Contract.inPhase` needs live exits and other-phase targets**: `none ∉ X` (so the halting
   leaf step is read through `phaseHostTM_run_le`, not `inPhase`) and `q.1 ≠ p` for every
   redirect target (its hypothesis `hsome`; its docstring explains why a redirect back to the
   phase's own entry cannot be allowed).
3. **A round whose heads all stay** has no track step; with stays as zero-time phases (the
   recommended shape) each round still passes through every track's phase, so the leaf never
   redirects to itself.
4. **The phase host's exit set is a set-builder** (`{q | ∃ s, some s ∈ X ∧ q = red p s}`), not a
   singleton: `Contract.trans` and `Contract.seq` need `{some e}`. Compose rounds as segments.
5. **Instances on `Σ i, Ph i`**: with `Ph` defined by cases, `Fintype` may need `inferInstanceAs`
   or `letI` per case (`ZoneRebalance`'s extension row needed a raised
   `synthInstance.maxSize`).
6. **The track-step family is existential**: `choose` it inside the body, and keep the controller's
   lemmas generic in it, so that no private definition depends on a classical choice.
7. **`Nat.log 2` in every statement**, `Nat.log2_eq_log_two` where a `Nat.log2` appears.
8. **A halted run is frozen** (`MultiTapeTM.runFrom_of_halt`): the bound at `t` follows from the
   halt at `t₀` by `ComputesInTime.mono`, never by a hand-made `Nat.exists_eq_add_of_le` split.
9. **Rewrite whole `ZoneData` values, never `.snd` alone.** `ZoneData k` is `Σ ℓ, Fin k →
   ZoneContents ℓ`, so a track's contents carry their level. After `rw [zoneRebalanceData_eq]`
   (or `zoneExtendData_eq`) the contents sit at `D.1` (or `D.1 + 1`), and the `Build/Zone` lemmas
   apply. A goal that prints as `f x = f x` but that `rfl` cannot close is a hidden-level mismatch.
9. `omega` with products as atoms (`ring` first); `nlinarith` for the `2^L` bounds, as `ZoneStep`
   does.

## REPORT.md checklist

- [ ] The preflight, the cache (the store's log first) and the bootstrap (per-module time and
      memory); the base hash, the ancestor check and the blob check.
- [ ] The overlay as the first edit; nothing outside regions (b)–(d).
- [ ] The checkpoints reached, one zip each.
- [ ] Every new declaration with its role; `HS`'s tapes, phases, redirects and leaf; the
      zero-tape case (R1) and the iteration (`Segment.iterate_seq`).
- [ ] The invariant, the count and level bounds, and `c₁`, `B`, `L` and `c`, term by term.
- [ ] The edge cases, each with the lemma that covers it.
- [ ] Promotion candidates (the round, `[Q3]`) and escalations, each stated mathematically, or
      "none"; a proposed `**Implementation.**` paragraph if the construction departs from the
      frozen sketch.
- [ ] Rule 10: the declarations cited outside your file (from an elaborated-constant walk), the
      import probe re-run as "N checks of M names", **the seal with its controls and both raw
      outputs**, the inspection table. Rule 11: a grep of your diff for the six R3 rows and for
      other files' private names.
- [ ] Duplication: both screens, every new pair with a disposition, the semantic search per
      private, the inline-step sweep, "new copies: none".
- [ ] File size, the final sweep tail, the axiom prints (the target, `two_work_tapes_binary`,
      `universal_TlogT`) and the lint lines.

## References

- [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009. (§1.7, the proof of Theorem 1.9.)
- [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing machines*, J. ACM
  13(4), 1966, 533–546.

---

## The drafting's questions, ruled (the user, 2026-11-05; G5's plan §8)

- **Q1, `k = 0`: separate**, through R1 (`embedEmitTM`) on two tapes with `c = 1` (route step 1),
  as the plan (§2) and the frozen sketch say. Never copy `SingleTape`'s private zero-tape
  embedding.
- **Q2, the iteration: API first.** #202 (gate 98) publishes `Turing.Segment.iterate_seq` in
  `Build/Contract/Basic`, with `Round.iterate_seq` re-proved as its corollary; this brief issues
  after it merges.
- **Q3, the controller:** decision G5-F1 stands (this fill writes it); note the round as a
  promotion candidate.
- **Q4, further API rows:** none found beyond Q2. An exit-set restatement is avoided by composing
  rounds as segments; a same-phase redirect by zero-time stay phases; `some entry ∉ X` for the
  track step stays unexported (gate 97's note 7).
- **Q5, the agent: Claude** (over the soft rule's Codex-first).
- **Q6, the estimate (ESTIMATE):** 1.2–2.2k lines in `TwoTapes`: the leaf and controller 250–400,
  the round 250–450, the invariant 300–500, the count and level bounds 200–400, the run, cost and
  converse 150–300, the frame and `k = 0` 50–150. Plan for one continuation brief.
