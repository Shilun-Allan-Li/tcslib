# External audit pack — B6 hosts: H3 and its step clock, H5, `U₀`, the bridges, and the addend-free `space_universal` (statement gate)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e, cluster B6), on the window
route of `Complexity.space_hierarchy` (design `machine-library-design.md` §16b item 3; backlog
RD-3). The RD-3 gate passed on 2026-10-13 (`audits/b6-restatement-findings.md`, 0/0/4) and ruled
that the hosts the route needs must pass their own statement gate before any consumer fill
(`policy.md` §1, *Hosts come first*). **This gate audits those hosts' public statements, in
landing form:**
- **H3**, the windowed runner: a pure specification `windowRun`, the step-clocked runner shared
  with C1, the windowed round loop, and two runners;
- **H5**, input devices: the native device and the bounded-prefix ruler device with its host;
- **`U₀`**, the self-application universal machine, and its startup;
- **the bridges** that `space_hierarchy`'s fill needs (space at every time, relabelling, window
  containment, the summary tag, the alphabet-reduction packaging);
- **the strengthened `Complexity.space_universal`**: the book's addend-free `C · s`, by user
  decision B1.

Every machine contract is `sorry` under a proof sketch. Every other declaration is proved:
definitions have their real bodies, and the pure lemmas have proofs that the gate checks only as
"elaborates, standard axioms". Nothing is landed yet.

| File (bundle path) | Content |
|---|---|
| `audits/evidence/b6hosts/gate/B6Hosts.lean.txt` (1837 lines) | **the landing-form unit**: eleven parts, each the body of one new module or a part of one existing module (table below) |
| `audits/evidence/b6hosts/gate/patches/*.patch` (8 files) | `diff -u` against the worktree for every existing file touched: six library files and two facades |

Supporting evidence, all in the bundle:
- the logs `audits/logs/b6-hosts-statements-{elaboration,cutcheck,freeze,axioms,names}.log`;
- the three probes `audits/evidence/b6hosts/gate/probes/*.lean.txt` (sanity, gated form, draft
  step clock);
- the scripts `audits/evidence/b6hosts/gate/scripts/*`, which regenerate every file and log
  (`runall.sh`);
- the draft this pack turns into landing form and its note, `audits/evidence/b6hosts/
  {B6HostsDraft.lean.txt, B6-hosts-design.md}`, with `audits/logs/b6-hosts-draft-elaboration.log`.

**Bundle:** `audits/b6-hosts-statements-bundle.md`, in the order of `BUNDLE-FILES.txt`: this
pack, `audits/TEMPLATE.md`, `policy.md`, `workflow.md`, the design document and the backlog, the
files under audit, the probes, scripts and logs, the draft and note, the RD-3 records, the H2-S
round-1 findings and pack, the H2 and C1 drafts the sketches cite, and every library file that
the statements, sketches or this pack cite.

**Provenance (maintainer).** A maintainer sub-agent wrote the draft against the checkout `wt-b6h`
(campaign commit `6aa9f67b`), and this landing form against the read-only checkout `wt-g5b6`.
All checks were then re-run, and every `file:line` here re-checked by script, at campaign commit
**`1781a230d2410ae2a09fbb961fe644512a6ba3c0`** (PR #84, fills-8), with the olean snapshot
`oleans-f8` of that commit. Per the integration record of PR #84, its only Lean changes since the
previous checkout are `Build/RecordTable.lean` (row 17, `Turing.exists_recordTemplateTM`, now
proved; statements unchanged) and `TuringMachine/CodeSimulator.lean` (new H1 and canonizer
privates; `h1Round_effect`'s statement unchanged). That was not re-verified by git, which the
brief forbids. Line numbers into those two files below are at `1781a230`.

## What the gate covers

1. **H3** (`Build/StepClock.lean`, `Build/WindowRun.lean`, `SpaceComplexity/WindowClock.lean`):
   the specification `Turing.windowRun` with its eight proved lemmas; the step clock
   `Turing.exists_stepClockTMVia` and C1's `Bool` form `Turing.exists_stepClockTM` (proved from
   it); the loop `Turing.exists_windowLoopTM`; the step-clocked runner
   `Turing.exists_windowRunnerTM`; the configuration-count runner
   `Turing.exists_configWindowRunnerTM`, which `space_hierarchy` cites.
2. **H5** (`Build/InputDevice.lean`): `Turing.inputCell`, `Turing.NativeAt` with three lemmas,
   `Turing.RulerAt`, the ruler device's correctness facts, the restoring boundary test
   `Turing.exists_rulerTestTM`, the call rows `Turing.exists_rulerDeviceTM`, and the ruler host
   `Turing.exists_rulerHostTM`, **restated as a block simulation** (H2-S finding 2).
3. **`U₀`** (`TuringMachine/SelfUniversal.lean`): `Turing.exists_selfStartupTM`,
   `Turing.exists_selfUniversal`, with **`U₀`'s sketch rewritten** on H2-S finding 4's reset
   invariant, naming its dependency on H2-S round 2.
4. **The bridges**, appended to existing modules: `StateRenaming`, `Encoding`, `ConfigCount`,
   `CfgRecord`, and the public summary code in `ConfigGraph`, which replaces S1b's private copy.
5. **`Complexity.space_universal`, strengthened** to `C · s`, with its revised sketch citing the
   ruler host, and the probe deriving the gated statement from it.
6. **The homes, the patches, the freeze**: that no existing statement changes except
   `space_universal`'s strengthening (and one private statement re-pointed under B3).

Out of scope: proofs and fill routes beyond the sketches; H2's own statements (H2-S, its own
gate); the design-record updates that follow this gate (listed under the landing obligations).

## Decisions in force (verify that the files reflect them)

**User decisions of 2026-10-13, binding:**
- **B1.** `space_universal` is strengthened to the book's addend-free `C · s` **in this pack**:
  a patch to the landed `SpaceComplexity/Hierarchy.lean` (statement and revised sketch citing the
  ruler host), with the gated form derived as evidence that it only strengthens.
- **B2.** No binary-position device is stated; its registry row (design §14, H5) stays for other
  consumers.
- **B3.** The public `outSummaryCode` and `summaryTag`, with their lemmas, land in
  `SpaceComplexity/ConfigGraph.lean`, and S1b's private `sumCode`, `s1b_summaryWord` and
  `s1b_tagUpdate*` are re-pointed at them in the same PR, leaving no copy.
- **B4.** `exists_configWindowRunnerTM` and `configBound_le_two_pow` go to a new
  `SpaceComplexity/WindowClock.lean`; `Build/WindowRun.lean` imports nothing from
  `SpaceComplexity`.
- **B5.** The contracts are gated as `∃` statements now; named witnesses (`def …TM`, with the
  `∃` row as a corollary) come at fill time.

**Earlier rulings, verified by audits and not disposed of by them:**
- the window route, and `space_universal` forward-only (design §16b item 3; RD-3 gate);
- hosts first (`policy.md` §1; `workflow.md` §2, §4 rule 4; design §14);
- the H2-S round-1 audit (`audits/h2-promotion-findings.md`, 0/3/5), read-only here:
  - finding 1: `roundTM_iterate` needs `t ≤ T`, being repaired in H2-S round 2;
  - finding 2: an input device is a positive finite **block** simulation with intermediate
    frames, output, exit cuts and head envelopes; literal lockstep only for the native device
    and Z1;
  - finding 4: `U₀`'s forwarding relates each reset seam to `{c with output := []}`, tracks the
    real output separately, and forwards before the physical halt;
  - its consumer rulings for B6 `U₀` and `SU`.

## Homes and module names (the auditor rules on them)

| Part | Lands in | Kind | Size (MEASURED) |
|---|---|---|---|
| A | `TuringMachine/StateRenaming.lean` | appended at the end | 124 → 160 lines |
| B | `TuringMachine/Encoding.lean` | inserted before `exists_codeTM`, which becomes its time clause | 632 → 671 |
| C | `SpaceComplexity/ConfigCount.lean` | appended at the end | 493 → 590 |
| D | `TuringMachine/Build/CfgRecord.lean` | appended at the end | 5256 → 5272 |
| E | `SpaceComplexity/ConfigGraph.lean` | inserted after `outSummary_append_congr`; S1b re-pointed | 930 → 964 |
| F | new `TuringMachine/Build/StepClock.lean` | H3's step clock | 214 |
| G | new `TuringMachine/Build/WindowRun.lean` | H3: specification, loop, runner | 465 |
| H | new `SpaceComplexity/WindowClock.lean` | H3 with the configuration-count clock; the bridges to windows | 212 |
| I | new `TuringMachine/Build/InputDevice.lean` | H5 | 339 |
| J | new `TuringMachine/SelfUniversal.lean` | `U₀` | 147 |
| K | `SpaceComplexity/Hierarchy.lean` | replaces `space_universal`; header and one sentence of `space_hierarchy` | 312 → 316 |

The facades `TCSlib/Complexity/TuringMachine.lean` (imports and lists `Build/StepClock`,
`Build/WindowRun`, `Build/InputDevice`, `SelfUniversal`) and `SpaceComplexity.lean` (imports and
lists `WindowClock`) are patched too. `TCSlib.lean` already imports both facades.

**How a part lands** (`scripts/gate.py land`, log `cutcheck` §1). A new module is the copyright
block, the part's `-- @imports`, the standard options and the part verbatim. A part of an
existing module is placed as its `-- @place` line says. *Append* adds the part with its namespace
lines at the end of the file. *Insert* puts it, without them, before or after a named line.
*Replace* (part K) swaps one declaration with its docstring. Then the edits of
`scripts/edits.py` follow, each asserted to match exactly once: the modules' docstrings,
`exists_codeTM`'s proof, S1b's re-pointing, `Hierarchy`'s header and one sentence, and the
facades. `diff -u` against the worktree gives the patches. Each patch replays (`patch -p1` on a
scratch copy) to the patched file byte for byte (log `cutcheck` §2).

**Why these homes.**
- The design note's §8, amended by B3 and B4, with **two further moves** (point P1 below):
  - `inWindow_of_spaceUsed_le` goes to `WindowClock`, not `ConfigCount`: it uses
    `Turing.Cfg.InWindow` (`Build/CfgRecord.lean:100`), which `ConfigCount` does not import, and
    `CfgRecord` is too heavy an import for it;
  - `windowRun_summary_of_halts` goes to `WindowClock`, not `ConfigGraph`: there it would make
    `ConfigGraph` import `Build/WindowRun`.
- **Layering (B4), checked** (log `cutcheck` §4): the import closures of `StepClock`,
  `WindowRun`, `InputDevice` and `SelfUniversal` contain no `SpaceComplexity` module. Only
  `WindowClock` imports `SpaceComplexity` modules: `ConfigGraph` for the tag, `ConfigCount`
  through it.
- `InputDevice` imports `Build/VirtualInput` (Z1, whose host pattern the ruler host follows) and
  `UniversalStartup` (for `Turing.universal_pair_length`, `UniversalStartup.lean:63`).
  `SelfUniversal` imports `UniversalStartup` (the canonizing startup) and `CodeSimulator` (for
  `Turing.tableBitsK`, `CodeSimulator.lean:99`, which the startup statement uses).
- `Hierarchy.lean` gains **no import**. Its revised sketch cites the new hosts, but the file does
  not use them yet (`policy.md` §1: import only what the file uses). The fill adds the imports
  (point P5).
- Namespaces: everything is `Turing.*`, except `Complexity.space_universal`.

**Landing obligations** (outside the audited statements, so that none is forgotten):
- the facade patches above;
- design §14's H3 and H5 rows, §16b item 3 and backlog RD-3 updated to these names and homes;
- the H5 row records that the binary-position device is not stated (B2);
- the dedup ledger records S1b's removed copy (B3);
- a full fresh sweep. Encoding has 163 reverse dependencies and StateRenaming 176 (MEASURED,
  import graph); the additions are new names screened against the whole tree.

## What the files state (verify)

**Part A** (`Turing.MultiTapeTM`): `relabelState_visitedByTapeHead tm e input t i`: in `t` steps
from the initial configuration, head `i` of `tm.relabelState e` visits exactly the cells head
`i` of `tm` visits. `relabelState_spaceUsed`: hence equal `spaceUsed` at every `t`. Both proved.

**Part B**:
- `CodeTM.one_le_spaceUsed M x t`: `1 ≤ spaceUsed` of a coded run at every time.
- `exists_codeTM_spaceUsed M hk`: some `M' : CodeTM` satisfies `exists_codeTM`'s `∀ x o t,
  M'.ComputesInTime x o t ↔ M.ComputesInTime x o t`, **and** `∀ x t`, equal `spaceUsed`.
- `exists_codeTM` keeps its statement and is now two lines from it (point P2).

All proved.

**Part C** (`Turing.FinTM`), all proved:
- `ComputesInTime.spaceUsed_le_of_halt`, over any alphabet: a run that has halted with
  `w` by `t` within `s` cells has `spaceUsed ≤ s` at **every** `t'`.
- `ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le`: `ComputesInSpace f s` gives
  `ComputesFunInTime f (n ↦ configBound M n (s n))` and `∀ x t, spaceUsed ≤ s |x|`, the `hM`,
  `hS` of `one_work_tape_binary_spaceUsed` (`Robustness/SingleTape.lean:2290`).
- `decidesInSpace_of_alphabetReduction e D L S hD hS`: if `D` over `Γ` halts on every `x.map e`
  with `[indicator L x].map e`, and `∀ x : List Γ, ∀ t, spaceUsed ≤ S |x|`, then
  `∃ c M, M.DecidesInSpace L (n ↦ c · (S n + 1))`.

**Part D**: `Cfg.inWindow_init q₀ x s`: `(Cfg.init q₀ x).InWindow s`. Proved.

**Part E** (`Turing`), all proved:
- `outSummaryCode`: `empty ↦ 0`, `accept ↦ 1`, `dead ↦ 2`, with `outSummaryCode_injective`;
- `summaryWord τ`: `[]`, `[true]`, `[false]` for `τ = 0, 1, 2`;
- `summaryTag τ b := outSummaryCode (outSummary (summaryWord τ ++ b.toList))`;
- `summaryTag_none`, and `summaryTag_append u b`:
  `code (summary (u ++ b.toList)) = summaryTag (code (summary u)) b`;
- `outSummaryCode_eq_one_iff u`: `code (summary u) = 1 ↔ u = [true]`, and
  `outSummaryCode_nil`.

S1b's seven private copies are deleted. Their four users (`count_windowed_vertices`,
`s1b_record`, `s1b_record_eq_iff`, `s1b_record_accepts`, all private) now name the public code;
the last of them changes its private statement accordingly. The five deleted `s1b_*` lemmas had
no users (grep).

**Part F, the step clock** (`Turing`):
- `clockCfg q c ct cp`: the host configuration with control `q`, `c`'s input head and output,
  tapes `Fin.lastCases ct c.workTapes` and heads `Fin.lastCases cp c.workTapePos`;
- `wordPatch ct cp u`: `u` in cells `cp … cp + |u| - 1`, `ct` elsewhere;
- `Cfg.Stopped stopAt c`: `c` is halted, or live in a state `s` with `stopAt s`.

`exists_stepClockTMVia e M stopAt` gives a host `H` with `inj`, and injective `finish` and
`timeout`, the three pairwise distinct. Start it at `inj q` from a live `c` at state `q`, with a
delimited word `w`, digits by `e`, of value `d = ofDigits 2 (w.map toNat)`, at the counter head
(cells `cp - 1 … cp + |w|`).
- *Finish.* If the body first stops at `τ ≤ d`, then within `T ≤ 5τ + 2|w| + 2` steps the host is
  exactly `clockCfg (finish (state at τ)) (body at τ) (wordPatch ct cp (w'.map e)) cp` for some
  `w'` with `|w'| = |w|`.
- *Timeout.* If the body does not stop by `d`, the same holds with `timeout`, the body at `d`, and
  `T ≤ 5d + 2|w| + 2`.
- *In both cases*: no `finish` or `timeout` before `T`, and **a frame at every `u ≤ T`**: the
  host's body tapes, body heads, input head and output are the body's at some `v ≤ τ` (or
  `≤ d`), and the counter head is in `[cp - 1, cp + |w|]`.

`exists_stepClockTM`: the `Bool` instance in C1's draft form (proved).

**Part G, the specification:**
- `windowRun M s upd N c τ` (structural on `N`): at `0`, `(exhausted, c, τ)`. At `N + 1`:
  `halted` if `c` is halted; else, if `M.step c` is in the window, the `N`-round run from
  `M.step c` with tag `upd τ (outputSymbol c)`; else `(left, c, τ)`.
- Proved:
  - `windowRun_halted_of_run`: a halt at `t < N` inside the window gives `halted` at time `t`,
    with `σ` of its output;
  - `windowRun_spec`: the full three-exit characterization;
  - `windowRun_tag`: the tag is `σ` of the reported output;
  - `windowRun_stop_unique`: a stop does not depend on the budget;
  - `windowRun_exhausted_of_live`: `N` live, windowed rounds give `exhausted` at time `N`, even
    if that configuration is halted;
  - `windowRun_halts_on_last_transition`: a halt at `t + 1` emitting `b` is reported at `t + 2`
    rounds, with `b` in the tag.

**Part G, the machines:**
- `exists_windowLoopTM M upd hupd`: a module over `RecSym` with `entry` and an injective
  `stop : WindowExit → P` that avoids `entry`. Start it from the record of a windowed `c` on
  tape `0`, other tapes blank, native input as digits. Then:
  - at all times, heads stay within `C · (L + 1)` and the output is unchanged
    (`L = recordLength k |x| s`, `RecordTable.lean:151`);
  - for every `N` there is `t ≤ C · N · (L + |x| + 1)`, with no stop before `t`, at which the
    module is `d` with state `entry` (exhausted) or `stop e` (stopped) and the record interval
    rewritten to `windowRun`'s record; `t ≥ N` if exhausted.
- `exists_windowRunnerTM`: the same with a clock word `w` of value `d` on the last tape. There
  are `t ≤ 5d + 2|w| + 3` and `out` with exit at `t` and none before, heads within
  `C · (L + |w| + 1)`, silence, and the `spaceUsed` bound. Moreover:
  - **certified**: every stopping `N` with `C · N · (L + |x| + 1) ≤ d` gives `out`;
  - **determined**: `out ≠ exhausted` is a stopping `windowRun`'s exit, with its record on
    tape `0`, a same-width word on the clock interval, and everything else restored.

**Part H** (`Turing`):
- `FinTM.inWindow_of_spaceUsed_le`: `spaceUsed ≤ s` at `t` puts every configuration up to `t`
  in the radius-`s` window (proved);
- `windowRun_summary_of_halts`: `ComputesInTime x w t`, `spaceUsed ≤ s` and `t < N` give
  `windowRun M.tm s summaryTag N (initCfg x) 0 = (halted, run at t, outSummaryCode (outSummary
  w))` (proved);
- `FinTM.configBound_le_two_pow`:
  `configBound M n s ≤ 2 ^ (|Q| + posWidth n + 3 · k · (2s + 1))` (proved);
- `exists_configWindowRunnerTM`: as `exists_windowRunnerTM`, but with no clock tape. It
  satisfies `t ≤ C · 2^(C · (L + 1))`, heads within `C · (L + 1)`, and
  `spaceUsed ≤ (K + 1)(2C(L + 1) + 1)`. Every stopping `N ≤ configBound M |x| s + 1` gives
  `out`, and `out ≠ exhausted` is determined, with every other tape blank again.

**Part I** (`Turing`):
- `inputCell y i`: blank at `0`, `y[i - 1]?` otherwise.
- `NativeAt d i := d.inputPos = i`, with `inputSymbol_eq`, `move`, and `nativeAt_init`
  (position `1`).
- `inputCell_sub_eq_none_iff`: for `0 < ℓ ≤ p ≤ |z| + 1`, cell `p - ℓ` is blank iff `p = ℓ`.
  `inputCell_of_drop`: for `z.drop ℓ = y` and `i ≠ 0`, `inputCell y i = inputCell z (ℓ + i)`.
- `RulerAt ℓ r d i`: `0 < ℓ ≤ |z|`, `z.drop ℓ = y`, physical head at `ℓ + i`, and tape `r` holds
  the delimited `true^ℓ` from its head.
- `pairEncode_pairEncode_length`, `_drop`: `space_universal`'s input is a header of length
  `2|u| + 2|α| + 4` followed by `x`.
- `exists_rulerTestTM`: for `0 < ℓ ≤ p` and the ruler at the head, within `C(ℓ + 1)` steps, no
  verdict before, ruler head within `ℓ + 1`, it reaches `{d with state := if p = ℓ then yes else
  no}`.
- `exists_rulerDeviceTM`: read `inputCell y i`, or move to `ℓ + moveInputPos i m`, within
  `C(ℓ + 1)`, with everything else unchanged.
- `rulerHostCfg ℓ hz q c rt rp`: the host layout.
- **`exists_rulerHostTM`** (with `0 < C`): for every `t` there is `t'` with
  `t ≤ t' ≤ C(ℓ + 1)t`, and:
  - *endpoint*: the host at `t'` presents the source at `t` with a correct tag;
  - *exit cut*: a source live before `t` gives a host live before `t'`;
  - *frames*: at every `u ≤ t'`, the bank tapes, bank heads and output are the source's at some
    `v ≤ t`, the ruler tape is `rt`, and the ruler head is in `[rp - 1, rp + ℓ]`;
  - *space*: the bank visited sets equal the source's, and the ruler's are within `[rp - 1,
    rp + ℓ]`.

**Part J** (`Turing`):
- `exists_selfStartupTM c`: a machine `R` with `K + 3` tapes and `exit`. For each `α` there are
  `T` and `B` such that, for every `w`, `R` from `initCfg (pairEncode α w)` is at time `T`
  exactly `⟨some exit, 1, tapes, all heads 0, []⟩`: tape `1` is `bufferTape (tableBitsK tr)`,
  tape `2` is `p ↦ bufferTape (unaryFin q₀) (p - 2)`, and the rest are blank. There is no exit
  before `T`, the output is `[]` up to `T`, and `spaceUsed ≤ B`.
- `exists_selfUniversal c`: `∃ U₀, ∀ α, ∃ C > 0`: every halting run of `c.decode α` on
  `pairEncode α w` with output `o` within `s` cells has a `U₀` run that halts with `o` within
  `C · (s + 1)` cells.

**Part K**: `Complexity.space_universal` with last line `≤ C * s`, otherwise byte-identical to
the gated statement (log `freeze`: the one authorized statement change).

## Changes from the draft (verify against `elaboration` log §6)

The comment-stripped comparison with the draft: 53 declarations kept, of which **two change
their statement**; one name moves; one declaration moves to a probe. Both changed statements are
strengthenings.
1. **`exists_rulerHostTM` becomes a block simulation** (H2-S finding 2, Task 2). The draft gave
   only the endpoint at `t' ≤ C(ℓ + 1)t` and the visited sets. Added:
   - the lower bound `t ≤ t'`;
   - the exit cut;
   - the intermediate frames (bank tapes and heads, output, ruler tape and ruler head);
   - `0 < C`.

   The probe `Sanity.lean` derives the two consumer directions from it: the host halts with the
   source's output, and the host halts only if the source has.
2. **`exists_stepClockTMVia`'s trajectory clause becomes a frame clause.** The draft gave the body
   heads only; now the body tapes, input head and output are the body's at some earlier body
   time. Without it the runner's silence and restoration do not follow from the clock's contract.
   C1's corollary `exists_stepClockTM` is unchanged, word for word, and still proved.

   **Note for C1.** The C1 host-contracts pack cites both names, from its fills' sketches; no C1
   statement uses them. `exists_stepClockTM` is byte-identical to the draft's (checked by
   script). `exists_stepClockTMVia` changes only inside its two frame clauses, and is strictly
   stronger: `probes/StepClockDraftFormProbe.lean` proves the draft's statement, extracted
   verbatim, from the new one by dropping conjuncts.
3. **`space_universal` lands in place** (B1, part K). `Complexity.B6Draft.space_universal` is
   now `Complexity.space_universal`, the same text. `space_universal_gated_form` moves to
   `probes/GatedFormProbe.lean`, whose statement is extracted mechanically from the worktree.
4. **`U₀`'s sketch is rewritten** (Task 2). The reset invariant of H2-S finding 4: each seam
   represents `{c with output := []}`, the physical output is the real cumulative output, a leaf
   forwards each emission, and on the last round before the physical halt. The iteration names
   H2-S round 2's repaired `roundTM_iterate`. The statements are unchanged and name no H2 draft
   declaration (log `names` §2: the only H2 names, `Turing.StepBlock.roundTM_effect`,
   `roundTM_iterate`, `roundTM_visited`, `h1Round_effect`, are in sketches).
5. **B3**: the public code lands in `ConfigGraph` (part E), and the private copies go.
6. **B4**: the new `WindowClock` module, plus the two moves of P1.
7. **`exists_codeTM` re-derived** from `exists_codeTM_spaceUsed` (P2), so that the relabelling
   is not built twice.
8. **Documentation:**
   - the draft's references to scratch files are removed;
   - status labels and [AB09] locations added;
   - every sketch names full declarations (one shorthand `_buffer` expanded);
   - the two Hierarchy docstrings are synchronized (P4).

## The RD-3 gate's requirements, mapped

| Requirement (`audits/b6-restatement-findings.md`) | Where it is met |
|---|---|
| Row 1: a bounded-prefix device with a unary ruler; addend-free `C · s` | `RulerAt`, `exists_rulerTestTM`, `exists_rulerDeviceTM`, `exists_rulerHostTM`; part K; the ledger facts `pairEncode_pairEncode_length`, `_drop` and `CodeTM.one_le_spaceUsed`; `GatedFormProbe` |
| Row 3: one optional early exit plus exhaustion; merge, then distinguish; three outcomes exposed | Route B of `exists_configWindowRunnerTM`'s sketch; `WindowExit`; the runners' certified and determined clauses |
| Rows 2 and 4 (records) | closed at RD-3 (resolutions minors 2 and 4); part K keeps the corrected Finding B wording |
| Note 7: carry the invariants into H3 | the surplus `N ≤ configBound + 1`; the halt test in `windowRun`; restoration in every endpoint; `inWindow_of_spaceUsed_le` |
| Note 8: startup, head reset, output, all-times as contracts | `exists_selfStartupTM`; `ComputesInTime.spaceUsed_le_of_halt` |
| Check 2: input position `1`, empty output, table on a work tape | `exists_selfStartupTM`; `nativeAt_init` |
| Check 3: uniform space | `exists_configWindowRunnerTM`'s envelope `C · (L + 1)`, `C` depending on `M` and `upd` only |
| Check 4: the four-factor bound, the strict surplus | `configBound_le_two_pow`; `windowRun_exhausted_of_live`; `N ≤ configBound + 1` |
| Check 5: `Fin 3` tag, accept exactly `[true]`, totality | part E; the runners always exit |
| Check 6: normal form, all-times bridge, relabelling, containment, flip | `computesFunInTime_and_forall_spaceUsed_le`, `exists_codeTM_spaceUsed`, `inWindow_of_spaceUsed_le`, `windowRun_summary_of_halts` |
| Check 7: alphabet reduction | `decidesInSpace_of_alphabetReduction` |
| Sanity: restoring suffix-boundary test, empty input included | `exists_rulerTestTM` (any `z`); `inputCell_sub_eq_none_iff`; probes at `z = [true]` |
| Sanity: `U₀` startup, empty output, position `1` | `exists_selfStartupTM` |
| Sanity: all-time space under relabelling | `relabelState_spaceUsed` |
| Sanity: an H3 run halting on its last transition, emitting the deciding bit | `windowRun_halts_on_last_transition`, instantiated in `Sanity.lean` (machine `emitHalt`), with the clock-exhaustion twin and negative control `neg4` |

**H2-S, mapped.**
- Finding 1: `U₀`'s sketch step (iii); the ruler host carries its own lower bound `t ≤ t'`.
- Finding 2: the ruler host's five clauses.
- Finding 4: `U₀`'s sketch step (ii), and part K's sketch step (ii).
- Ruling for B6 `U₀`: the statements use library notions only; the sketch adds the
  reset-output invariant, forwarding before the halt, and the startup and host space
  composition (step (iv)).
- Ruling for B6 `SU`: the ruler host is the required H5 block transport.

## Dependencies (at `1781a230`)

| Dependency | Needed by | Status |
|---|---|---|
| H2 promotion (H2-S; backlog F7-1(a)) | `U₀`'s and `SU`'s fills | private `h1Round_effect` (`CodeSimulator.lean:5657`) and `h1RoundRep` (`:5599`), statement unchanged at fills-8. H2-S round 1: 0 blockers / 3 majors / 5 minors; round 2 pending (finding 1's `t ≤ T`). `exists_rulerHostTM` is generic and does not need it |
| Record-table row 17, `exists_recordTemplateTM` (`RecordTable.lean:4335`) | row 18 | **proved** (fills-8, PR #84) |
| Record-table row 18, `exists_recordInitTM` (`RecordTable.lean:4610`) | `space_hierarchy`'s fill: the initial record | admitted (its `sorry` at `:4636`); statement unchanged; still needed |
| `exists_recordStepTM`, `exists_recordTestTM` (`CfgRecord.lean:4308`, `:4971`) | H3's loop | proved |
| `counterLoopTMVia` and its contracts (`CounterLoop.lean:614`, `:1220`, `:1306`, `:1500`) | Route B; the step clock's proof | proved |
| `universalCanonTM`, `universalCaptureTM`, `universalCanon_complete` (`UniversalStartup.lean:238`, `:405`, `:287`) | `U₀`'s startup | proved |
| `alphabet_reduction_spaceUsed`, `one_work_tape_binary_spaceUsed`, `of_spaceUsed_le` | the bridges | proved |
| MIG-0a `Turing.Contract` (`Build/Contract.lean`) | later phrasing (Q7) | landed (PR #83) |
| MIG-0b | later phrasing (Q7) | statement gate issued (`audits/mig0b-pack.md`) |
| C1 | consumer of the step clock | design pending user decisions (backlog C1-D) |

## Brief for the auditor

Restate every definition in your own words before reading its docstring. Argue each of the ten
sorried theorems true in two to five sentences, or exhibit a counterexample. Attempt at least six
adversarial instantiations (failure modes 1–4 of `audits/TEMPLATE.md`). They must include:
- **empty input** (`y = []`, `x = []`, `z` a pure header);
- **a halt on the last permitted transition** (one round fewer than the surplus);
- **clock exhaustion**: a timeout at `τ = d`, `d = 0`, `w = []`, and a body already at a stop
  state at time `0`;
- **`k = 0` tapes** and **`ℓ = 1`**.

Points to rule on:

1. **The step clock.**
   - Is the frame clause true for the fused decrement-and-step design (the input head and output
     at intermediate times included)?
   - Are `5τ + 2|w| + 2` and `5d + 2|w| + 2` attainable? The note §5 calls this an inferred plan,
     and suggests allowing `+ 3` if a dispatch step is needed. Should the gate allow it now?
   - Are the edge cases right: `w = []` (value `0`), `τ = 0`, a halting body transition landing
     directly on `finish none`?
   - Is the exact endpoint (`wordPatch`, the head back at `cp`) right at a timeout?
2. **The loop and the step-clocked runner.**
   - Does the loop's every-`N` clause, with "stationary stop states" and an all-times envelope,
     follow from the two record rows as sketched?
   - Is the runner's certification threshold `C · N · (L + |x| + 1) ≤ d` consistent with the
     loop's time bound?
   - Is the `+ 3` dispatch right?
3. **The configuration-count runner.**
   - Is `N ≤ configBound M |x| s + 1` the right surplus (check 4)?
   - Is the time bound `C · 2^(C · (L + 1))` reachable by both routes, with `C` depending on `M`
     and `upd` only?
   - Do the routes' clock widths (A: `c_M · L`; B: `|Q| + posWidth |x| + 3k(2s + 1) + 1`) work,
     the case `|x| > L` included?
4. **The ruler host against H2-S finding 2.** Are the five clauses the block simulation the
   finding asks for? Is any clause missing? The physical input head between checkpoints is left
   unconstrained (P6). Are the cumulative bounds `t ≤ t' ≤ C(ℓ + 1)t` the right resource
   guarantees: space for `SU`, and time for a device consumer such as C1 or U-1?
5. **The ruler test and the call rows.** Check the empty payload, `p = |z| + 1`, and the clamped
   moves at both boundaries. Q9: should the call rows be gated now?
6. **`U₀`.**
   - The statement: forward only, `C · (s + 1)`.
   - The startup's endpoint against H2's seam relation (`h1RoundRep`, `CodeSimulator.lean:5599`;
     the H2 draft's `Rep`, `audits/evidence/h2/StepBlockDraft.lean.txt`).
   - Does the rewritten sketch carry finding 4's invariant correctly, through the halting round
     (forward, then halt)?
   - Is the stated dependency on H2-S round 2 the right one, given finding 1 and finding 4's
     remark that the silent iterate is not a theorem about the wrapper?
7. **`space_universal`, strengthened.**
   - Fidelity to [AB09, Exercise 4.1], p. 93 (`C · t`).
   - The ledger `ℓ = 2|bits s| + 2|α| + 4 ≤ (2|α| + 6) · s`, from `s ≥ 1` and `|bits s| ≤ s`.
   - The probe's derivation of the gated form.
   - The edits of `Hierarchy.lean`'s module docstring and of one sentence of
     `space_hierarchy`'s.
8. **The bridges**: are they the statements `space_hierarchy`'s fill needs? Note that
   `decidesInSpace_of_alphabetReduction` takes an all-inputs, all-times space hypothesis and no
   time bound.
9. **B3.** Is the public summary surface right (`summaryWord` as a public representative; a
   `Fin 3` code rather than a `Fintype OutSummary` instance)? Does the re-pointing preserve S1b's
   private proofs (the patched `ConfigGraph` elaborates)? Does it leave no copy?
10. **The note's open questions**, each with its recommendation (`B6-hosts-design.md` §10):
    - **Q1**: which clock the fill uses. Recommended: `exists_configWindowRunnerTM`
      clock-agnostic, Route A if the step clock is filled first, else Route B.
    - **Q6**: `∃` statements or named machines. B5 decides `∃` now. Rule on whether the `∃` rows
      serve their consumers until then, and on naming `U₀` by `Classical.choose` as `univTM` is
      (`TimeHierarchy/Diagonal.lean:110`).
    - **Q7**: `Contract` phrasing. Recommended: the existing style now, adapters after MIG-0b.
    - **Q8**: `U₀` generic in the scheme. Recommended: yes.
    - **Q9**: gate the ruler call rows with the host; fill them inside the host's fill.
    - **Q10**: no time clause on `U₀`.
    - **Q11**: `windowRun` is noncomputable; acceptable for a specification.
11. **The maintainer's further points:**
    - **P1.** The two home moves (`inWindow_of_spaceUsed_le`, `windowRun_summary_of_halts` to
      `WindowClock`).
    - **P2.** `exists_codeTM` keeps its statement, but its proof becomes two lines from
      `exists_codeTM_spaceUsed`. The alternative is a second copy of the relabelling
      construction, which `policy.md` §1 counts as duplication needing approval. The freeze
      allows this one body change.
    - **P3.** `CodeTM.one_le_spaceUsed` sits beside `exists_codeTM` rather than beside `CodeTM`,
      so that Part B is one insertion.
    - **P4.** `space_hierarchy`'s docstring changes in two places only:
      - one stale sentence ("the binary-position one, hence without its logarithmic addend"),
        now citing `Turing.exists_selfUniversal`;
      - its status label (the RD-3 gate passed).

      Its sketch is otherwise unchanged. Should it be re-pointed at the gated names
      (`exists_configWindowRunnerTM`, `windowRun_summary_of_halts`, the bridges) now, or at
      fill?
    - **P5.** `Hierarchy.lean` gains no imports; its docstrings cite names in modules it does
      not import yet.
    - **P6.** Should the ruler host bound the physical input head between checkpoints? It costs
      no space.
12. **Documentation and policy** (`policy.md`): module headers, statement prose, [AB09]
    locations, a literal `**Proof sketch.**` on every nontrivial theorem, and 100-character
    lines.
13. Report anything else that the files, this pack or the note misstate, in the table.

## Repository-side attestations (verify or challenge)

Source facts, which the bundle lets you check, are kept apart from the maintainer's execution
claims, which are in the logs.
- **Elaboration** (log `elaboration` §1): the unit, elaborated read-only against `oleans-f8`
  (Lean `v4.25.0`), gives exit 0, 0 errors, and exactly ten warnings, all
  `declaration uses 'sorry'`, one per contract (the log lists them).
- **Cut checks** (log `cutcheck` §3): nineteen check files, each 0 errors:
  - eleven, one per part, each in exactly its landing module's import closure, which the
    worktree's import graph computes, so appended parts are included where they will be visible;
  - eight, one per patched existing file, each elaborated **in full** in its patched closure:
    `CfgRecord`'s 5272 lines, `ConfigGraph` with its re-pointed privates, `Encoding` with the
    re-derived `exists_codeTM`, and both facades.

  The unit's imports are exactly the union of the parts' existing imports.
- **Patch replay** (log `cutcheck` §2): each of the eight patches applies with `patch -p1` to a
  scratch copy and reproduces its patched file byte for byte.
- **Freeze** (log `freeze`): in the six library files, no public declaration is removed and no
  public statement changes, except `Complexity.space_universal` (B1). Also:
  - one public body changes, `Turing.exists_codeTM` (P2);
  - under B3, seven privates are removed, three private bodies are re-pointed, and one private
    statement (`s1b_record_accepts`) is re-pointed;
  - docstrings change on `exists_codeTM`, `space_universal`, `space_hierarchy` and the three
    re-pointed privates;
  - all else is byte-identical (comment-stripped).

  A positive control (`Hierarchy.lean` without its allowance) fails, as it must.
- **Axioms** (log `axioms`): separate probe copies, never landing material.
  - All 54 declarations of the unit were printed. Forty-three show a subset of `[propext,
    Classical.choice, Quot.sound]`.
  - `sorryAx` appears exactly in the ten contracts and in `exists_stepClockTM`, which is derived
    from one of them.
  - The re-derived `exists_codeTM` and the public `ConfigGraph` theorems above the re-pointed
    privates show the standard three.
- **Semantic probes** (log `elaboration` §2): 26 `example`s and four helpers over the unit:
  - the input cell, the empty payload included;
  - the boundary test at `z = [true]`;
  - the header layout for a one-bit budget word and empty code and payload;
  - the summary code on `[]`, `[true]`, `[true, true]`, `[false]`, and the tag update;
  - the windowed run of a no-tape machine that halts on its first transition emitting `true`:
    exhausted after one round, `halted` with tag `1` after two;
  - the ruler host's two consumer directions.

  Four negative controls, each a probe made false, fail: three by `decide`, and `neg4` (the
  surplus round removed) by its proof.
- **The gated form** (log `elaboration` §3): the worktree's gated `space_universal`, extracted
  verbatim and renamed, is proved from the strengthened statement in the patched closure.
- **The draft's step clock** (log `elaboration` §3): the draft's `exists_stepClockTMVia`,
  extracted verbatim and renamed, is proved from the landing form's.
- **Names** (log `names` §1): 54 declarations; no full-name clash with the worktree's 13,984
  declaration names, apart from the intended replacement of `Complexity.space_universal`. No new
  name shares a last component with a declaration directly in `Turing` or `Complexity`, where
  `open Turing` inside `namespace Complexity` could make it ambiguous. A positive control is
  caught.
- **Cited names** (log `names` §2): 156 backticked tokens of the unit and of the patches' added
  lines were `#check`ed. Those that do not resolve fall in these classes:
  - bound variables (`C`, `L`, `SU`, `U₀`, …);
  - module and file names;
  - `Complexity.space_hierarchy`, which is not in the unit's imports but is
    `Hierarchy.lean:262`;
  - the H2 draft's names, cited as H2-S dependencies;
  - the private `h1Round_effect`;
  - S1b's deleted privates, named by the part E header.
- **Style lint** (log `elaboration` §5): `scripts/campaign_style_lint.py` over the landing
  modules and the patched files: 0 FAIL, and 1 WARN, `CfgRecord.lean` at 5272 lines (5256
  before). File size alone is no reason to split (user rule).
- **Line widths** (log `elaboration` §4): no line over 100 characters, in the unit, the landing
  modules, the probes, or the patches' added lines.
- **Nothing in the worktree was changed.** All files were written to a scratch directory; no git
  command and no `lake` command was run; no olean was written. `lean` ran only through
  `tools/leanelab.sh`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is that of `audits/TEMPLATE.md`. Findings go verbatim into
`audits/b6-hosts-statements-findings.md`. The gate closes when a round reports zero blockers and
zero majors. The parts then land as cut, by PR, with the homes as ruled, and the H3, H5 and `U₀`
fills may be briefed.
