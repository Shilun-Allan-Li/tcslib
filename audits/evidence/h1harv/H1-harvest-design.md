# H1 hosted-clock harvest: design note (statement gate)

**Base.** The campaign tip **`e831b5b0`** (`e831b5b0` resolved by `git rev-parse` in every log),
a backlog-only commit whose Lean content is that of `6fbdefac` and `13a16a69`: the brief's base
`2c3c975a` plus **MIG-0b (PR #90, merged as `79c30a89`)** and PR #91 (proof sketches in
`Build/StepBlock.lean`, comments only). The tree is exported read-only (`git archive`) into the
gate's `base/tip/`; Lean runs only through `tools/leanelab.sh` against the olean snapshot
`oleans-lm0b`, which holds the post-MIG-0b round layer (content-checked, §7.1), with the packages of
`wt-h1harv`, whose `lake-manifest.json` and `lean-toolchain` equal the tip's (Lean `v4.25.0`).
Every `file:line` below is at the tip. The gate was first drafted and run at `2c3c975a` (with the
snapshot `oleans-lc1`; 40 checks, 0 failed) before #90 merged; that run's logs were lost when the
session stopped at about 16:22 UTC, and every check was re-run at the tip (§12).

**In one paragraph.** The C1 gate's ruling 5 (`audits/c1-hosts-statements-findings.md:184`)
requires the H1 hosted clock, eleven private declarations of `TuringMachine/CodeSimulator.lean`, to
be harvested into public contracts before the brief of the interpreter core `R`
(`Turing.exists_ndInterpreterCore`, `NDCodeSimulator.lean:128`): an arbitrary represented live start
with the stream already installed, the early-escape time bound, and live exits usable by the
caller. This note proposes a new public module `Build/StepBlockLoop.lean` with two machines and
three theorems in namespace `Turing.StepBlock`, generalizing the private ones in exactly those
three ways (and, at no cost, in the counter word, the boundary tag and the output prefix). **All
five are proved** in the unit, with the standard axioms only; the landing deletes eight private
declarations of `CodeSimulator` (no private copy is kept) and re-points the three that stay (the
one-bit verdict of the deterministic simulator). The full-file overlay elaborates with 0 errors
and only the tip's two headline `sorry` warnings; the private statements follow from the public
ones by `example`s in the overlay; a landing rehearsal of `CodeSimulator` elaborates likewise; and
two consumer probes derive the loop step of `R`'s sketch, the second at the replay machine of a
coded NDTM with the verdict and both of `R`'s time clauses.

---

## 1. What `R`'s sketch needs from the clock

`R`'s statement (`NDCodeSimulator.lean:128-145`): one machine for all codes, a stream tape `j`,
three states `entry`, `accept ≠ reject`; for every code a constant `C` such that, from `entry` on
`z = ⟨⟨bits t, α⟩, x⟩` with a stream `s` (`t ≤ |s|`) on tape `j` from cell 0, `R` reaches `accept`
iff the coded machine's branch `e` on `x` along `s.take t` has halted with output exactly
`[true]`, else `reject`, at a time `T` with no verdict earlier, `T ≤ C·(t + 1)`, and
`T ≤ C·(t' + |x| + |bits t| + 1)` whenever the branch along `s.take t'` has halted (`t' ≤ t`).

Its sketch (`NDCodeSimulator.lean:112-127`) and the C1 design note (`audits/evidence/c1/C1-design.md`
§2.2 rows U8, U9, U11, lines 219-222; §3.6, line 470) use the clock as follows.

| Need | From the sketch | Kind |
|---|---|---|
| N1. Simulate the **replay machine** `N.replayTM` (3 work tapes, states `Fin (n + 1)`) on the **copied window** `x.take t`, hosted by Z1 | "the deterministic clocked interpreter loop at three work tapes, the stream as the mirrored choice tape … hosted by Z1 … on the window" | hosted loop, `k = 3` |
| N2. Start from the replay machine's initial configuration **with the stream already on its choice tape**, `NDTM.withChoiceTape (N.initCfg (x.take t)) (bufferTape s) 0` (`ChoiceReplay.lean:68`) — not the replay machine's initial configuration, whose choice tape is blank | "from an arbitrary represented start" | **generalization (a)** |
| N3. The deadline counter is the parsed `bits t` | "leaving `bits t` on a counter tape" | counter word of value `t` |
| N4. Per-round cost a per-code constant, counter cost `4r + 2|bits t|` over `r` rounds (`counterOverhead_le_of_le`, `CounterLoop.lean:518`), escape **at that round's exact time** (`counterLoopTM_run_escape`, `:1455`) | "which gives the prefix clause" | **generalization (b)**: a bound in the halting time `t'`, not the deadline `t` |
| N5. Read the output summary at the exits into `R`'s own verdict states | "The verdict reads H2's output summary into the live exits" | **generalization (c)**: live exits, endpoint, cut, summary cell |
| N6. No verdict earlier | `R`'s `∀ u < T` clause | the exit cut for every boundary tag |
| N7. Identify the simulated run with the branch on `x` | `replayTM_runFrom` (`ChoiceReplay.lean:80`), `runWith_initCfg_take` (`Nondeterministic.lean:583`) | `R`'s own composition (probed, §4.4) |

## 2. What the private H1 clock provides today

The eleven declarations of `section StepBlockClients` after H2-M (`CodeSimulator.lean:2760-3185`),
over the public step block (`Build/StepBlock.lean`), the counter loop (`Build/CounterLoop.lean`) and
the virtual-input host (`Build/VirtualInput.lean`):

| Declaration | `CodeSimulator.lean` | Statement, in words | Against `R`'s needs |
|---|---|---|---|
| `h1ClockTM k` | `:2806` | `counterLoopTM (roundTM k) (exit k true) (some (exit k false))`, type inferred | the machine (N1) |
| `h1HostedClockTM k` | `:2811` | `vhostEmitTM (h1ClockTM k)` | the hosted machine (N1) |
| `h1RoundTime d` | `:2815` | first positive time the block is at an exit (`Nat.find`), else `0` | proof index |
| `h1RoundTime_spec` | `:2827` | at a **live** represented entry `c` (already arbitrary): positive, `≤ 50·(|table| + 1)`, endpoint at `exit k (M.step c).state.isSome` representing `M.step c`, silent, cut | general already |
| `h1Clock_orbit` | `:2871` | the block's orbit represents `M`'s run **from `M.initCfg x`**; its successor step unfolds the orbit (`simp only [counterLoopOrbit, roundOrbit, …]`, `:2892`, the token `roundOrbit` added by MIG-0b) | (a) missing |
| `h1Clock_round` | `:2898` | round hypotheses of the counter loop, **from `M.initCfg x`** | (a) missing |
| `h1Clock_effect` | `:2931` | from `M.initCfg x` and the counter `bufferTape (bits t)` at `0`: some `T ≤ t·B + 4t + 2|bits t| + 2` with the loop at `done`/`escape` (as `M` is live/halted after `t` steps), the endpoint representing `M`'s `t`-th configuration, output kept, no exit earlier | (a) missing; (b) missing: the proof's halting branch has the exact time `Σ_{j<u} τ_j + counterOverhead (bits t) u` (lines 2969-2971) but the statement keeps only the full budget |
| `h1HostedClock_effect` | `:3035` | the same hosted by Z1, initial tag `true`, prefix `[]`, any native input and frozen head: live exits `(done, b)`/`(escape, b)`, valid arrival tag, cut for every tag | (c) present but private; tag and prefix fixed |
| `h1HostedVerdictTM k` | `:3083` | the hosted clock with both exits replaced by one halting emission of the verdict bit | B5a's need, not `R`'s (`R` needs live exits, distinct verdict states) |
| `h1HostedVerdict_effect` | `:3101` | the verdict machine halts within `… + 3` with output `d.output ++ [summaryClock …]` | B5a |
| `h1HostedVerdict_accepts` | `:3166` | that bit is bounded acceptance of the decoded `MachineFormat` machine | B5a |

The semantic clock `summaryClock` and its three lemmas (`:2768-2801`) sit in the same section; they
are B5a's specification, used only by the verdict.

## 3. The generalizations

* **(a) Any represented live start.** Replace `M.initCfg x` by an arbitrary configuration `c` with
  `c.state ≠ none`, represented (`Rep M.tr c d`) by a block configuration `d` at the entry. Liveness
  is needed: the block's contract `roundTM_effect` (`StepBlock.lean:3116`) assumes `c.state = some
  q`, and with a halted `c` the represented state word is empty and the block's behaviour is
  unspecified. The orbit invariant's base case is the only place the private proof used
  `initCfg`'s liveness.
* **(b) The early-escape bound.** `∀ t' ≤ t, (M.runFrom c t').state = none →
  T ≤ t'·B + 4t' + 2|w|`, with `B = 50·(|tableBitsK M.tr| + 1)`. It follows from the exact escape
  time: if `u ≤ t'` is the first halting time, `T = Σ_{j<u} τ_j + counterOverhead w u ≤ u·B + 4u +
  2|w|`. There is no `+ 2`: the final underflow sweep does not happen on escape.
* **(c) Live exits usable by the caller.** Public machines and contracts whose endpoint is the live
  control `(done, b')`/`(escape, b')` (not the halting verdict), with the exact transported
  endpoint configuration, the cut at both exits for every tag, the counter frame (the counter tape
  changes only on `[cp, cp + |w|)`, its head back at `cp`), and a reading lemma for the cell under
  the summary head. A caller redirects the two exits (by `seamCompTM` or a phase host) and reads
  its verdict there in one step, as `h1HostedVerdictTM` does.
* **Free generalizations**, because the counter loop's and Z1's own contracts are already general:
  any delimited counter word `w` of value `t` (padding allowed) on any counter tape `ct` at any
  head `cp`; any boundary tag `b` valid at the start's input position; any prior output `pre`.

## 4. The proposed public statements

Home: new module `TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean`, namespace
`Turing.StepBlock` (unit `H1Harvest.lean`, Part A; line numbers in the unit).

| Name | Unit line | Meaning |
|---|---|---|
| `Turing.StepBlock.loopTM (k : ℕ) : MultiTapeTM (k + 2 + 1) Bool (CounterLoopState (Σ key, Ph k key))` | `:133` | the counter loop over the step block (= `h1ClockTM`, now with its type explicit) |
| `Turing.StepBlock.hostedLoopTM (k : ℕ) : MultiTapeTM (1 + (k + 2 + 1)) Bool (CounterLoopState (Σ key, Ph k key) × Bool)` | `:141` | Z1 over the loop (= `h1HostedClockTM`) |
| `Turing.StepBlock.loopTM_run` | `:330` | from any live `c` represented by `d` at the entry, a counter word `w` of value `t` at `cp`: `∃ T e ct'`, the full bound, the early-escape bound, `Rep M.tr (M.runFrom c t) e`, `e.output = d.output`, the counter frame, the run equation to `counterLoopCfg (some (done or escape)) e ct' cp`, the cut |
| `Turing.StepBlock.hostedLoopTM_run` | `:458` | the same hosted by Z1 over any native input `z`, head `p`, tag `b` with `VirtualTag c.inputPos b`, prefix `pre`: `∃ T e ct' b'`, the same clauses plus `VirtualTag e.inputPos b'`, the run equation to `vhostCfg (counterLoopCfg (some (done or escape)) e ct' cp) b' p pre`, the cut for every tag |
| `Turing.StepBlock.hostedLoop_read` | `:522` | at `vhostCfg (counterLoopCfg (some q) e ct cp) b p pre` with `Rep tr c' e`: control `some (q, b)`, native head `p`, output `pre ++ e.output`, and the cell under `vhostBank (summaryTape k).castSucc` is `outputSummary c'.output` |

Private helpers, moved with the harvest: `loopRoundTime` (= `h1RoundTime`, body unchanged),
`loopOrbit_succ` (new: the core's `Turing.roundOrbit_succ`, `Build/Contract/Basic.lean:713`, read
through the abbreviation `counterLoopOrbit`), `loopRoundTime_spec` (= `h1RoundTime_spec`,
statement unchanged; its uniqueness step now cites `roundTM_firstExit_unique`,
`StepBlock.lean:3457`), `loopOrbit_rep` (= `h1Clock_orbit` from `c`), `loopOrbit_round`
(= `h1Clock_round` from `c`). `scripts/decls.py movemap` checks the defs' bodies identical after
renaming, the spec's statement identical after renaming, and the two orbit lemmas equal to the
private ones at `c := M.initCfg x`.

**Not stated** (deliberately): the exact time (it is the round index's sum plus
`counterOverhead`, and no round-time function is public before the round adapter of the H2 design's
O7, now possible on MIG-0b's round layer but not yet built); the head trajectories and envelopes
(`counterLoopTM_run_done`/`_escape` state them for the body heads; a sibling theorem can add them
when a space consumer needs the clocked loop); the counter's final content inside `[cp, cp + |w|)`
(all `true` after underflow, `counterWord w u` after an escape; existential here).

### 4.1 Proofs

All five are proved (no `sorry` in the unit; axioms `propext`, `Classical.choice`, `Quot.sound`).
`loopTM_run` is `h1Clock_effect`'s proof run from `c`, with the counter general and the
early-escape clause from the escape branch's exact time (`counterOverhead_le_of_le` at `u ≤ t`);
`hostedLoopTM_run` is `h1HostedClock_effect`'s proof with the tag and the prefix general;
`hostedLoop_read` is the reading step of `h1HostedVerdict_effect`'s proof, over `counter_cfg_eq`
(`CounterLoop.lean:691`) instead of `embedEmitCfg_selected_tape`.

### 4.2 The corollary direction (overlay §C)

Each private H1 declaration that the landing deletes is recovered in the overlay, its statement
copied verbatim from the tip by `scripts/mkoverlay.py` (the copy is checked in the log):
`h1ClockTM k = loopTM k` and `h1HostedClockTM k = hostedLoopTM k` by `rfl`; `h1RoundTime d =
loopRoundTime d` by `rfl`; `h1RoundTime_spec`, `h1Clock_orbit`, `h1Clock_round` from the moved
private forms (their statements name the round index, so they follow from the moved helpers, not
from the public contracts); `h1Clock_effect` and `h1HostedClock_effect` from `loopTM_run` and
`hostedLoopTM_run` at `c = M.initCfg x`, `w = bits t` at `0`, tag `true`, prefix `[]`.

### 4.3 Sanity (overlay §S)

S0: for every configuration of every table there is a represented entry (non-vacuity of `Rep`
with `entry`). S1: a counter of value `0` (`[]` or the padded `[false, false]`) runs no round and
reaches `done` within `2|w| + 2`, its body part representing the start. S2: a start whose first
transition halts escapes within `B + 4 + 2|w|` for **every** deadline `t ≥ 1`. S3: the
initial-configuration start recovers today's statements (§C, C6 and C7). S4: at deadline `1`, the
hosted loop is at a live state `(q, b')`, `q = escape` iff the first transition halts, and the
summary cell holds `outputSummary (M.step c).output`. S5: a concrete one-state, zero-tape machine
emitting `true` and halting, with the counter `[true, false, true]` (deadline 5): escape, verdict
cell `some true`, within `B + 10`.

### 4.4 The consumer probes

* `probes/ConsumerProbe.lean` (the overlay with `scripts/consumer_tail.lean` appended): for any
  table, one constant `C = B + 6` such that, from any live represented start over the counter
  `bits t`, the hosted loop reaches a live exit, at no exit earlier, with the verdict
  `(q = escape ∧ cell = some true) ↔ (M's run from c has halted by t with output [true])`,
  `T ≤ C·(t + 1)` and `T ≤ C·(t' + |bits t| + 1)` when halted by `t' ≤ t`.
* `probes/ReplayProbe.lean` (Part A alone, plus `ChoiceReplay`): the same at `M := N.replayTM`
  for a two-tape NDTM `N`, from `withChoiceTape (N.initCfg (x.take t)) (bufferTape s) 0`, with
  the verdict stated on `N`'s branch **on `x`** along `s.take t` and the prefix clause in exactly
  `R`'s form `T ≤ C·(t' + |x| + |bits t| + 1)` (through `replayTM_runFrom` and
  `runWith_initCfg_take`). Its only local lemma is the counter value of `bits t` (§11, Q6).

## 5. Home and layering

`R`'s module `NDCodeSimulator` imports `CodeSimulator`, so either home is visible to `R`. The
choice is decided by layering and by the other consumers.

| Option | Consequence |
|---|---|
| **New `Build/StepBlockLoop.lean`** (proposed) | Imports exactly the three hosts it composes: `Build/StepBlock`, `Build/CounterLoop`, `Build/VirtualInput`. Its forward closure at the tip does not contain `CodeSimulator` (MEASURED, `closure.py`; module count in the log); the graph with the landing edges is acyclic. `CodeSimulator` and the `TuringMachine` facade import it. A consumer (U-1, EXPCOM) imports the loop without the canonizer and `CodeSimulator`'s two sorried headlines. Ownership of the new module is disjoint from B5a's region of `CodeSimulator`. |
| In place in `CodeSimulator`, public in `Turing.StepBlock` | No new module, but every consumer imports a 3,290-line maintainer-owned file with two admitted headlines, contrary to the layering rule (`policy.md` §1: definition files apart from heavyweight theorem files) and to "a host … placed in the shared construction layer" (`policy.md` §1, *Hosts come first*). The private round index would sit beside the B5a canonizer. |
| Appended to `Build/StepBlock` | `StepBlock` would gain `CounterLoop` (and through it, since MIG-0b, `Build/Contract/Basic`) and `VirtualInput` (and `Simulation`, `Embed`), so every unclocked consumer of the bare block (B6's `U₀` in PR #92's `SelfUniversal`, U-1) pays for the clock; the H2 promotion deliberately kept `StepBlock`'s closure free of them (`H2-design-r2.md` §4.1; checked again here). |

**Decision (proposed): the new module.** Size is not a driver either way (user rule); the new
module is about 500 lines.

**Replay set at landing** (MEASURED, `closure.py`, header imports; the root `TCSlib.lean` is never
listed): `Build/StepBlockLoop`, `CodeSimulator`, `Codes2Tape`, `NDCodeSimulator`,
`Diagonalization/EXPCOM`, `Diagonalization/Relativization`, and the `TuringMachine` and
`Diagonalization` facades: **8 modules** at the tip; on PR #92's tree `SelfUniversal` (which
imports `CodeSimulator`) joins (§8).

## 6. The landing form

One maintainer PR (`CodeSimulator.lean` is maintainer-owned):

1. **New module** `Build/StepBlockLoop.lean`, the unit's Part A verbatim with the copyright block,
   its three imports and the standard options (`landed/TCSlib/…/Build/StepBlockLoop.lean`).
2. **`CodeSimulator.lean`** (`landed/TCSlib/…/CodeSimulator.lean`, diff
   `PostHarvest-CodeSimulator.diff`, generated by `scripts/mkposth.py` from the tip's file, every
   edit asserted):
   * the import of `Build.StepBlockLoop` after `Build.StepBlock`;
   * **deleted, by name, with their docstrings** (269 lines): `h1ClockTM`, `h1HostedClockTM`,
     `h1RoundTime`, `h1RoundTime_spec`, `h1Clock_orbit` (with MIG-0b's `roundOrbit` token),
     `h1Clock_round`, `h1Clock_effect`, `h1HostedClock_effect`. **No private copy is kept.**
   * **re-pointed**: `h1HostedVerdictTM` is `{ hostedLoopTM k with … }` (its code is the tip's
     after renaming `hostedLoopTM` back to `h1HostedClockTM`, checked); `h1HostedVerdict_effect`'s
     proof cites `hostedLoopTM_run` at `c = M.initCfg x` and `hostedLoop_read` (its own reading
     steps, 34 lines, become 14); `h1HostedVerdict_accepts` is unchanged.
   * **status text** (comments only): the module's status bullet names the public loop;
     `h1HostedVerdictTM`'s docstring names `StepBlock.hostedLoopTM`; the headline's H1
     continuation-2 appendix uses the new names; a new paragraph "**H1 harvest.**" gives the rename
     map, as the H2-M paragraph does.
   * **Freeze** (`decls.py freeze`): 105 → 97 declarations; exactly the eight private ones removed;
     nothing added; no statement or visibility changed; code changed only in
     `h1HostedVerdictTM` and `h1HostedVerdict_effect`; docstrings only in `h1HostedVerdictTM` and
     `exists_uniformSimulator`; outside declarations only the import and the status bullet. Both
     headlines (`exists_polyCanonizer`, `exists_uniformSimulator`) keep their statements and
     admissions.
3. **Facade** `TCSlib/Complexity/TuringMachine.lean`: `import TCSlib.Complexity.TuringMachine.Build.StepBlockLoop`
   after `Build.StepBlock`, and a `## Contents` line: "`Build/StepBlockLoop` — the step block's
   counter loop (host H2's loop form, `machine-library-design.md` §14): the binary deadline clock
   over the step block, native and on a buffered input, from any represented live start, with its
   early-escape bound and live exits." (PR #92 edits the same facade; §8.)
4. **Records and synchronized sketches**: the registry row (§9); `NDCodeSimulator.lean`'s `R`
   sketch (`:117-120`) re-points "H1's hosted clock … (private in `CodeSimulator` since fills-8;
   harvested with H2's promotion …)" to `Turing.StepBlock.hostedLoopTM_run` (comment only; the
   file is in the replay set; `policy.md` §3, synchronization); backlog C1-D's "Next" line.
5. **Replay**: the 8 modules of §5 (plus `SelfUniversal` if PR #92 has landed).

**Private → public promotions** (the only statement changes the landing makes; `decls.py movemap`):
`h1ClockTM` → `StepBlock.loopTM` (body identical after renaming; type now explicit),
`h1HostedClockTM` → `StepBlock.hostedLoopTM` (likewise), `h1Clock_effect` →
`StepBlock.loopTM_run` (generalized), `h1HostedClock_effect` → `StepBlock.hostedLoopTM_run`
(generalized). New public: `StepBlock.hostedLoop_read`. Moved and staying private: the round
index, its specification (statement unchanged) and the two orbit lemmas (generalized to `c`).

The rehearsal `probes/PostHarvest-CodeSimulator.lean` (the tip's header, Part A, then the landed
`CodeSimulator` body, in one file) elaborates with 0 errors and the two headline sorries. Being one
file it cannot test cross-module privacy; `decls.py refs` does: the landed `CodeSimulator` names
none of the deleted declarations or the module's private helpers in code, and names the deleted
ones in comments only in the harvest paragraph; no other TCSlib file names them at all.

## 7. MIG-0b (PR #90, merged as `79c30a89`)

The brief anticipated #90 as pending; it landed while the gate was drafted. It turned
`counterLoopOrbit` (`CounterLoop.lean:651`) into `abbrev counterLoopOrbit … := roundOrbit …`, with
`def roundOrbit … := (fun c => M.runFrom c (τ c))^[r] c` and `roundOrbit_succ` in
`Build/Contract/Basic` (`:708`, `:713`), and edited `h1Clock_orbit`'s unfolding step
(`CodeSimulator.lean:2892`) by adding `roundOrbit` (one of its four consumer edits;
`audits/evidence/mig0b/r2/NOTES-r2.md` §6).

* **The statements never depended on it.** No public statement of the unit mentions
  `counterLoopOrbit`, `roundOrbit` or a round-time function; they use `counterLoopTM`,
  `counterLoopCfg`, `vhostEmitTM`, `vhostCfg`, `Rep`, `exit`, `tableBitsK`, `FinTM.bufferTape`,
  `FinTM.VirtualTag`, `outputSummary`, none of which #90 changed.
* **No copied proof unfolds the orbit.** `h1Clock_orbit`'s `simp only [counterLoopOrbit,
  roundOrbit, Function.iterate_succ_apply']` is replaced in `loopOrbit_rep` by
  `rw [loopOrbit_succ, …]`, and `loopOrbit_succ` is the term `roundOrbit_succ (roundTM k)
  loopRoundTime d r`, accepted through the abbreviation. Nothing in the harvest needs #90's kind of
  edit again. (Before #90 merged, the unit proved `loopOrbit_succ` by
  `Function.iterate_succ_apply' _ _ _`, which elaborated against the pre-#90 definition at
  `2c3c975a`; at the tip it cites the core lemma instead, the dedup MIG-0b makes possible.)
* **Order.** #90 is in the base, so the harvest deletes `h1Clock_orbit` together with #90's edit.

### 7.1 The snapshot

No snapshot was supplied with the new tip. `oleans-lm0b` is a copy of `oleans-lc1` with the
modules downstream of #90's files rebuilt (last write 15:30 UTC, before #91 merged at 15:33 UTC:
its `StepBlock.olean` was built from the pre-#91 source, which differs from the tip's in comments
only). Its content is checked in the log's §0: the tip's `CodeSimulator.lean` elaborates against it
with exactly its two headline sorries, and against the pre-#90 `oleans-lc1` it does not (its
`roundOrbit` is unknown); `2c3c975a`'s `CodeSimulator.lean` fails against it exactly at the unedited
`h1Clock_orbit` (#90's known negative); the tip's `Build/StepBlock.lean` (with #91's sketches)
elaborates against it; and it prints `counterLoopOrbit` as the reducible abbreviation of
`roundOrbit`. Against `oleans-lc1` (`scripts/snapdiff.py`): exactly 23 oleans differ, the 16
modules #90 changed or added and 7 downstream ones (`Nondeterministic`, `ChoiceReplay`, `Oracle`,
`Build/OracleSim`, `ClassNP/Nondeterminism`, `ClassPSPACE/TQBF`, `SpaceComplexity/Inclusions`);
none differs outside #90's reverse closure, and the other 285 oleans of that closure are
byte-identical, as a deterministic rebuild leaves a module whose elaborated content did not
change. That the snapshot is a complete rebuild is therefore INFERRED, not attested by its
builder; the content checks above are MEASURED.

## 8. Sequencing with the open PRs #92 and #93

Read as text only (`lean/b6-hosts` `6158e48f`, `lean/arm-minor-fixes` `3fe6a2de`, both based on the
tip; file lists in the log's §8).

* **PR #92 (B6 hosts).** It changes `StateRenaming`, `Encoding`, `Build/CfgRecord`, the
  `TuringMachine` and `SpaceComplexity` facades and three `SpaceComplexity` modules, and adds
  `Build/StepClock`, `Build/WindowRun`, `Build/InputDevice`, `SelfUniversal`, and
  `SpaceComplexity/WindowClock`. Overlaps with the harvest:
  - **the `TuringMachine` facade**: both PRs add import lines next to `Build.StepBlock` and
    `## Contents` bullets; textual neighbours, so the second to land rebases its two hunks;
  - **`Encoding` and `StateRenaming` are in the new module's forward closure**: whichever lands
    second re-elaborates `Build/StepBlockLoop` and `CodeSimulator` on the merged tree (#92's replay
    already contains `CodeSimulator` and its downstream);
  - **`SelfUniversal` imports `CodeSimulator`**, so it joins the harvest's replay set if #92 lands
    first (measured on #92's tree in the log's §7); it cites the unclocked block
    (`roundTM_effect`, `roundTM_iterate`), not the clock, so it is not a consumer of the harvest;
  - **citations**: the probes cite `Encoding`'s `length_bits_le_self` and `unaryFin`; #92's diff
    of `Encoding` touches neither (it moves a `CodeTM` normalization proof);
  - **names**: #92 adds `Turing.clockCfg`, `Turing.exists_stepClockTMVia`, `Turing.exists_stepClockTM`
    (host H3's step clock); the name screen against #92's tree finds no clash.
  *Either order works; recommended: land #92 first (it is open and replaying-ready), then the
  harvest on the merged base with `SelfUniversal` added to its replay.*
* **PR #93 (ARM comments and imports, 33 files in `ClassPSPACE` and `SpaceComplexity`).** No
  overlap: none of its files is edited by the harvest, lies in the new module's closure, or is in
  the replay set. Independent.
* **MIG-1** (statement gate closed at round 2, not landed) will edit modules of the new module's
  closure (`Simulation`, `Composition`, `Encoding`, …); its landing replays the harvest's module.

## 9. H2's open items (they do not disappear with this gate)

| Item | Status after the harvest |
|---|---|
| O7, the round-time function (`H2-design-r2.md:572`) | Still private (moved as `loopRoundTime`); its specification now takes its uniqueness step from `roundTM_firstExit_unique` instead of re-proving it (the disclosed dozen-line duplication is paid). MIG-0b's round layer is now landed, so the public replacement (the adapter `roundTM_round : RoundContract …` with `time` the first positive exit) can be built; it is not part of this gate. |
| O4, three summary encodings | Unchanged; `hostedLoop_read` exposes the step block's `outputSummary`, one member of the family. |
| O8, U-1's frozen constant | Unchanged, unresolved. |
| O9, the run head bound's home | Unchanged. |
| O12, F7-1(c), the fixed-field walk | Unchanged; open. |
| CO-RF, the reset/forward wrapper (recorded on `U₀` and U-1) | Unchanged. The harvested loop keeps the block silent (the summary cell, not the output, records the emission), so it needs no CO-RF. |
| R2-1, fidelity-script false passes | This gate's acceptance checks are the elaborator's axiom prints (no `sorryAx`), an `axiom`/`sorry` census of every file, and a declaration inventory by name (`decls.py`); no fidelity script is relied on. |
| R2-8, `RoundContract` envelopes cover work heads only | Unchanged; no envelope is stated here. |
| H2-M's docs-only follow-up (eleven moved private lemmas without a sketch) | **Done** by PR #91 (in the base). |

## 10. Registry (`machine-library-design.md` §14)

The registry's H1 is the AND/OR evaluator; the private `h1…` names come from brief B5a-H1
(`briefs/b5a-fill-h1*.md`), not from the registry, which is why the harvest renames them. The
clock is **H2's loop form** (the records' name since the C1 design note, §2.2 U8) and belongs with
H2. Proposed row, directly after H2:

| # | Host | Status | Named consumers |
|---|---|---|---|
| H2-L | **H2's loop form, the clocked interpreter loop**: the binary counter loop over the step block, native (`Turing.StepBlock.loopTM`) and on a buffered input by Z1 (`Turing.StepBlock.hostedLoopTM`); from any represented live start, any delimited counter of value `t`; time `≤ t·B + 4t + 2\|w\| + 2`, and `≤ t'·B + 4t' + 2\|w\|` when the simulated run halts by `t'`; live exits `done`/`escape` with the exact endpoint, the cut, and the verdict cell (`hostedLoop_read`) | **harvested (gate `audits/h1-harvest-statements-findings.md`)** from B5a H1's private hosted clock (fills-8); all contracts proved; `Build/StepBlockLoop.lean` | B5a H1 (`exists_uniformSimulator`, through `h1HostedVerdict*`); C1's `R` (`exists_ndInterpreterCore`); U-1 (the timed universal, if it uses the deadline clock); EXPCOM (through B5a) |

## 11. Duplication ledger and open questions

**Ledger.** No proved material is copied. The private assembly **moves** (eight declarations
deleted from `CodeSimulator`, their generalizations added to the new module). Three small overlaps
are retired: `h1HostedVerdict_effect`'s own summary-reading steps (now `hostedLoop_read`),
`h1RoundTime_spec`'s uniqueness step (now `roundTM_firstExit_unique`), and the orbit's successor
step (now `roundOrbit_succ`). The evidence files (overlay, probes, rehearsal) repeat the unit and
the tip's `CodeSimulator.lean` as evidence, not as production copies. The replay probe's local
value lemma for `bits t` (12 lines) is evidence only; see Q6.

**Open questions for the user** (recommendations in italics):

1. **Home.** *`Build/StepBlockLoop.lean`, namespace `Turing.StepBlock` (§5).*
2. **Registry row.** *A sub-row H2-L of H2 (§10), not a new number: it is H2's loop form, shares
   H2's consumers, and a new number would invite confusion with the brief name "H1".*
3. **Names.** *`loopTM`, `hostedLoopTM`, `loopTM_run`, `hostedLoopTM_run`, `hostedLoop_read`.*
   "Clock" names were avoided: `Complexity.TimeHierarchy.clockTM` (Hydroxyi's fused runner) and
   host H3's step clock (`Turing.exists_stepClockTMVia`, `Turing.clockCfg`, in PR #92's
   `Build/StepClock.lean`) already use the word; the name screen finds no clash and no short-name
   overlap for the chosen names.
4. **Order with PR #92.** *Either works; recommended #92 first, then the harvest on the merged base
   with `SelfUniversal` in its replay (§8).*
5. **Gate and fill at once.** The statements are proved, so the landing needs no fill brief. *Land
   as one maintainer PR (module, `CodeSimulator` edits, facade, records) with its replay, after this
   gate closes; `R`'s brief then cites the public names.*
6. **The counter value of `bits t`.** `R`'s fill (and B5a's verdict) need
   `Nat.ofDigits 2 ((bits t).map Bool.toNat) = t`, i.e. `counterValue t.bits = t`; the only proof in
   the tree goes through `CodeSimulator`'s private `canonBits_value` and the public
   `codeBitsNat_bits` (`CodeParser.lean:209`). The harvested statements take the value as a
   hypothesis, so nothing here depends on it. *Add a public `Turing.counterValue_bits` beside
   MIG-0b's `counterValue` (`CounterLoop.lean:1939`) with the harvest's landing (one lemma; the two
   `digits` steps in `CodeSimulator` then cite it), rather than letting `R`'s fill carry a private
   copy.*
7. **`R`'s sketch text.** *Re-point `NDCodeSimulator.lean:117-120` to the public names in the
   harvest PR (comment only): the file is in the replay set anyway, and a sketch should not name
   a private host that no longer exists.*

## 12. Evidence

| File (gate directory → repository) | Content |
|---|---|
| `H1Harvest.lean` → `audits/evidence/h1harv/H1Harvest.lean.txt` | the unit (Part A lands as the module) |
| `overlay/H1HarvestOverlay.lean` → `…/H1HarvestOverlay.lean.txt` | the overlay: the tip's `CodeSimulator.lean` byte for byte, Part A, §C, §S, §X |
| `probes/ConsumerProbe.lean` | the overlay + `scripts/consumer_tail.lean` (bundled as the tail) |
| `probes/ReplayProbe.lean` → `…/probes/ReplayProbe.lean.txt` | Part A + `ChoiceReplay` + `scripts/replay_tail.lean` |
| `probes/PostHarvest-CodeSimulator.lean`; `landed/…/CodeSimulator.lean`; `work/PostHarvest-CodeSimulator.diff` | the landing rehearsal; the landed file; its diff against the tip (bundled as the diff) |
| `landed/…/Build/StepBlockLoop.lean`; `cut/…check.lean` | the module as it lands; the cut check |
| `scripts/` | `mkoverlay.py`, `mkstandalone.py`, `mkposth.py`, `decls.py` (freeze, movemap, names, refs, inventory), `closure.py`, `admissions.py`, `banned.py`, `snapshot_probe.lean`, `runall.sh` (fails closed; exports the bases itself); `cutcheck.py`, `widths.py`, `lint.py` (= `scripts/campaign_style_lint.py` with its root as an argument), `cited.py` copied from the C1 gate |
| `logs/h1-harvest-statements-{elaboration,cutcheck,freeze,names,axioms}.log` → `audits/logs/…` | every check with its expected outcome; the last line of the elaboration log counts them |
