# External audit pack — C1 host contracts: the hosts of the nondeterministic time hierarchy (statement gate)

Campaign: the Arora-Barak chapters 3-4 plan, cluster C1 (`Diagonalization/NTimeHierarchy.lean`, [AB09,
Theorem 3.2] at linear overhead, decision CH34-Q8). The C1 design note
(`audits/evidence/c1/C1-design.md`) proposed a route and a set of host contracts; the user answered
its five questions on 2026-10-13 (below). **This gate audits the landing form of those host
contracts, and a docstring-only patch of `NTimeHierarchy.lean` that restates two (in fact three)
proof sketches under the decided route.** Every sorried theorem stands under a proof sketch;
definitions have their real bodies; eleven public theorems (one of them modulo `E`) and five private
helper lemmas are proved and machine-checked. Nothing is landed.

| File (bundle path) | Content |
|---|---|
| `audits/evidence/c1/gate/C1Hosts.lean.txt` (1012 lines, MEASURED) | **the unit**: six parts, each the body of one landing module or one addition to an existing module (table below); 27 declarations, 5 sorried |
| `audits/evidence/c1/gate/NTimeHierarchy-docstrings.patch` (230 lines, MEASURED) | **the docstring patch** of `TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`: the sketches of statements 1, 2 and 4(iii), a declared-deviation bullet, the decision-4 comment fix; no statement, proof or import changes |

Supporting evidence: `audits/logs/c1-hosts-statements-elaboration.log` (every check; §-numbers below
refer to it) with its companions `…-cutcheck.log`, `…-axioms.log`, `…-freeze.log`, `…-names.log`;
`audits/evidence/c1/gate/probes/C1HostsSanity.lean.txt` (the unit plus 12 sanity `example`s);
`audits/evidence/c1/gate/scripts/` (the cut check, verbatim from the stage-2 gate; the statement
comparison, the freeze check, the name screen, the patch writer, the landing-file writer, the probe
and axiom-probe builders, `runall.sh`, which regenerates every log).

**Bundle:** this pack first, then the standards (`audits/TEMPLATE.md`, `policy.md`, `workflow.md`),
the design records (`machine-library-design.md`, `backlog.md`, `AroraBarakChapters3-4Plan.md`), the
two files under audit, the probes, scripts and logs, the C1 design note and draft, the B6 host draft,
the stage-2 pack and its `NDSlice` file, the H2-S findings, the P3.3 gate records, and every library
file that the unit, the patch or this pack cites (`BUNDLE-FILES.txt` lists them in order).

**Provenance (maintainer).** A maintainer sub-agent wrote the files against the read-only checkout
`wt-g5c1`, moved during the work from campaign commit `385d6e5a` to `1781a230` (PR #84, fills-8), and
**every check reported here was re-run at `1781a230`** with the olean snapshot `oleans-f8` (Lean
`v4.25.0`). Between the two commits only `TuringMachine/CodeSimulator.lean` (new canonizer and H1
privates, notably H1's hosted clock and verdict) and `Build/RecordTable.lean` changed; every
`CodeSimulator.lean:line` below is at `1781a230`. The C1 design note and draft were written at an
earlier tip with `oleans-f7` (draft log: 0 errors, 5 sorries); their `CodeSimulator.lean` line numbers
are stale by up to about 1,190 lines (MEASURED: `h1RoundTM` moved from `:3979` to `:4809`).

## What the gate covers

1. **The nondeterministic contract variant at run level**: the agreement transfer along a state
   embedding, its deterministic-source form, the slice lemma (statement gated by stage 2, proof
   here), state relabelling, and the new input-locality lemma.
2. **The replay machine** (choice-tape determinization) and the replay lemma.
3. **The nondeterministic phase host** and **the choice writer** (bounded contract).
4. **The bounded input window copier** (new; user decision 5).
5. **The code layer for ND interpretation**: the serialization bridge, the per-code replay
   canonizer, and **the interpreter core `R`**.
6. **The exhaustive replay `E`** and the derivation `BF := E(UN)`.
7. **The restated sketches** of `NTimeHierarchy.lean` (statements 1, 2, 4(iii) and its chain
   arithmetic), the declared deviation, and the comment fix of user decision 4.
8. **Homes, module names and the landing obligations** they create.

Out of scope: proofs and fill routes beyond the sketches; the **step clock**
`Turing.exists_stepClockTMVia`, which is gated in the B6 hosts' pack (in preparation in parallel;
its draft is bundled) and only cited here; the H2 step block and its promotion (H2-S gate, round 1
open); MIG-0a's `Turing.Contract` (landed, PR #83) and MIG-0b; the six statements of
`NTimeHierarchy.lean`, which are frozen (the patch is checked to change no code).

## Decisions in force (verify that the files reflect them)

**User decisions of 2026-10-13, binding** (C1 design note §6):
1. **Guess first** for the universal NDTM `UN` and the diagonalizer `D`: it changes the sketch route
   of statements 1 and 4(iii), not their statements. SC-3 (design §12.7, the "nondeterministic
   lifting of the counter loop") closes with no nondeterministic loop host. Recorded as a declared
   sketch deviation, **audited here** (brief point 1).
2. **`BF := E(UN)`**, with `E = Turing.FinNDTM.exists_exhaustiveDecider` a public generic theorem.
3. **ND codes are interpreted through their replay machine** (option (c) of the design note §3.2):
   the H2 step block unchanged at `k = 3`, with a per-code primitive recursive re-serialization.
4. **One step clock, shared with B6** (`Turing.exists_stepClockTMVia`, cited); the "quadratic
   `clockTM`" record errors are corrected — the maintainer fixes the design and plan records; the
   comment-only fix of `NTimeHierarchy.lean`'s two docstring passages that attribute `C·(t+1)²` to
   `clockTM` (`:51-52`, `:110`) is in the patch.
5. **UN reads its input through a bounded window copy plus an input-locality lemma** (no new
   device); the in-place suffix device stays with U-1.

**Earlier rulings in force.** The P3.3 gate's round 2 (`audits/ch3-p33-r2-findings.md`, PASS) and
its resolutions (`audits/ch3-p33-resolutions.md`): the fixed-code schedule, the seeded ladder, the
capped locator, the allowance split, the prefix-bound obligation (`:37`), the amortized countdown.
The stage-2 pack (`audits/stage2-statements-pack.md`) gates `Turing.NDTM.runWith_eq_fixChoice_runFrom`;
design §15d records that one copy lands, in `Nondeterministic.lean`, with C1's proof under the gated
statement. The H2-S round-1 consumer ruling for C1 (`audits/h2-promotion-findings.md`, NF5 and the
consumer table): keep the choice installer, the nondeterministic host, branch alignment and the
amortized clock as separate obligations, and do not describe the table-only identity as equality of
complete serialized headers (mapped below).

## Dependencies

* **The B6 step clock** (`Turing.exists_stepClockTMVia`, proposed home
  `TCSlib/Complexity/TuringMachine/Build/StepClock.lean`; draft
  `audits/evidence/b6hosts/B6HostsDraft.lean.txt:732`). It is consumed by the fills of `E` and of
  `D` (the mid-rung, top-rung and locator caps), **not by any statement of this unit**, so nothing
  here elaborates against it. C1's draft statement `Turing.exists_stepClockTM` is the B6 draft's
  `Bool` corollary word for word (log §7: "IDENTICAL"); the draft's `Turing.clockCfg` is the `Bool`
  instance of B6's alphabet-generic one. Both leave this unit.
* **H2, the step block, and H1's hosted clock** (consumed by `R`'s fill only). The step block
  `h1RoundTM` / `h1Round_effect` (`CodeSimulator.lean:4809`, `:5657`) is under promotion (H2-S round
  1: 0 blockers, 3 majors; none refutes what C1 needs, and finding 2's requirement that an input
  device preserve C1's time bounds is met by the window route, which hosts a copied window by Z1's
  lockstep). Since fills-8, H1's **hosted clock and verdict** exist
  privately: `h1ClockTM` (`counterLoopTM` over `h1RoundTM k`, `:5755`), `h1HostedClockTM` (Z1-hosted,
  `:5760`), `h1Clock_effect` (`:5880`), `h1HostedClock_effect` (`:5984`), `h1HostedVerdict_effect`
  (`:6050`). This is the "H2 loop form" the design note §2.2 U8 asked for. `R` needs it **harvested**
  (policy §1: a private host is harvested before a second consumer is briefed) with two
  generalizations, both visible in its proof: (i) from the initial configuration (`h1RoundRep M.tr
  (M.initCfg x) d`, `:5880-5884`) to an arbitrary represented live start, because `R` starts the
  replay machine with the stream preloaded on its choice tape; (ii) the escape-time bound (`R`'s
  prefix clause): the halting case of `h1Clock_effect`'s proof has the exact time of
  `Turing.counterLoopTM_run_escape`, but the statement weakens it to the full-budget
  `t·50·(|table| + 1) + 4t + 2|bits t| + 2`. The live exits of `h1HostedClockTM` (not the halting
  verdict of `h1HostedVerdictTM`, `:6032`) are what `R` needs.
* **MIG-0a/0b**: not needed by these statements (run-level and existential rows). `Contract.toND`
  (design note §3.1) is deferred to MIG-0b, as proposed there.

## Homes and module names (proposed; the auditor rules on them)

| Part | Lands as | Namespace | Size at landing (MEASURED) |
|---|---|---|---|
| A | appended to `TCSlib/Complexity/TuringMachine/Nondeterministic.lean`, which gains `import TCSlib.Complexity.TuringMachine.StateRenaming` | `Turing.NDTM` | 265 → 581 lines |
| B | new `TCSlib/Complexity/TuringMachine/ChoiceReplay.lean` | `Turing.NDTM` | 137 |
| C | new `TCSlib/Complexity/TuringMachine/Build/NDHost.lean` | `Turing.NDTM`, `Turing` | 191 |
| D | new `TCSlib/Complexity/TuringMachine/Build/InputWindow.lean` | `Turing` | 77 |
| E | new `TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean` | `Turing` | 141 |
| F | new `TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean` | `Turing`, `Turing.FinNDTM` | 106 |

**Why one elaboration unit holds six parts**, and the cut: as in the stage-2 pack. Each part becomes
its module (copyright block, the `-- @imports` lines, standard options, the part verbatim); an
addition to an existing module is appended at its end with the extra imports. Each landing module's
import closure is elaborated on its own (the cut check, `cutcheck.log`); the four landing files whose
imports all exist in the snapshot are also elaborated standalone as they would land (`landed/`).

**Why these homes.**
- **Part A goes into `Nondeterministic.lean`**, next to what it generalizes
  (`Turing.MultiTapeTM.toNDTM_runWith`, `:251`), because design §15d places the slice lemma's one
  copy there and C1's proof of it goes through the transfer, which uses `Turing.Cfg.mapState`
  (`StateRenaming.lean:76`). Hence the new import; `StateRenaming` imports only `Deterministic`, so no
  cycle. Downstream (log §8): 32 modules have `Nondeterministic` in their closure, and only
  `NondeterministicSpace` and `ClassNP/NTIME` (besides `Nondeterministic`) gain `StateRenaming`; copies
  of both with the extra import elaborate with the same diagnostics as the originals. **The part is
  appended at the end**, not after `stepWith_eq_fixChoice_step` (`:163`) as the stage-2 pack said:
  C1's proof uses `toNDTM_runWith` (`:251`).
- **Part B is its own module** (`ChoiceReplay`): the replay machine is a construction, consumed by the
  code layer (E) and by `E` (F), and needs `FinTM.bufferTape` (`Simulation.lean:494`); keeping it out
  of `Nondeterministic.lean` keeps that file's imports minimal (layering).
- **Part C is a new Build module beside `Build/Seam.lean`**, not an addition to `Seam.lean`: `Seam`
  does not import `Nondeterministic`, is imported by most of `Build/`, and a new module keeps fill
  ownership disjoint. The phase host is a host (policy §1); the writer is an H5-family device.
- **Part D cannot sit beside the input copier in `Build/Scan.lean`**: its fill is a counter loop,
  and `Build/CounterLoop.lean` imports `Build/Scan.lean`. A new module importing `CounterLoop`.
- **Part E sits next to `CodeSimulator.lean`**, the deterministic uniform simulator, since `R` is an
  interpreter host over codes; it imports `NDCodes` and `CodeSimulator`, neither of which imports the
  other (design note §4 item 1). No `MachineFormat` instance and no change to `NDCodes`.
- **Part F is in `ClassNP/`**, because its statements use `Turing.FinNDTM.AcceptsWithin`
  (`ClassNP/NTIME.lean:93`) and no `TuringMachine/` module imports `ClassNP` (grep). `E` is the
  machine core of `NTIME(T) ⊆ DTIME(2^{O(T)})`, beside `ClassNP/Nondeterminism.lean`, whose private
  `choiceCore` replay it may retire (design note §3.5, INFERRED). The alternative, `E` in `Build/` with
  acceptance inlined, is open question 1. `BF := E(UN)` goes with `E` (it needs `NDCodes`, which
  `ClassNP` may import).

**Landing obligations** (outside the audited statements): the `TCSlib.Complexity.TuringMachine`
facade imports `ChoiceReplay`, `Build.NDHost`, `Build.InputWindow`, `NDCodeSimulator` with
`## Contents` lines, and `TCSlib.Complexity.ClassNP` imports `ExhaustiveReplay`; `Nondeterministic.lean`'s
module docstring lists the new definition (`relabelState`) and results; the stage-2 `NDSlice` Part A
lands as this copy (its sorried copy is superseded; Part B still lands in `NondeterministicSpace.lean`);
the design §14 host registry gains `phaseHostND` (host), the choice writer (H5 device), the window copier
(row), `R` (host) and `E` (host); design §12.7 closes SC-3 with a pointer to Part A/C; the docstring
patch lands with or after the five new modules, since it names them; a full downstream replay of the
32 modules above at landing.

## What the files state (verify)

**Part A** (`Turing.NDTM`; `C1Hosts.lean.txt:50-374`):
- `stepWith_mapState_of_agreeOn` (proved): if at every good state both transition functions of
  `host` are `src`'s renamed along `emb : S ↪ H`, then from a halted or good configuration one
  `host` step under either bit is the renamed `src` step.
- `runWith_mapState_of_agreeOn` (proved): the same along a whole word `w`, provided `src`'s run under
  every proper prefix of `w` is halted or at a good state.
- `runWith_mapState_of_agreeOn_det` (proved): the same with a deterministic source; every branch of
  length `|w|` is the renamed `src.runFrom c |w|`.
- `runWith_eq_fixChoice_runFrom` (proved; **statement gated by the stage-2 pack, verbatim**, log §7
  "identical 1"): if the slice `tm.fixChoice b`'s run from `cfg` is halted or at a state with
  `tm.tr false q = tm.tr true q` at each `j < |w|`, then `tm.runWith w cfg = (tm.fixChoice b).runFrom
  cfg |w|`.
- `relabelState` (def) and `relabelState_runWith` (proved): relabelling along `e : S ≃ S'`, and
  relabelled branches are renamed branches from any configuration.
- `runWith_initCfg_take` (proved, **new**, decision 5): for `|w| ≤ m`, the branch along `w` from the
  initial configuration on `x.take m` has the same state, work tapes, work heads and output as on `x`,
  and its input head is at the same position (as a natural number). Five private helpers.

**Part B** (`ChoiceReplay`): `replayTM N` (def): `k + 1` work tapes; reads the last (blank as
`false`), applies `N.tr` of that bit on the first `k`, moves the choice head `+1`, never writes it.
`withChoiceTape c ct cp` (def). `replayTM_runFrom` (proved): for `t ≤ |s|`, the replay's run for `t`
steps from `c` with `s` on the choice tape is `N.runWith (s.take t) c` with the choice tape, the
choice head at some `p ≤ t`, and `p = t` while that branch is live.

**Part C** (`Build/NDHost`): `phaseHostND M q0 red` (def): `phaseHostTM` over ND phases;
`phaseHostND_fixChoice` (`rfl`): each slice is `phaseHostTM` of the slices; `phaseHostND_run`
(proved): a phase's run with no earlier redirect is the host's along every prefix of the word, and
one more choice of either bit dispatches. `NDWriterState Q` (`run q | done`, `DecidableEq`);
`ndWriterTM k j q₀ δ stop bounded` (def); `ndWriterTM_run_block` (**sorried**): bounded flavor, trivial
controller, a nonblank block of `m` cells from the head of tape `j` then a blank: every word of length
`m + 1` reaches `done` with the block overwritten by its first `m` bits and the head at `pos + m`, every
other field unchanged; no shorter word reaches `done`.

**Part D** (`Build/InputWindow`): `exists_inputWindowCopyTM k j dst (j ≠ dst)` (**sorried**): a machine
`W`, states `entry`, `done`, a constant `C`, such that from `entry` with the input head at native
position `p + 1` and a delimited counter word `w` of value `d` on tape `j` (blanks at `-1` and `|w|`,
the `counterLoopTM` convention), with `y := (z.drop p).take d`: within `T ≤ C·(|y| + 1) + 2|w|`, no
`done` earlier, `W` reaches `done` with the input head at `p + 1 + |y|`, `y` written on `dst` from its
head and that head after it, the counter word replaced by some `w'` of the same width with the counter
head back, every other tape and head and the output unchanged.

**Part E** (`NDCodeSimulator`): `CodeNDTM.serialize_eq_tableBitsK` (proved): `M.serialize =
pairEncode (bits numStates) (unaryFin q₀ ++ (tableBitsK (fixChoice false).tr ++ tableBitsK
(fixChoice true).tr))`. `exists_replayCanonizer c` (**sorried**): some `FinTM` computes
`α ↦ serializeK (c.decode α).tm.replayTM` within some `T |α|`. `exists_ndInterpreterCore c`
(**sorried**): one `R : MultiTapeTM K Bool Q` with stream tape `j`, states `entry`, `accept`, `reject`,
**`accept ≠ reject`**, such that for every `α` some `C` gives, for all `x`, `t`, `s` with `t ≤ |s|`,
from `start` (state `entry`, input head `1` on `z = ⟨⟨bits t, α⟩, x⟩`, `s` on tape `j` from cell 0,
other tapes blank, heads at 0, output empty), with `e` the coded branch on `x` along `s.take t`: a time
`T` with the verdict state at `T` (`accept` iff `e` halted with output exactly `[true]`), neither verdict
before `T`, `T ≤ C·(t + 1)`, and `T ≤ C·(t' + |x| + |bits t| + 1)` whenever the branch along
`s.take t'` has halted, `t' ≤ t` (**the prefix clause**).

**Part F** (`ExhaustiveReplay`): `FinNDTM.exists_exhaustiveDecider N` (**sorried**): some `E : FinTM
Bool` and `C` such that whenever `N.tm.HaltsWithin z T`, `E` computes `[true]` if `N.AcceptsWithin z T`
and `[false]` otherwise, within `C·2^{C·(T + 1)}`. `ndAcceptsWithin_decider_of_universal c hUN`
(proved, modulo `E`): from the statement of `exists_timed_universal_NDTM` as a hypothesis, the
statement of `exists_ndAcceptsWithin_decider`, with `C := C_E·(C_α + 1)`.

## The docstring patch (verify against `freeze.log`)

`NTimeHierarchy.lean` gains, in comments only: (1) in the module's deviation list, the decision-4
fix (the quadratic is `Turing.timed_universal`'s per-step `O(|bits t| + 1)` decrement,
`Universal.lean:2777-2802`; `Complexity.TimeHierarchy.clockTM` is linear, `ClockLoop.lean:345`, and
not composable) and a new bullet declaring the guess-first routes; (2) statement 1's sketch, restated
(guess with the writer, then the deterministic core on the replay serialization, the window copy and
input locality; the amortized fused countdown kept; the `clockTM` attribution at `:110` removed);
(3) **statement 2's sketch, restated** (`BF := E(UN)`, decision 2; beyond the two sketches the brief
named, because the old sketch describes a dedicated replay loop that will not be built — policy §3,
synchronization; it is a separate hunk and can be dropped); (4) statement 4's (iii) (the guess as `D`'s
only nondeterministic phase; the step clock; the prefix-bound obligation as a clause of the core's
contract) and **the chain's mid-rung arithmetic**, which the window term changes (below); (5) the
named fill obligations of statement 4; (6) a rewrap of the one pre-existing line over 100 characters
(`:236`, sketch (ii)), with no word changed. The freeze check strips every comment from both versions
and finds the code identical (48 code lines, 6 declarations each); both elaborate with 0 errors and the
same 6 sorries.

## Changes from the draft (verify against log §7)

The comment-stripped statements of `C1HostsDraft.lean.txt` against the unit: 16 identical, 4 changed,
2 removed, 7 added (5 private helpers, `runWith_initCfg_take`, `exists_inputWindowCopyTM`).
1. **`runWith_eq_fixChoice_runFrom` takes the stage-2 statement verbatim**: binders `(tm) (b) (w)
   (cfg) (hagree)`, hypothesis `tm.tr false q = tm.tr true q` (function equality; the draft's was
   pointwise, equivalent by `funext`), at `Type*`. C1's proof is kept (the transfer at the identity
   embedding); the pointwise form is recovered by rewriting with the hypothesis.
2. **Universes**: the transfer lemmas, `relabelState` and the replay machine move from `Type` to
   `Type*`, so that the stage-2 statement (at `Type*`) is proved through them, and to match
   `Nondeterministic.lean`. `relabelState`'s `{S' : Type}` binder moves into the section variable. The
   phase host and the writer keep `Type`, as `phaseHostTM`.
3. **The draft's §4 leaves** (`clockCfg`, `exists_stepClockTM`): the clock is gated with B6.
4. **`exists_ndInterpreterCore` gains `accept ≠ reject`.** Without it the draft statement is
   **trivially satisfiable**: a machine with `accept = reject` that moves from `entry` to that state in
   one step and stays meets every clause for every code with `C = 1` and `T = 1`. (`entry` need not be
   required distinct: the cut at `u = 0` forces it whenever both verdicts occur.)
5. **`R`'s prefix clause changes** from `C·(t' + 1) + 2|bits t|` to `C·(t' + |x| + |bits t| + 1)`.
   Under decision 5, `R` copies the window `x.take t` before it simulates, at cost
   `Θ(min(t, |x|) + |bits t|)` whatever the halting time `t'`. The draft's clause is not met by that
   route (a coded machine whose initial state halts at once, `t' = 0`, with `t = |x| = n`: the window
   copy alone costs about `n`, against `C + 2|bits n|`); meeting it would need the in-place suffix
   device that decision 5 leaves with U-1. **Consequence for `D`** (sketch only, patched): the
   mid-rung cost of a genuine accepting branch becomes at most
   `C_α·(C₁·(c₀·f(n+1) + 1) + (n + 1) + |bits (g n)| + 1) ≤ A*·(f(n+1) + n + 1) + C_α·|bits (g n)|`
   with `A* := C_α·(C₁·c₀ + C₁ + 2) + 1` (round 2 had `+ 1` inside), absorbed by the domination
   hypothesis's `n + 1` addend; the `|bits (g n)|` term is `o(g n)`. The design note did not see this
   interaction.
6. **New, for decision 5**: `runWith_initCfg_take` (proved, with five private helpers) and
   `exists_inputWindowCopyTM` (sorried). The window is `x.take t` (`m = t` suffices for `t` steps;
   the design note had `x.take (t + 1)`), counted down on `bits t` itself.
7. **`NDWriterState` derives `DecidableEq`** (probes; later `Fintype` packaging).
8. **`ndAcceptsWithin_decider_of_universal`'s proof** no longer uses `nlinarith` and `ring`, which are
   outside `ExhaustiveReplay`'s import closure (the cut check failed with 4 errors until then). The
   statement is unchanged.
9. **Documentation**: statement prose and `[AB09, location]` on every declaration; a literal
   `**Proof sketch.**` on every nontrivial theorem, private helpers included; module headers for the
   five new modules. `serialize_eq_tableBitsK`'s docstring now says that it is an identity of
   `CodeNDTM.serialize` with its own header and not of any `serializeK` (H2-S NF5). `R`'s sketch cites
   H1's hosted clock (fills-8) and its two generalizations.

## The H2-S consumer ruling (NF5), mapped onto the decided route

The H2 design proposed for C1 a choice-*lifted* table (`audits/evidence/h2/C1LiftProbe.lean.txt`)
with a per-round choice installer; decision 3 chose the replay machine instead. The four obligations
the ruling keeps separate:

| Obligation | Under decision 3 and guess-first | Where |
|---|---|---|
| choice installer | none per round: the stream is written once by the writer and read by the replay machine from its own tape; the per-code table rewrite replaces the lifted table | `ndWriterTM_run_block` (sorried), `exists_replayCanonizer` (sorried) |
| nondeterministic host | the ND phase host and the transfer | `phaseHostND`, `phaseHostND_run`, `runWith_mapState_of_agreeOn_det` (proved) |
| branch alignment | the writer's exact guessed word and branch-independent time; the replay lemma; a "guess, then run" assembly lemma over `phaseHostND` | writer (sorried), `replayTM_runFrom` (proved), assembly **not stated** (open question 2) |
| amortized clock | inside `R`'s contract (both time clauses); H1's hosted clock with the counter ledger | `exists_ndInterpreterCore` (sorried); H1 harvest (above) |

The table identity: `CodeNDTM.serialize_eq_tableBitsK` is a full identity of the ND serialization
**with its own header** (state count, unary initial state, two tables). It is not described as an
equality with `serializeK` of any deterministic machine, and the replay serialization's header
coincidence (same states, same initial state) is part of the canonizer's sorried obligation.

## Brief for the auditor

Restate every definition in your own words before reading its docstring, argue each sorried theorem
true in 2–5 sentences or exhibit a counterexample, and attempt at least the adversarial
instantiations of point 11 (failure modes 1–4 of `audits/TEMPLATE.md`). Points to rule on:

1. **The guess-first route (decision 1).** Is it sound for `UN` and `D`? In particular: the writer is
   the only nondeterministic phase, and every other phase is deterministic and enters the phase host
   as `toNDTM`, so a branch of `UN` of length `C·(t + 1)` is determined by the `t` bits the writer
   wrote; `UN` accepts within `C·(t + 1)` iff some stream of length `t` makes `R` accept
   (`AcceptsWithin` is exact-length; absorption pads); all branches halt within `C·(t + 1)`. Is it
   right that **no nondeterministic counter loop is needed** (SC-3 closes), i.e. that no choice ever
   occurs inside a multi-step round host (the counter loop, the step clock)? Check the principle in
   Part C's module docstring against the hosts the route uses.
2. **Linear overhead (CH34-Q8) under guessing.** Check that the expansion of `t`
   (`Turing.expandTM`, `CounterLoop.lean:1524`), the guess (`t + 1` steps), the rewind, the window copy
   (`O(min(t, |x|) + |bits t|)`) and `R`'s `C_α·(t + 1)` keep `UN` within `C·(t + 1)` with no `|x|`
   term, and that `D`'s guess of `g n` bits fits its `K·(g n + 1)` allowance.
3. **`R`'s statement.** Is it true as stated (one machine for all codes, `C` per code)? The repair
   `accept ≠ reject`; the start configuration; the verdict `e.state = none ∧ e.output = [true]` against
   `Turing.FinNDTM.AcceptsWithin` (`NTIME.lean:93`); `s` longer than `t`; `t = 0`; both time clauses
   together. **Is the restated prefix clause right, and is its consequence for `D`'s chain**
   (`A*` and the `n + 1` addend; change 5) correct? Alternatively, should `D` guess a nominal budget
   `t' ≤ g n` (design note §3.6's fallback), so that `R` needs no prefix clause at all?
4. **The replay route (decision 3).** `replayTM` (blank read as `false`; the choice head moves on every
   live step; the choice tape is never written); the replay lemma's `p`; `exists_replayCanonizer`'s
   truth (arbitrary time; the header kept; records re-emitted in `workReadsK 3` order,
   `CodeSimulator.lean:91`, with the choice read innermost; blank and `false` choice reads give equal
   records); H2 at three work tapes needs exactly `tableBitsK` on its table tape
   (`h1RoundRep`, `CodeSimulator.lean:5599`), and its round bound `50·(|table| + 1)` is a per-code
   constant at 81 records per state.
5. **The window copy and input locality (decision 5).** Is `runWith_initCfg_take` the right lemma, and
   is `|w| ≤ m` tight (probe)? Is `exists_inputWindowCopyTM` true, including `w = []`, `p = |z|`
   (head on the right blank) and an input shorter than `d`? Is its endpoint the one `R` needs (`R`
   rewinds `dst`; the native input head is left after the window)? Does the counter convention match
   `Turing.counterLoopTM`'s (`CounterLoop.lean:593`)? Is `x.take t` (not `t + 1`) enough?
6. **`E` and `BF := E(UN)` (decision 2).** Is `E` true for every fixed `N` with `T` arbitrary per input
   and uncomputable (iterative deepening; the first all-halting length is at most `T`; acceptance at it
   and at `T` agree)? No `|z|` term: each replay of length `L` touches at most `L + 1` input cells, and
   the input head is rewound. `T = 0` is vacuous (probe). `E` must suppress `N`'s emissions to output
   exactly `[true]` or `[false]`. Is the derivation's constant right?
7. **The slice lemma.** Verbatim (log §7)? Is C1's proof route (the transfer at the identity
   embedding) acceptable for the gated statement, and its position at the end of the file?
8. **The transfer and the phase host** (proved). Do they say what their docstrings claim, and are they
   the form `UN`'s, `D`'s and stage 2's assemblies need?
9. **The writer's contract.** `m = 0`; the block's nonblank hypothesis; `done` live and silent; the
   input head and output untouched; every stream of length `m` is guessed.
10. **Homes, names, layering** (table above; open questions 1, 3, 5).
11. **Adversarial instantiations** (at least these): `numStates = 0` (a one-state `CodeNDTM`: the bridge,
    probe; the replay canonizer's output; `R` at a code whose machine halts at once); **empty input**
    `x = []` (`R`'s window is empty; locality is trivial; `UN` and `E` on `z` with an empty suffix);
    **a halting choice step** (probe `haltOnTrue`: `true` halts, `false` continues; along
    `[false, true, false]` the branch halts at time 2 and the replay's choice head stops at 2 after 3
    steps); `t = 0` (`R`: `e` is initial and live, so `reject`; `AcceptsWithin x 0` is false, probe);
    `k = 0` work tapes for the replay (one tape, the choice tape; probe); a stream `s` longer than `t`;
    `accept = reject` (the draft's trivialization).
12. **Documentation and policy** (`policy.md`): module headers, statement prose, attribution
    ([AB09] locations), a literal proof sketch on every nontrivial theorem, deviations declared,
    100-column lines; the patch's restated sketches against the P3.3 gate's carried obligations
    (`ch3-p33-resolutions.md:50-60`).
13. Report anything else that the files, this pack, the design note or the draft misstate.

**Open questions (maintainer recommendations in italics).**
1. *`E`'s home*: `ClassNP/ExhaustiveReplay.lean` (as proposed) or a `Build/` module with acceptance
   written out (`∃ w, |w| = T ∧ halted ∧ output = [true]`, definitionally `AcceptsWithin`)? *Keep
   `ClassNP`: the statement reads in class vocabulary and no layering rule is bent.*
2. *The "guess, then run" assembly lemma* (design note §3.1; branch alignment in H2-S's terms) is not
   stated. *State it in the C1-A statement round before `UN`'s brief, as a public lemma of
   `Build/NDHost.lean`; it is a lemma about a proved host, not a new host.*
3. *Statement 3's sketch* cites `Turing.MultiTapeTM.relabelState` for packaging an NDTM; the right
   citation is `Turing.NDTM.relabelState` (Part A). *Fix it in C1-D's brief, not in this patch.*
4. *The prefix clause* (brief point 3). *Keep the restated clause; the fallback adds a second guess
   phase to `D` for no gain.*
5. *The H1 harvest* (Dependencies): *register H1's hosted clock with the two generalizations as a
   requirement of the H2 promotion, so that `R`'s brief can cite a public host.*

## Repository-side attestations (verify or challenge)

Source facts (checkable in the bundle) are separated from maintainer execution claims (the logs).
- **Elaboration** (log §1): the unit, at `oleans-f8`, gives exit 0 and 0 errors; the only warnings are
  5 `declaration uses 'sorry'` (`ndWriterTM_run_block`, `exists_inputWindowCopyTM`,
  `exists_replayCanonizer`, `exists_ndInterpreterCore`, `FinNDTM.exists_exhaustiveDecider`).
- **Cut checks** (`cutcheck.log`): each of the six landing modules, in exactly its own import closure,
  gives 0 errors, and the unit's imports are exactly the union of the parts' (8): `Nondeterministic` 0
  sorries, `ChoiceReplay` 0, `Build/NDHost` 1, `Build/InputWindow` 1, `NDCodeSimulator` 2,
  `ExhaustiveReplay` 1. The landed forms of `Nondeterministic.lean` (581 lines), `ChoiceReplay`,
  `InputWindow` and `ExhaustiveReplay` elaborate standalone with 0 errors; `NDHost` and
  `NDCodeSimulator` import new content and are covered by the cut check only.
- **Axioms** (`axioms.log`): every proved declaration depends on at most `propext`,
  `Classical.choice`, `Quot.sound`; the five sorried ones and `ndAcceptsWithin_decider_of_universal`
  (through `E`) add `sorryAx`.
- **Probes** (log §3): 12 `example`s (the counter word `bits t` has value `t`; 81 and 54 records per
  state; a halting choice step in the replay; the writer at `m = 2` for all 8 words of length 3, all 4
  of length 2, and at `m = 0`; locality tight at `|w| = m + 1` and holding at `|w| = m`; `HaltsWithin`
  and `AcceptsWithin` false at `0`; the bridge at `numStates = 0`), 0 errors. Three negative controls
  fail (1, 1 and 4 errors).
- **Freeze** (`freeze.log`): the patch changes no code of `NTimeHierarchy.lean`; both versions
  elaborate with 0 errors and 6 sorries; the patched file has no line over 100 characters.
- **Names** (`names.log`): 27 declarations (22 public), no full-name clash with `TCSlib`; one name
  shared with the stage-2 `NDSlice` by design (`runWith_eq_fixChoice_runFrom`), none with the B6, H2,
  MIG-0 or stage-2 drafts otherwise; one short-name overlap (`NDTM.relabelState` /
  `MultiTapeTM.relabelState`, different namespaces, the mirror by design). A positive control with two
  planted clashes catches both.
- **Cited names** (log §6, `freeze.log`): every backticked identifier of the unit's and the patched
  file's comments was `#check`ed. Those that do not resolve are bound variables, module names, the
  stage-2 unit's name `NDSlice`, and names in modules not imported (`Turing.Contract`,
  `Turing.exists_timed_universal_NDTM`, `Turing.exists_ndAcceptsWithin_decider`,
  `Turing.timed_universal`, `Complexity.time_hierarchy`), or proposed in another pack
  (`Turing.exists_stepClockTMVia`).
- **Style lint** (log §4): `scripts/campaign_style_lint.py` over the six landing modules and the patched
  file: 0 FAIL, 0 WARN. **Widths** (log §5): no line over 100 characters.
- **Nothing in the checkout was changed**; no git, lake or elan command was run; `lean` ran only through
  `tools/leanelab.sh`, which writes no olean; Python only as `python3 -I`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/c1-hosts-statements-findings.md`. The gate closes when a round reports zero blockers and zero
majors; the parts then land as cut (homes as ruled), with the docstring patch.
