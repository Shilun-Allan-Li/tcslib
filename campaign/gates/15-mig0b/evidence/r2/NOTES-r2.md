# MIG-0b round 2: notes (2026-10-13)

Drafted read-only by a maintainer sub-agent against the checkout `wt-r2m0b`. It was at campaign
commit `385d6e5a` when the work started, and at `1781a230` (PR #84, fills-8) for every result
reported here. Elaboration used `oleans-f8` (all of TCSlib at `1781a230`), only through
`tools/leanelab.sh`. No `lake`, no git, no build command, no network; no `.olean` written. Figures
are labelled **MEASURED** (from a file or a run) or **ESTIMATE**. Paths are repository paths unless
they start with `<OUT>`, the round-2 output directory. D and A are round 1's draft and adapters
files (`audits/evidence/mig0b/Contract-mig0b-{draft,adapters}.lean.txt`).

**fills-8, merged mid-task.** Between the two commits only `CodeSimulator.lean` and
`Build/RecordTable.lean` changed (MEASURED: SHA-256 of `Build/Contract.lean`, `Build/Seam.lean`,
`Build/CounterLoop.lean`, `Build/Embed.lean`, `Build/Catalog.lean`, `Finite.lean` and
`StateRenaming.lean` unchanged). Every check below was re-run at `1781a230`. fills-8 matters in
three places (§7): a new unfolding consumer of `counterLoopOrbit` (`CodeSimulator.lean:5841`), a
new private copy of the R1 reconstruction lemma (`RecordTable.rt_embed_matches`, over `Type*`), and
shifted line numbers.

## 1. What changed since round 1

| Round-1 item | Round 2 |
|---|---|
| D started with a **copy** of the gated MIG-0a file; the split was a plan (NOTES §6) with a probe that kept the fit bridge and left out the seam consumers | The split is **the draft**: one landing unit of 13 parts (`<OUT>/Contract-mig0b-r2-unit.lean`), generated from the **landed** `Build/Contract.lean` and the round-1 evidence by `build.py`, each part cut-checked in exactly its own import closure, with no fit namespace in the unit and the seam consumers in their own module (finding 1) |
| `mem_hull_left/right`, `runFrom_state_none_mono` private in the core, used by the seam proofs | **Deleted.** Their 12 uses cite public results: Mathlib's `Finset.Icc_subset_Icc` (7 hull uses) and `Finite`'s `MultiTapeTM.runFrom_state_ne_none_of_le` (5 halting uses: `seq_traj`, `live`, `branch_traj`, `Segment.live`, `ReturnContract.toRound`) |
| `counterLoopTMVia_done_witness` called `MIG0bFit.counterLoop_hround_of_rounds` | Derives the round hypothesis locally from `Round.cut_some`, as the escape witness already did; the fit lemma stays in the fit file |
| `seamReleaseTM_runFrom_pos` over `Type`, via `runFrom_mapState_of_agreeOn` | **Dropped.** `Build/Seam`'s private `seamRelease_run_pos` is promoted under that name with its universes and its step-commutation proof, together with its two step lemmas (`seamReleaseTM_step_fresh`, `seamReleaseTM_step_inr`) (finding 2) |
| Layering homes: `Deterministic` for the two raw-layer lemmas | **`Finite`**: `Finite.lean` is where raw-layer additions go, "so the vendored `Deterministic.lean` stays byte-comparable with upstream" (its own docstring; `Deterministic` is vendored from cslib) |
| `counterLoopOrbit` unchanged, with an `rfl` lemma | An `abbrev` of `roundOrbit` (Q11); the four proofs that unfold it are edited and checked, three of them outside the MIG-0b files (§6) |
| `ReturnContract.release`'s envelope through the visited sets | Through the pointwise lockstep (Q14), statement unchanged |
| Minors 3–5 | `Contract.lockstep_admissible` and `_map` with the condition documented; `RoundContract.release`'s two-exit claim qualified; a literal proof sketch for the admitted lockstep and the full [AB09] entry where it is cited |

Also new in round 2, each explained in §5: the raw-layer exports that move into `Build/Embed` and
`Build/Seam` take those modules' universes (`Type*`); `embedEmitCfg_select` is re-derived from the
R1 lemma; `workTapePos_runFrom_mem_Icc` is stated over any alphabet and state type.

## 2. The unit, and why it is built from the landed file rather than importing it

The brief asked for the round-2 draft as an increment on the landed `Build/Contract.lean`,
importing it. A pure increment cannot be the landing form, for two reasons the split exists to
remove:
1. `Build/Loop` (MIG-17) and other lower modules must import the core, but the landed file imports
   `Build/Catalog`, which imports `Build/Loop`.
2. MIG-0b's seam layer (`Traj.seq`, `Traj.inPhase`, `Traj.branch`, `Frames.seq`,
   `RoundContract.release`) uses the landed file's **private** trajectory lemmas (`seq_traj`,
   `inPhase_traj`, `branch_traj`, `release_start`, `mapState_state`), which another module cannot
   see; finding 1 is this problem's other half.

So the MIG-0a text must move, and the evidence is made to match what lands in a different way:
`build.py` takes every MIG-0a declaration **by name from the landed file** (not from D's copy),
asserts that each of the 37 landed declarations is taken exactly once or is in a declared
retirement list, applies every edit as an exact replacement asserted to match once, and records
each block's source and hashes in `<OUT>/manifest.json`. `identity.py` then re-derives, from the
files themselves, that the landed file is the gated round-2 file with only its status paragraph
changed, and lists each declaration's fate (§8). The round-1 MIG-0b declarations are taken by name
from D and A in the same way (91 of 93 kept, 2 retired; MEASURED).

**Part kinds.** A part is *appended* to an existing module when it lists that module among its
imports (Finite ×2, StateRenaming, Build/Embed, Robustness/AlphabetReduction), the **whole edited
file** of an existing module when it does not (Build/Seam, Build/CounterLoop, and Build/Contract,
which becomes the facade), and otherwise a new module (Contract/Basic, /Seam, /Embed, /Catalog,
/Lift). A `-- @moved-from M` part holds declarations moved verbatim from `M`.

**The cut check** (`cutcheck2.py`) extends `audits/evidence/stage2-gate/scripts/cutcheck.py`:
- the closure follows existing modules too, so an appended part reaches every check whose
  closure holds its module (the CounterLoop check includes the Embed part through
  `Catalog → Loop → Embed`, and the AlphabetReduction part through `Catalog → Encoding →
  SingleTape → AlphabetReduction`);
- a moved part is omitted where its old home is already imported (its body is byte-identical to
  the old copy, `identity.py` §3.3, and its printed type too, `sigprobe.py`);
- a check stops if an existing module of its closure imports a module that an included part
  replaces;
- extras parts (`<OUT>/extras.lean`, generated by `mkextras.py`) check the edited existing files
  whole, in their own closures, the downstream consumers of Q11, and the fit file over every
  landing module.

The method checks each landing module against the *old* oleans of the modules below it plus the
parts in its closure. It does not rebuild the 170 modules that would newly have the core in their
closure, or the 26 that depend on `Build/CounterLoop` (MEASURED, `graphcheck.py` and
`tools/closure.py`): the landing PR's replay remains a separate obligation, as the auditor said.

## 3. The revised layering plan

All line counts MEASURED on `<OUT>/landing/`, the files the landing PR writes (header included).

| Module | Kind | Imports (as landed) | Lines | Contents |
|---|---|---|---|---|
| `Finite` | appended (parts 1, 2) | unchanged | 354 → 410 | `MultiTapeTM.spaceUsedByTape_le_card_Icc` (moved from `Build/Catalog:392`, verbatim); `MultiTapeTM.workTapePos_runFrom_mem_Icc` (round 1's export over `Type*`); docstring entries |
| `StateRenaming` | appended (part 3) | + `Simulation` | 124 → 182 | `MultiTapeTM.runFrom_mapState_of_agreeOn` (moved from `Build/Embed:1010`, verbatim; its signature, `{S H : Type}`, kept); docstring entry |
| `Build/Embed` | appended (part 4) | + `Build/Convention` | 1,049 → 1,126 | the moved block deleted; `embedEmitCfg_unselected`, `Cfg.select`, `embedEmitCfg_select` (moved from `Build/Contract`), `embedEmitCfg_eq`, `_mapState_eq`, `_ofWords_eq`; all over `Type*` |
| `Build/Seam` | whole file (part 5) | unchanged | 854 → 873 | `seamComp_right` promoted as `seamCompTM_runFrom_right`; `seamRelease_fresh_step`, `_step_right`, `_run_pos` promoted as `seamReleaseTM_step_fresh`, `_step_inr`, `_runFrom_pos`; 6 call sites renamed; docstring |
| `Build/Contract/Basic` | new (part 6) | `Linarith`, `Simulation`, `StateRenaming` | 1,309 | MIG-0a: `Contract`, `within`, `spaceUsedByTape_le`, `Positive`, `mem_Icc_of_abs_le`, `trans`, `live`, the frame layer, `ReturnContract`. MIG-0b: segments, `SafeSegment`, the bridges, rounds, `roundOrbit`, `RoundContract` with `returning`/`escaping`, `ReturnContract.toRound`, the orbit hulls, `headBox_lastCases`, `Traj` with `trans`, `Frames.trans`, the sanity lemmas, `Contract.mapState`, `Lockstep`, `Contract.lockstep`, `lockstep_admissible(_map)` |
| `Robustness/AlphabetReduction` | appended (part 7) | + `Build/Contract/Basic` | 884 → 969 | the admitted lockstep and the contract theorem (open question 1) |
| `Build/Contract/Seam` | new (part 8) | `Contract/Basic`, `Build/Seam` | 815 | MIG-0a: `seq`, `inPhase`, `Cfg.bindState`, `branch`, `ReturnContract.release` with their private trajectory lemmas. MIG-0b: `RoundContract.release`, `Traj.seq/inPhase/branch`, `Frames.seq`, positivity |
| `Build/Contract/Embed` | new (part 9) | `Contract/Basic`, `Build/Embed` | 128 | `embed`, `Traj.embed`, `embed_positive` |
| `Build/Contract/Catalog` | new (part 10) | `Contract/Basic`, `Build/Catalog` | 102 | `clearTM_contract`, `_frames`, `_traj` (MIG-11's instances join it) |
| `Build/Contract/Lift` | new (part 11) | `Contract/Basic`, `SymbolLift` | 82 | `Contract.liftSymbols` |
| `Build/CounterLoop` | whole file (part 12) | + `Build/Contract/Basic` | 1,699 → 2,118 | `counterLoopOrbit` an abbreviation of `roundOrbit`; one proof edit; the `_witness`/`_segment` theorems, `counterLoopBody`, `counterLoopCfg_body`, `counterValue`, `RoundContract.counterLoopDone/Escape` with `_traj`; docstring |
| `Build/Contract` | whole file: the facade (part 13) | the five `Contract/*` modules | 1,101 → 52 | `## Contents` |
| `Build/Catalog` | edit only | unchanged | 12,752 → 12,732 | the moved lemma deleted; docstring |
| `Build/CfgRecord`, `CodeSimulator` | edit only | unchanged | unchanged | Q11's consumers (§6) |
| `Build/Zone`, `TuringMachine` (facade) | docstrings | unchanged | unchanged | the lemma's home; the `Build/Contract` entry |

The core's closure is `Configuration`, `Deterministic`, `Finite`, `Simulation`, `StateRenaming`
(MEASURED, `graphcheck.py`), so `Build/Loop`, `Build/CounterLoop`, `Build/Catalog`, `Build/Embed`,
`Build/Seam` and `Robustness/SingleTape` can all import it; the import graph with the landing files
substituted is acyclic. Imports were checked by elaboration, not reasoned: each part's check imports
exactly the closure above. `TCSlib.lean` needs no change: it imports `TuringMachine`, which imports
the facade.

**Basic's size.** It is 1,309 lines, and the repository lint calls a file over 1,000 lines a split
candidate (auditor note 19). File size alone is not a reason to split (user rule); the module is
one import boundary (everything `Build/Loop` and `Build/CounterLoop` may need), and a further split
would add modules without moving any boundary. No split is proposed.

## 4. The findings

**Finding 1.** Resolved as above. The cut checks run with `MIG0bFit` absent from the unit
(`build.py` asserts it). The seam consumers that broke are in `Build/Contract/Seam`, checked over
`Contract/Basic` and `Build/Seam` alone: `seq_traj`, `seq`, `branch_traj` and `branch` now use only
public results, and `live` is public in the core. `counterLoopTMVia_done_witness` no longer refers
to the fit namespace. The other private helpers left (`mapState_state`, `mapState_const_inl(_inl)`,
the three trajectory lemmas, `release_start`, `mapState_traj`) are each used only inside their own
module, which the checks confirm.

**Finding 2.** The promoted lemma keeps the private lemma's statement (`{Symbol : Type*}`, the
section's `{S : Type*}`) and its proof through `seamReleaseTM_step_fresh`, `seamReleaseTM_step_inr`
and `MultiTapeTM.runFrom_comm_of_step`; it does not use `runFrom_mapState_of_agreeOn`. The public
consumers `seamReleaseTM_firstReturn` and `seamReleaseTM_visitedByTapeHead` keep their statements
byte for byte (`identity.py` §3.5) and their printed types (all 18 public `Build/Seam` declarations,
`sigprobe.py`); only their call sites changed. The fit file checks that round 1's `Type` statement
is an instance, and instantiates the lemma at a machine whose state carrier is `Type` itself, the
auditor's example.

**Minor 3.** `Contract.lockstep_admissible`: if `enc` maps every source configuration at `entry` to
one at `entry'`, every admissible source start `c` gives the admissible target start `enc c`;
`_map` is the case of a state-renaming encoding with `entry' = ρ entry`. `Contract.lockstep`'s
docstring states the condition. The fit file has the auditor's case (identity encoding, `b ≠ a`:
no admissible start) and the compatible case.

**Minor 4.** `RoundContract.release`'s docstring now says that the escape set is arbitrary (it may
hold `none`, several states, or the anchor), that only `escape = {some e}` with `e ≠ anchor` gives
two distinct live exits, the shape of `branch`'s first phase, and that the phase host needs in
general that `none` is not an exit and the redirect conditions. Two fit examples check the halting
case and the singleton case. The formal statement is unchanged. The round-1 notes' row for it
(§3) is superseded by this one.

**Minor 5.** `exists_alphabetReduction_lockstep` has a literal `**Proof sketch.**` naming the
witnesses (`arTM` with the one-hot code, `L = 3(|Γ| + 1) + 2`, `ρ = arReady`, `enc = arCfg`) and
covering the step equation (`arCfg_cycle`) with a halted source, offset `0` (injectivity of `ρ`),
the intermediate controls (live read, write and move controls, none of the form `arReady q`, so
outside the renamed `X` for every `X`, `none ∈ X` included), and the halted source's offsets. The
full [AB09] entry is in the new section's docstring and in `AlphabetReduction`'s References (which
already had it), and in `Contract/Basic`'s References, where `Lockstep` cites Claim 1.5.

**Minor 6.** The record corrections are listed in §10, not made.

**Rulings applied.** Q11 (§6). Q14: `ReturnContract.release`'s envelope at time `0` is the start's,
and at positive times the release run is the right-tagged source run (`seamReleaseTM_runFrom_pos`);
its statement and data fields are unchanged and the sketch was rewritten to match.

## 5. Changes beyond the findings, and why

1. **Raw-layer exports take their host module's universes.** Finding 2's principle is that the
   contract structures' `Type` convention does not justify narrowing a raw-layer lemma. Applied to
   the other moves:
   - `seamCompTM_runFrom_right`. MIG-0a's export (over `Type`) had a private polymorphic twin in
     `Build/Seam` (`seamComp_right`). The twin is promoted under the export's name; the landed
     statement is an instance (checked).
   - `embedEmitCfg_unselected`, `Cfg.select` and `embedEmitCfg_select` (MIG-0a), and
     `embedEmitCfg_eq`, `_mapState_eq` and `_ofWords_eq` (round 1). They are stated over
     `Type*`, like the rest of `Build/Embed`. fills-8's `RecordTable.rt_embed_matches` is a private
     copy of the R1 lemma over `Type*`, which a `Type` lemma could not replace at its own
     signature; the fit file proves its verbatim statement from `embedEmitCfg_eq`.

   The only printed-type changes in the whole unit are these generalizations, plus
   `workTapePos_runFrom_mem_Icc`'s. One more type changes only by the universe instantiation
   `.{0, 0}`: `Traj.embed`, which mentions `Cfg.select` (`sigprobe.py`). The structures, and the
   moved `runFrom_mapState_of_agreeOn`, keep `Type` (open question 2).
2. `embedEmitCfg_select` is now a one-term corollary of the R1 lemma. That retires MIG-0a's own
   time-zero frame workaround, the very debt family the lemma resolves. Its statement is unchanged
   apart from the universes.
3. `MultiTapeTM.workTapePos_runFrom_mem_Icc` is stated over any alphabet and state type, in
   `Finite`'s variable style (round 1's statement is an instance, checked).

## 6. Q11: `counterLoopOrbit` as an abbreviation of `roundOrbit`

An `abbrev` changes what `rw [counterLoopOrbit]` and `simp [counterLoopOrbit]` produce:
`roundOrbit …`, not the iterate. Every use was screened (`grep` over `TCSlib/` at `1781a230`,
MEASURED: 6 files mention the name; 5 sites, in 4 declarations, unfold it):

| Site | Use | Result |
|---|---|---|
| `Build/CounterLoop.lean:1156` (`counter_rounds`) | `simp [counter_layout, counterLoopOrbit]` | needs `roundOrbit` added (negative control fails without it) |
| `Build/CfgRecord.lean:716`, `:729` (`recordStep_save_orbit`) | `rw [counterLoopOrbit, Function.iterate_succ_apply']` | need `roundOrbit` added (negative control: 2 errors) |
| `CodeSimulator.lean:5841` (`h1Clock_orbit`, new in fills-8) | `simp only [counterLoopOrbit, Function.iterate_succ_apply']` | needs `roundOrbit` added (negative control: 1 error) |
| `SpaceComplexity/Inclusions.lean:2553` | `simpa only [counterLoopOrbit, Function.iterate_zero_apply, …]` | **no edit**: elaborates verbatim |
| every other use (`InputCall`, `InputLength`, `CodeSimulator`'s term uses, `RecordTable`'s comment) | statements, `change`, terms | elaborate verbatim |

The four edits each add the one token `roundOrbit`. The downstream probes elaborate `InputCall`,
`CfgRecord`, `Inclusions`, `CodeSimulator` and `InputLength` over the new `Build/CounterLoop` (with
the old `Build/Seam`, whose changes do not bear on this). All 31 public `Build/CounterLoop`
declarations keep their printed types. `CodeSimulator.lean` is a fill-batch file (H1, B5a):
landing order is open question 5.

## 7. fills-8: re-checked references at `1781a230`

The R1 family's members and the fit rows were re-located (MEASURED). The R1 reconstruction lemma's
consumers in `CodeSimulator` are unchanged in text and have moved:

| Row | Round 1 (`wt-m0b`) | Now |
|---|---|---|
| `CodeSimulator.canonEmbedEq` (private) | `:1201`, 4 uses | `:1205`; uses `:1242`, `:1690`, `:1702`, `:1779`, `:2098` (5) |
| `CodeSimulator.canonEmbedWords` (private) | `:1231`, 9 uses | `:1235`; 13 uses, `:1301`–`:2549` |
| `CodeSimulator.h1Run_headBound` (private) | `:3638` | `:4466`; use `:5733` |
| `RecordTable.rt_find_round_entry` (fit `findRound_round`) | `:1810` | `:1811`, text unchanged |
| `RecordTable.rt_findClock_eq` | — | `:1787`, text unchanged |
| **`RecordTable.rt_embed_matches`** (private, new in fills-8) | — | `:3727`; uses `:3786`, `:3799`, `:3950`, `:3971`; a member of the R1 family over `Type*` |

`OracleSim`, `Loop`, `Primitives`, `CertShell`, `EmitIterEmbed`, `SingleTape`, `CfgRecord` and
`CounterLoop` are unchanged, so round 1's citations into them stand. The round-1 fit tests are
carried unchanged; their docstrings cite `wt-m0b` lines.

## 8. Evidence

| File | What it shows |
|---|---|
| `<OUT>/Contract-mig0b-r2-unit.lean` (5,792 lines, SHA-256 `f61731e3…`) | the landing unit |
| `<OUT>/landing/` | every file the landing PR writes, in full, with a `.diff` against the worktree for the 12 existing ones |
| `<OUT>/fit-tests.lean` (462 lines) | round 1's 28 fit declarations unchanged, and 13 round-2 `example`s |
| `<OUT>/elaboration.log` | all runs (§2 cut checks, extras, negative controls, warnings beyond the baseline; §3 identity; §4 signatures; §5 axioms; §6 lint; §7 import graph) |
| `<OUT>/axioms.log` | the 201 axiom prints |
| `<OUT>/manifest.json` | each block's source, edit flag and hashes |
| `<OUT>/work/scripts/` | `build.py`, `mkextras.py`, `cutcheck2.py`, `identity.py`, `sigprobe.py`, `axprobe.py`, `graphcheck.py`, `blocks.py`, `runall.sh`, `elab_all.sh`; `<OUT>/work/src/new.lean`, the new text |

`bash runall.sh <S>` regenerates everything from the worktree in one run (about 2 minutes on 12
cores, MEASURED). The scripts expect the layout `<OUT>/work/scripts/` with the new text at
`<OUT>/work/src/new.lean`; in the repository bundle they sit in `audits/evidence/mig0b/r2/scripts/`.
The generated `extras.lean` (42,748 lines, MEASURED, mostly whole copies of the edited existing
files and the probed consumers) and the check files are not bundled, since `runall.sh`
regenerates them.

Results (MEASURED, `elaboration.log`):
- the 13 landing checks: exit 0, 0 errors;
- the 5 whole edited files, the 5 downstream probes and the fit file: exit 0, 0 errors;
- the 3 negative controls fail as they must;
- warnings: exactly the worktree files' own (Seam 5, Embed 2, Finite 2, Catalog 90, CodeSimulator
  3), and the one `sorry` in every check whose closure holds part 7;
- axioms: 201 prints, and only `exists_alphabetReduction_lockstep` and
  `alphabetReduction_contract` depend on `sorryAx`; nothing beyond `propext`, `Classical.choice`
  and `Quot.sound`;
- statements: all 33 moved MIG-0a declarations keep their statements except the 3 universe
  generalizations; all 30 `Build/Seam`, 54 `Build/CounterLoop`, 481 `Build/Catalog` and the other
  edited files' declarations keep theirs, `counterLoopOrbit`'s body aside;
- printed types: 23 of 27 MIG-0a, 18 of 18 `Build/Seam`, 31 of 31 `Build/CounterLoop`, 2 of 2
  moved and 85 of 92 round-1 public declarations are identical, the rest being the
  generalizations (§5);
- lint: compared with the worktree files, the landing files add one finding, `Contract/Basic`'s
  size, and lose one, the landed `Build/Contract.lean`'s size.

## 9. Size

**MEASURED** (`<OUT>/landing/` against the worktree):

| Group | Lines |
|---|---|
| New modules: Contract/Basic, /Seam, /Embed, /Catalog, /Lift, facade | 1,309 + 815 + 128 + 102 + 82 + 52 = 2,488 |
| The landed `Build/Contract.lean`, replaced | −1,101 |
| Appended or edited existing modules | Finite +56, StateRenaming +58, Embed +77, Seam +19, CounterLoop +419, AlphabetReduction +85, Catalog −20 |
| **Net** (16 files, +3,260 / −1,179) | **+2,081** |

So MIG-0 is 1,101 (MIG-0a) + 2,081 (MIG-0b) ≈ **3.2k lines** (MEASURED), against backlog MIG-0's
"+1.5k to +2.5k" (ESTIMATE) and round 1's 3.3k–3.4k (ESTIMATE). The fit file (462 lines) does not
land. The direct retirements at the rebases (about 400 lines, round-1 ESTIMATE) are unchanged, plus
`rt_embed_matches` (about 25 lines, ESTIMATE).

## 10. Record corrections for the maintainer (minor 6; not made here)

1. **backlog MIG-0.** At `1781a230` the row's status is already corrected: MIG-0a's round 2
   closed and it landed by PR #83; MIG-0b round 1 was 0/2/4. Its estimate column still says
   "+1.5k to +2.5k". MEASURED: MIG-0a 1,101 lines plus MIG-0b net +2,081, about +3.2k.
2. **Design §16a item 4.** It names only the interval-space move. It should list:
   - both moves, with their homes: `spaceUsedByTape_le_card_Icc` to **`Finite`**, not
     `Deterministic`; `runFrom_mapState_of_agreeOn` to `StateRenaming`, which then imports
     `Simulation`;
   - the deleted MIG-0a helpers;
   - the `Build/Seam` promotions;
   - `AlphabetReduction` importing the core;
   - the Embed exports' universes;
   - the core's closure: `Configuration`, `Deterministic`, `Finite`, `Simulation`,
     `StateRenaming`.
3. **F7-1(b), F6-1(i): the R1 family.**
   - The silent flavour (`CertShell.cert_silent_words`) is a **named remaining part**, to be
     resolved at MIG-14 by a capture-field export and a silent corollary. It is not discharged
     by `embedEmitCfg_eq`.
   - Accounting: `CounterLoop.counter_layout`, `CodeSimulator.canonEmbedWords`,
     `CertShell.cert_embed_words` and MIG-0a's `embedEmitCfg_select` (re-derived in this round)
     are members, and fills-8 adds **`RecordTable.rt_embed_matches`** (`:3727`, 4 uses), retired
     at MIG-13.
   - The CodeSimulator use counts are now 5 and 13.
4. **RS-5.** Its row mentions only envelopes. One milestone is missing: prove
   `exists_alphabetReduction_lockstep` in `AlphabetReduction` against `arTM`, `arCfg` and
   `arCfg_cycle`, with the intermediate-control lemma (80–150 lines, ESTIMATE). Round 1's notes
   §6 called this instance "proved" at the split; it is admitted.
5. **F7-1(a), H2, and the run head bound.** Ruling O9 places
   `MultiTapeTM.abs_workTapePos_runFrom_sub_le` in `Build/StepBlock` (H2-M), moving down with
   MIG-1. MIG-0b lands the interval form `workTapePos_runFrom_mem_Icc` in `Finite`, and the fit
   file proves H2's exact statement from it in three lines. Record: when both have landed, H2's
   lemma becomes that corollary, beside the interval lemma in `Finite`, rather than a second
   proof.
6. **backlog MIG-1's note** "Spec theorems in the existing style, not `Contract` instances
   (layering: `Contract.lean` imports `Catalog`)" no longer holds after the split:
   `Contract/Basic` does not import `Catalog`, and Catalog instances live in `Contract/Catalog`.
7. **backlog MIG-15.** `counterLoopOrbit` becomes an abbreviation at MIG-0b (Q11). The
   compatibility name stays, and the consumer edits land with MIG-0b (§6).
8. **Design §16a decision 1.** Add that raw-layer exports take their host module's universes
   (finding 2), while the contract structures keep `Type`.
9. **Round-1 notes.** §3's `RoundContract.release` row ("two live exits") and §6's `Deterministic`
   homes are superseded by this file.

## 11. Open questions, with recommendations

1. **Land the admitted alphabet pair now, or with RS-5?** As planned it lands now (part 7). That
   adds one `sorry` to `Robustness/AlphabetReduction`, which has none today, and puts the core in
   the closure of 170 modules through `SingleTape` and `Encoding`. *Recommendation:* hold part 7
   for RS-5, which proves it in place. The gate audits the statements now, and nothing else in the
   unit depends on part 7.
2. **The universes of §5.** *Recommendation:* accept. Every earlier statement is an instance, and
   no consumer's statement changes. Leave `runFrom_mapState_of_agreeOn` at `Type` (a verbatim
   move); generalize it under UNIV-1 if wanted.
3. **`Finite` rather than `Deterministic`** for the two raw-layer lemmas. *Recommendation:*
   `Finite`, by the vendored-file rule.
4. **The cut-check extension** (closure through existing modules, moved parts, whole-file parts):
   is it an adequate stand-in for checking each landing module before the landing replay?
   *Recommendation:* yes; the landing PR still runs the full replay.
5. **Landing order with `CodeSimulator.lean`'s owners.** The Q11 edit at `:5841` touches a
   fill-batch region (H1). *Recommendation:* include the one-token edit in the MIG-0b landing PR
   if no continuation holds the file. Otherwise land MIG-0b after it, re-running probe 109.

## 12. Recommendations (not work in this round)

- `Frames.embed`, before MIG-16 relies on it (Q13).
- Trajectory predicates for `ReturnContract` and `RoundContract` (Q13).
- A general positive-cut contract with its release, gated before claiming direct support for all
  install and emit calls (Q5; F7-1(d)'s `canonStrictInstall`). The release must preserve duration,
  endpoint and envelope without requiring that intermediate states avoid repeated entry visits.
- Uniform-bound corollaries of the hull envelopes where consumers need a fixed window (Q12).
- A round-time uniqueness lemma for the proof clock: `Segment.time_eq` needs a first-step shift
  there (note 9).
- Positivity from the linked second contract (note 16).
- The silent reconstruction corollary at MIG-14 (Q9).
