# External audit pack — Stage 2, PROG-3 and PROG-2: the word RAM on Turing machines (statement gate)

Campaign: the programming layer (design `machine-library-design.md` §15–§15d, §16, §16b; backlog
PROG-1 to PROG-4), under the Arora-Barak chapters 3-4 plan. The language-first decision (§15a)
routes Savitch's theorem, `NSPACE ⊆ DTIME(2^O(S))`, TQBF ∈ PSPACE, graph search, `PATH ∈ NL`,
Immerman–Szelepcsényi and the algorithms curriculum through programs of the vendored light
language ([AFM26], §15b), compiled in two stages: stage 1, the vendored compiler to the word RAM;
**stage 2, one Turing machine that simulates a word-RAM program** (PROG-4). Stage 2 needs the RAM
extended by input read in place, output, read-once coins and halving (PROG-2), and footprints
along runs (PROG-3). Every downstream route is stated against these statements, so they must be
right before any fill.

**This gate audits statements and definitions only.** Every theorem is `sorry` under a proof
sketch; definitions have their real bodies. Nothing is landed. Three files are under audit:

| File (bundle path) | Content |
|---|---|
| `audits/evidence/stage2-gate/Stage2.lean.txt` (1024 lines) | **stage 2 and PROG-3**: six parts, each the body of one landing module or one local modification of a vendored file (table below) |
| `audits/evidence/stage2-gate/NDSlice.lean.txt` (93 lines) | **the nondeterministic slice lemma**: two additions to the machine core that the nondeterministic form needs |
| `audits/evidence/stage2-gate/LanguageExtensions.lean.txt` (563 lines) | **PROG-2, as a specification mirror**: the edited vendored declarations under `X`-prefixed names, and the new declarations |

Supporting evidence: `audits/logs/stage2-statements-elaboration.log` (every check below);
`audits/evidence/stage2-gate/probes/*.lean.txt` (semantic sanity probes);
`audits/evidence/stage2-gate/scripts/*.py` (the cut check, the draft comparison, the name screen,
the cited-name extractor); `audits/evidence/stage2-gate/upstream-Footprint.lean.txt` (upstream's
deferred footprint file, for the last attestation); the drafts this pack turns into landing form,
`audits/evidence/stage2/{Stage2Draft.lean.txt, ExtensionsDraft.lean.txt, NOTES.md}`.

**Bundle:** `audits/stage2-statements-bundle.md`: this pack, `audits/TEMPLATE.md`, `policy.md`,
`workflow.md`, the design document and the backlog, the three files, the probes, scripts and log,
the drafts and notes, and every library file that the statements, sketches or this pack cite.

**Provenance (maintainer).** A maintainer sub-agent drafted the files against the read-only
checkout `wt-g2` of campaign commit `d63c7159c30b87c8e77b7aa5a9ca6adfc942f21d`, with the olean
snapshot `oleans-f7`. The bundle is built at a later campaign commit. Between the two, the only
Lean changes are the restated `SpaceComplexity/Hierarchy.lean` (PR #82) and the landed
`TuringMachine/Build/Contract.lean` with its facade import (PR #83). No file this pack cites by
line is among them, so every `file:line` here and in the files holds at the bundle's commit. The
two probe tails are bundled as `scripts/*_tail.lean.txt`, a `.txt` suffix like the other Lean
evidence, so that nothing under `audits/` is a Lean source.

## What the gate covers

1. **Stage 2 (PROG-4)**: the deterministic and nondeterministic simulation theorems, their bounds,
   the word-size hypothesis with its two bridges, and nine corollaries (DTIME, P, SPACE, L,
   log-space transducers, Savitch's `SPACE(S·S)` shape, NSPACE, NL).
2. **PROG-3**: footprints along runs, at the RAM level (`StepsIn`, `XStepsIn`) and for compiled
   code (`sim_in`, `compileProgram_footprint`), and the interface from the compiler to stage 2's
   hypothesis (`haltsWithin_compileProgram`).
3. **The RAM extension**, by the wrapper (`XInstr`, `XCfg`, `xstep`), with conservativity over the
   vendored RAM.
4. **PROG-2 as a specification**: the four new statements, `Exec`'s new indices, `EndsIO` and its
   rules, the determinism lemma, `XFits`, and the exhaustive list of vendored definitions and
   inductions that the real, scripted edit must extend. The edit itself is not audited here:
   backlog PROG-2 gives it a fidelity check of the vendored edits, then a statement gate for the
   new rules; this gate is the specification that both will be checked against.
5. **The proposed homes and module names**, and the landing obligations they create.

Out of scope: proofs and the fill route beyond the sketches; MIG-0a's `Turing.Contract`, which
stage 2's fill will use (gated in two rounds, `audits/mig0a-pack.md`; landed by PR #83 as
`TCSlib/Complexity/TuringMachine/Build/Contract.lean`, bundled); the vendored upstream design.

## Decisions in force (verify that the files reflect them)

**User decisions of 2026-10-12, binding** (design §15d, "Answered"):
1. The RAM is extended by a **wrapper**, `XInstr.base` with `XCfg` extending `Cfg`, not by new
   constructors of the vendored `Instr`.
2. `Exec`'s output and coin indices are added **in place** (option A).
3. The word size is **`WordSizeComputable W TW SW`**, with two bridges: `c·logSpace`, from R8.5c,
   and `c·S`, from `SpaceConstructible`.
4. `emit` appends "nonzero"; the footprint counts **touched** cells (read or written).

**Earlier rulings** (design §15a–§15c, §16, §16b): language first; two stages; the input read in
place by a statement `x := inBit e` and a RAM `rdIn`, `inLen` from an argument cell, no `len`
instruction (§15c); coins read once, a consumed `List Bool`, with **time and space bounds uniform
over all streams** (§15c); `emit` and `half` included now (§15c); Savitch and
`NSPACE ⊆ DTIME(2^O(S))` as programs (§16, decision 3); Savitch's configurations as single words
of `Θ(S)` bits, so stage 2 takes a **computed word size** and keeps "cells times word width"
(§16b item 1); C2 as programs with coins, so stage 2 needs a **nondeterministic form** and a
**logspace grade** (§16b item 4). Audit rounds verify these; they do not dispose of them.

## Homes and module names (proposed; the auditor rules on them)

| Part | Lands as | Namespace | Size at landing (lines, estimate) |
|---|---|---|---|
| `Stage2` A | new `TCSlib/Programs/WordRAM/Extended.lean` | `WordRAM` | about 400 |
| `Stage2` B1 | appended to vendored `TCSlib/Programs/Light/Compiler/Simulation.lean` | `Light.Compiler` | +58 |
| `Stage2` B2 | appended to vendored `TCSlib/Programs/Light/Compiler/WholeProgram.lean` | `Light.Compiler` | +80 |
| `Stage2` C | new `TCSlib/Complexity/RAMSimulation/WordSize.lean` | `WordRAM` | about 100 |
| `Stage2` D | new `TCSlib/Complexity/RAMSimulation/Simulation.lean` | `WordRAM` | about 160 |
| `Stage2` E | new `TCSlib/Complexity/RAMSimulation/Classes.lean` | `WordRAM` | about 195 |
| `NDSlice` A | appended to `TCSlib/Complexity/TuringMachine/Nondeterministic.lean` | `Turing.NDTM` | +25 |
| `NDSlice` B | appended to `TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean` | `Turing.NDTM` | +20 |
| `LanguageExtensions` 1 | edits of six vendored files (table in the file) | `Light`, `Light.Compiler` | (the PROG-2 edit set) |
| `LanguageExtensions` 2 | new `TCSlib/Programs/Light/InputOutput.lean` | `Light` | about 300 |
| `LanguageExtensions` 3 | nothing (mirror-only bridges) | — | — |

**Why one elaboration unit holds six parts.** A file elaborated against the snapshot can import
only modules that already exist, and each later part of `Stage2` uses declarations of an earlier
one, so the parts share one file, as the RD-2 draft did. Landing is a cut at the `-- @landing`
markers: each part becomes its module with the copyright block, the imports its `-- @imports`
lines list, the standard options, and the part verbatim. No declaration changes. The cut is
checked: each landing module's import closure is elaborated on its own (log §2), by the method of
`scripts/vendor_afm26/closurecheck.py`.

**Why these homes.**
- **The wrapper sits in the WordRAM topic, below the compiler** (Part A). Under the wrapper
  decision, PROG-2's edited compiler emits `rdIn`, `emit`, `coin` and `half`, so its code becomes
  `List XInstr` (NOTES Q1) and the vendored compiler must import the module that defines
  `XInstr`. That module therefore cannot import the compiler, nor anything heavy: Part A imports
  only `TCSlib.Programs.WordRAM.Steps` and `Mathlib.Data.Finset.Card` (log §2). The drafts put
  `XInstr` in the same file as `haltsWithin_compileProgram`, which imports the compiler; after
  PROG-2 that would be an import cycle. The name is `Extended.lean`, not `Footprint.lean`: the
  vendoring map would send upstream's deferred `Machine/Footprint.lean` (PROG-1(e)) to
  `TCSlib/Programs/WordRAM/Footprint.lean`.
- **PROG-3's compiler level is a local modification of two vendored files** (B1, B2), because its
  proofs run through private lemmas: the case lemmas `sim_skip` … `sim_call` and `codeAt_*`
  (`Simulation.lean:70-437`), `setting`, `start_mainStmt`, `not_mem_of_far`, `steps_tail`
  (`WholeProgram.lean:82-198`), and the footprint twins they need of private segment lemmas
  (`effects_compileExpr`, `Expressions.lean:128`; `steps_dispatcher_pair`, `Dispatcher.lean:72`;
  and others). The alternatives are a new file plus a vendored edit that makes them public (a
  larger diff), or re-deriving them (duplication, which policy §1 requires the human to approve).
  `haltsWithin_compileProgram` goes with them (B2): it is `compileProgram_footprint` in stage 2's
  vocabulary, and placing it there keeps the stage-2 machine modules free of the compiler.
- **The stage-2 machine and its corollaries are a new Complexity topic, `RAMSimulation`** (C, D,
  E, with a facade `TCSlib/Complexity/RAMSimulation.lean` imported by `TCSlib.lean`). Today
  nothing in `TCSlib/Programs` imports `TCSlib/Complexity`, and only `ComputationalModels.lean`
  and the root `TCSlib.lean` import `TCSlib.Programs` (grep). Stage 2 needs the machine library
  (`Build/`), and its corollaries need the class definitions, so it belongs on the Complexity
  side, where the precedent program layers and their machine compilers live
  (`TuringMachine/CounterProg.lean`, `CounterProgRun.lean`; `SpaceComplexity/CounterProgSim.lean`,
  `CounterProgSimRun.lean`). It is a topic of its own, like `CookLevin`, because it is one
  theorem cluster consumed by several class topics. The split follows policy §1's
  layering: the word-size notion (C), the simulation (D), and the corollaries (E), so that a
  consumer of `WordSizeComputable` does not import the simulation.
- **Namespace `WordRAM`** for A, C, D, E: policy §1's model-registry rule puts a registered
  model's operations and lemmas in the model's own namespace, and `WordRAM.Instr` is registered
  (`ComputationalModels.lean:87`). The names read accordingly: `WordRAM.exists_simulation`,
  `WordRAM.mem_LOGSPACE_of_decides`.
- **The slice lemmas** go next to what they generalize: `Turing.MultiTapeTM.toNDTM_runWith`
  (`Nondeterministic.lean:251`) and `Turing.MultiTapeTM.toNDTM_spaceUsedWith`
  (`NondeterministicSpace.lean:146`), the special case where the two transition functions agree
  everywhere.
- **PROG-2's new declarations** go to a new non-vendored `TCSlib/Programs/Light/InputOutput.lean`.
  Its one import outside `TCSlib/Programs` is `TCSlib.Complexity.Randomized.Classes`, for
  `Randomized.randProb`; that module imports only Mathlib (grep), but it would be the Programs
  area's first import from Complexity (brief point 12).

**Landing obligations** (outside the audited statements; listed so that none is forgotten):
`TCSlib/Programs/WordRAM.lean`, `TCSlib/Programs/Light.lean` and `TCSlib/Programs.lean` import
the two new Programs modules, which `scripts/vendor_afm26/facades.py` generates today, so the
generator learns them or the facades stop being generated; the new facade
`TCSlib/Complexity/RAMSimulation.lean` and its line in `TCSlib.lean`; the repository `NOTICE`'s
list of non-vendored files under `TCSlib/Programs/` gains `WordRAM/Extended.lean` and
`Light/InputOutput.lean`; the headers of the vendored `Simulation.lean` and `WholeProgram.lean`
list B1 and B2 as local modifications, made by the vendoring scripts; `ComputationalModels.lean`
gains an entry for `WordRAM.XInstr` (programs `WordRAM.XProgram`) and a Conversions pointer to
`WordRAM.exists_simulation` (its "nine instructions" stays true under the wrapper); design §15d's
`startMem` becomes `initMem` (below).

## What the files state (verify)

**`Stage2` Part A, the extended RAM** (`WordRAM`):
- `XInstr`: `base (i : Instr)`, `rdIn i j`, `emit i`, `coin i`, `half i j`. `XCfg W extends Cfg W`
  with `out : List Bool` and `rd : ℕ`. `xstep P x ρ c : XCfg W ⊕ Bool`: the vendored arms (the six
  straight-line ones through `WordRAM.effect`), reject past the end; `rdIn` writes `inBitWord`
  (`1` iff `0 ≤ p` and `x[p] = true`); `emit` appends `decide (m i ≠ 0)`; `coin` writes
  `coinWord (ρ.getD rd false)` and increments `rd`; `half` writes `(m j).sshiftRight 1`.
- `XSteps`, `CoinFree`, `XProgram.proj` (new instructions ↦ `reject`); `XSteps.trans`,
  `xstep_map_base`, `XSteps.of_steps`, `XSteps.of_steps_proj`.
- Footprints: `baseTouches` (the named cells, plus `(m j).toInt` for `load` and `(m i).toInt` for
  `store`), `XInstr.touches`, `XInstr.card_touches_le` (`≤ 3`); `StepsIn P K n c c'` and
  `XStepsIn P x ρ K n c c'` (every step's touched set `⊆ K`); `toSteps`, `exists_stepsIn` and
  `exists_xStepsIn` (a footprint of at most `3 n` cells), `mono`, `trans`, `agreeOutside` (every
  intermediate memory agrees with the first outside `K`), `stepsIn_straight`,
  `XStepsIn.of_stepsIn_proj`.
- Halting: `initMem W n` (cell `-1` holds `wd W n`, all others `0`), `XCfg.init`,
  `HaltsWithin P x ρ W t v o f` := some `n < t`, configuration `c` and `K : Finset ℤ` with
  `K.card ≤ f`, an `XStepsIn` run of `n` steps from `XCfg.init W |x|` to `c`, `xstep … c = .inr v`
  and `c.out = o`. `HaltsWithin.mono`, `.touches_le` (`f := 3 t`), `.unique`, `.coin_irrel`.

**`Stage2` B1, B2, PROG-3 for compiled code** (`Light.Compiler`): `Touchable Z q := Writable Z q ∪
Constants Z.disp`; `FinishedIn` extends `Finished` by `runIn : StepsIn S.code (Touchable S.toSizes
q) n ⟨pos, m⟩ ⟨pos + s.size S.F, m'⟩`; `sim_in` (the hypotheses of `sim`, conclusion
`FinishedIn`); `region P dec lim := Finset.Ico (-lowCell) lim.space` and `card_region`;
`compileProgram_footprint` (the hypotheses of `compileProgram_correct`; some `n < ramSteps P dec c`
and `cfg` with a `StepsIn` run of the compiled program within the region from `⟨0, m⟩` to `cfg`,
the verdict step, and `Outcome`); `haltsWithin_compileProgram` (a light run of `mainStmt p0` on
`frame [0, |x|, 0]` and the zero memory, `Fits`, `|x| ≤ lim.word` ⟹ `HaltsWithin
((compileProgram P p0 dec).map .base) x ρ W (ramSteps P dec c) (verdictOf …) [] (lowCell +
lim.space)` for every `ρ`). These are stated for the compiler as vendored (`List Instr` code).

**`Stage2` C, the word size** (`WordRAM`): `WordSizeComputable W TW SW := ∃ M : FinTM Bool, ∀ x,
∃ t ≤ TW |x|, M.ComputesInTime x (W |x|).bits t ∧ M.tm.spaceUsed (M.tm.initCfg x) t ≤ SW |x|`;
`.mono`; `wordSizeComputable_logSpace c : ∃ a, WordSizeComputable (c·logSpace) (a·(n+1))
(a·logSpace)`; `wordSizeComputable_of_spaceConstructible : SpaceConstructible S → ∃ a TW,
WordSizeComputable (c·S) TW (a·S)`.

**`Stage2` D, stage 2** (`WordRAM`), with `simTime A TW n W t f = TW n + A·(t+1)·(f·(W+1) + W² +
n + 1)` and `simSpace A SW n W f = SW n + A·(f·(W+1) + W + logSpace n + 1)`:
- `exists_simulation P fn hW : ∃ M A, ∀ x t f v o, HaltsWithin P x [] (W |x|) t v o f →
  M.ComputesInTime x (outputOf fn v o) (simTime …) ∧ M.tm.spaceUsed (M.tm.initCfg x) (simTime …)
  ≤ simSpace …`, where `outputOf fn v o = if fn then o else [v]`;
- `exists_ndSimulation P hW : ∃ N A, ∀ x t f, (∀ ρ, ∃ v o, HaltsWithin P x ρ (W |x|) t v o f) →
  N.tm.HaltsWithin x T ∧ (∀ w, |w| = T → N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ simSpace …) ∧
  (N.AcceptsWithin x T ↔ ∃ ρ o, HaltsWithin P x ρ (W |x|) t true o f)`, `T = simTime …`.

**`Stage2` E, the corollaries** (`WordRAM`): `mem_DTIME_of_decides`, `mem_P_of_decides`,
`mem_P_of_decides_logWord`, `mem_SPACE_of_decides`, `mem_LOGSPACE_of_decides`,
`computesInSpace_of_computes`, `mem_SPACE_mul_of_decides`, `mem_NSPACE_of_accepts`,
`mem_NL_of_accepts`. Each sketch states its constant.

**`NDSlice`** (`Turing.NDTM`): if every configuration of the slice `tm.fixChoice b`'s run from
`cfg`, at the times `j < |w|`, is halted or in a state `q` with `tm.tr false q = tm.tr true q`,
then `tm.runWith w cfg = (tm.fixChoice b).runFrom cfg |w|`
(`runWith_eq_fixChoice_runFrom`), and `tm.spaceUsedWith w cfg = (tm.fixChoice b).spaceUsed cfg
|w|` (`spaceUsedWith_eq_fixChoice_spaceUsed`).

**`LanguageExtensions`** (`Light`; landing names drop the `X`): `XStmt` (the seven constructors
and `inBit x e`, `emit e`, `coin x`, `half x e`), `XLimits extends Limits` with `input`,
`inBitVal`, `XExec lim P d s σ σ' o r c` (13 rules; `seq` and `whileTrue` concatenate `o` and `r`,
`call` passes them through; costs `e.cost + 1` for `inBit`, `emit`, `half` and `1` for `coin`),
`XStmt.assigns`, the four restated inductions (`append`, `loc_eq_of_notMem_assigns`, `bounded` with
the new hypothesis `1 ≤ lim.word`, `mem_outside`), `XEnds` (type unchanged, `∃ σ' o r c`),
`xmainStmt`, `Compiler.XFits` (adds `|lim.input| ≤ lim.word`); new: `coins_length_le`,
`output_length_le`, `det`, `XStmt.IOFree`, `io_eq_nil_of_ioFree`, `EndsIO` (a run whose consumed
word is a prefix of `ρ`), 15 rules (`toXEnds`, `mono`, `of_xEnds_ioFree`, one per statement,
`XEnds.coin`), `MeetsIO`, `EndsIO.callLast`, `AcceptsND` (some stream of length `T`), `acceptProb`
(`randProb m`); mirror only: `XStmt.ofStmt`, `XExec.ofExec`, `EndsIO.ofEnds`.

## Changes from the drafts (verify against log §8)

The comment-stripped statements were compared with the drafts' (log §8): `Stage2Draft` 49
identical, 5 changed, 2 added; `ExtensionsDraft` 37 identical, 1 changed (binders only), 3 added.
1. **Namespaces.** `TCSlib.Draft.Stage2` becomes `WordRAM` (A, C, D, E) and `Light.Compiler`
   (B1, B2); `TCSlib.Draft.Stage2.Lang` becomes `Light`, with `XFits` as `Light.Compiler.XFits`.
2. **`startMem` is renamed `WordRAM.initMem`, and writes cell `-1` literally.** The vendored
   compiler declares `Light.Compiler.startMem` (`StartUp.lean:198`) and its files `open WordRAM`
   (`Simulation.lean:56`, `WholeProgram.lean:59`, `StartUp.lean:48` and others), so once they
   import the wrapper an unqualified `startMem` would be ambiguous there; the literal `-1` (the
   compiler's `cARG1`, `StatementCode.lean:82`) avoids importing the compiler from below it.
3. **`haltsWithin_compileProgram` moves** from the stage-2 file to B2 (homes above).
4. **Footprint counts.** `Steps.exists_stepsIn` and `XSteps.exists_xStepsIn` now give a footprint
   of at most `3 n` cells; new `XInstr.card_touches_le` and `HaltsWithin.touches_le`.
5. **`mem_P_of_decides` and `mem_P_of_decides_logWord` drop `f ≤ C·(n + 1)^d`**, which follows
   from `HaltsWithin.touches_le` (a run of `t` steps touches at most `3 t` cells). The P grade so
   needs no footprint reasoning from its consumers.
6. **New `NDSlice`**: the slice lemma that NOTES §3.9 names and design §15d records as needed,
   with its space companion.
7. **New in the mirror: `XStmt.IOFree`, `XExec.io_eq_nil_of_ioFree`, `EndsIO.of_xEnds_ioFree`.**
   The drafted bridge `EndsIO.ofEnds` is stated through `XStmt.ofStmt`, which has no meaning after
   the in-place edit (one `Stmt` type). The post-edit form needs the statement and every procedure
   of the program to be free of `emit` and `coin`.
8. **The mirror is in three parts** (edits, new declarations, mirror-only bridges) with a landing
   table; `EndsIO.ofEnds` moved out of the `Rules` section, so its binders are explicit.
9. **Documentation.** Every sorried theorem has a proof sketch (the policy lint checks it, log §4);
   [AFM26] design-adaptation entries in the policy §2 form (full commit, date, licence, upstream
   paths); corrected citations: the draft's `Simulation.lean:284` for `sim` is `:483`;
   `Logic.lean:78-80` for `Ends` is `:94`, and `Logic.lean:62` for `Exec.append` is `:78`;
   `StartUp.lean:256` is `:254`; `computesInSpace_of_computes` now cites [AB09, Definition 4.16,
   Exercise 4.8] and declares its deviation (no polynomial bound on `|g x|`); the
   nondeterministic form and the NL grade cite [AB09, §4.3.1, Definition 4.19] (read-once
   certificates); `acceptProb` cites [AB09, §7.1] (the draft had "Def 7.2", and
   `Randomized.randProb` cites "Def 7.4"; chapter 7's text is not in the bundle, so the
   auditor's copy decides).
10. **Sketches made specific**: stage 2's start-up through the R1 silent embedding
    `Turing.embedSilentTM` and dispatch through `Turing.phaseHostTM`; the alphabet question (point
    11 below); the fill's dependence on MIG-0a's `Turing.Contract`; the bridges' routes (R8.5c,
    the B3a machine, `computesFunInTime_lengthBits_spaceUsed`).

## The PROG-2 edit list, re-verified (grep, then read; line numbers at commit `d63c7159`, unchanged at the bundle's commit)

NOTES §5's tables are confirmed site by site, with four corrections and additions.

**`Stmt`: four new constructors at each site.**

| Site | Kind | Status |
|---|---|---|
| `Light/Syntax.lean:80` `inductive Stmt` (`deriving Repr`) | the type | confirmed |
| `Compiler/StatementCode.lean:205` `Stmt.size` | match, 7 arms | confirmed |
| `Compiler/StatementCode.lean:215` `compileStmt` | match, 7 arms | confirmed; its result type changes too (below) |
| `Compiler/StatementCode.lean:287` `length_compileStmt` | induction (`:289`) | confirmed |
| `Compiler/StatementCode.lean:337` `Stmt.width` | match | confirmed |
| `Compiler/StatementCode.lean:361-375` `Stmt.width_*_le_iff` | one lemma per non-`skip` constructor (6 today) | confirmed; 4 new |
| `Light/Assigns.lean:44` `Stmt.assigns` | match | confirmed (mirror `XStmt.assigns`) |
| `Light/Rules.lean:154` `Ends.of_blockSafe` | exhaustive term match, 7 arms | confirmed; 4 new arms |
| `Light/Rules.lean:64, 73, 81` `Stmt.after`, `blockCost`, `BlockSafe` | wildcard | confirmed: new statements are non-blocks unless the edit decides otherwise |
| `Compiler/Simulation.lean:70-104` `codeAt_set/seq/ite/while/call` (private) | one per constructor with code | confirmed; 4 new |

**`Exec`: four new rules, and the indices `o`, `r`.** Exactly six files name `Exec` (grep:
`Syntax`, `Logic`, `Assigns`, `RunsStayInLimits`, `Compiler/Simulation`, `Compiler/WholeProgram`);
`Rules.lean` uses its constructors without the name.

| Site | Kind | Status |
|---|---|---|
| `Light/Syntax.lean:155` `inductive Exec` | the type | confirmed |
| `Light/Logic.lean:78` `Exec.append` | induction | confirmed |
| `Light/Logic.lean:94` `Ends`, rules `:99-224` | witnesses (option A) | **corrected count**, below |
| `Light/Assigns.lean:54` `Exec.loc_eq_of_notMem_assigns` | induction | confirmed |
| `Light/RunsStayInLimits.lean:83` `Exec.bounded` | induction, new hypothesis | confirmed |
| `Light/RunsStayInLimits.lean:99` `Exec.mem_outside` | induction | confirmed |
| `Compiler/Simulation.lean:483` `sim`; `Start` `:167`, `Finished` `:182`; `sim_*` `:223-437` | induction, 4 new cases, indices threaded | confirmed |
| `Light/Rules.lean:191, 193, 205, 207, 275, 278` | `cases` on `Exec` | confirmed (valid under option A) |
| `Compiler/WholeProgram.lean:241` `compileProgram_correct` | takes `Exec` | confirmed; its full name is `Light.Compiler.compileProgram_correct`, not NOTES' `Light.compileProgram_correct` |

**Correction 1: the `Ends` witness lines are 38, not 32.** Lines that build or take apart an
`Ends` witness `⟨σ', c, …⟩`: `Logic.lean` 28 (101, 102, 107, 108, 111, 115, 121, 126, 127,
133–136, 142, 143, 148, 166, 169–171, 200, 202, 206–208, 214, 223, 224), `Rules.lean` 8 (190,
194, 204, 208, 274, 276, 277, 279), `Assigns.lean` 2 (74, 75). NOTES gives 22 for `Logic`, a
regex estimate; the list above comes from reading `Logic.lean:93-224` line by line.

**Correction 2: under the wrapper the compiler's code type changes**, which NOTES' Q1 says
("the compiler's code type becomes `List XInstr`") but §5's tables do not list. The sites that fix
the code type to `List Instr`: `StatementCode.lean:215` (`compileStmt`'s result; `compileExpr`
`:136`, `callCode` `:198`, `epilogue` `:233` and `dispatcher` `:241` can stay `List Instr` and be
lifted by `.map .base`); `ProgramCode.lean:116` `bodiesCode`, `:147` `mainCode`, `:156`
`compileProgram`, `:261` `codeAt_bodies`; `Simulation.lean:66` (the section variable), `:123`
`Setting.code`, `:170` `Start.codeAt`, `:184` `Finished.run` (a `Steps` run, to become an `XSteps`
run, the vendored segment lemmas applying to `S.code.proj` through `XSteps.of_steps_proj`);
`WholeProgram.lean:75` `Verdict`, `:82` `steps_tail`, `:245` (`exec` of the compiled program).
By grep, `List Instr`, `: Instr`, `code :` and `CodeAt` occur in `Cells` 4, `Conditions` 8,
`Dispatcher` 7, `ProgramCode` 21, `Simulation` 27, `StatementCode` 10 and `WholeProgram` 5 lines
(an estimate of the touched surface, not a list of edits).

**Correction 3: the `Instr` table is void under the wrapper.** `WordRAM/Basic.lean:40, 53`,
`WordRAM/Steps.lean:116, 163, 244, 249, 271, 412, 417, 420` stay byte-identical (confirmed: no
part of the proposed files edits them). `ComputationalModels.lean:87`'s "nine instructions"
stays true; the registry instead gains `WordRAM.XInstr`.

**Addition: PROG-3's footprint twins** live in the vendored compiler too (homes above): of
`steps_jump` and `steps_setVar` (`Cells.lean:329, 334`), the test code (`Conditions.lean:62-95`,
`decides_compileCond` `:158`), the dispatcher (`Dispatcher.lean:72-109`), the expression and
frame code (`Expressions.lean:128` private, `:176`; `CallFrames.lean:56, 93, 122`), and the
start-up (`StartUp.lean:254`). They are fill-time helpers, not gated statements.

Not affected (confirmed): the `Expr`, `Cond` and `Op` inductions
(`Compiler/Expressions.lean:52, 132`, `Conditions.lean:161`, `StatementCode.lean:118`); `Lib/`,
`Frames.lean` and `Calls.lean` neither match on `Stmt` or `Exec` nor destructure `Ends`
witnesses; `Tactics.lean` drives the `Ends` rules, whose statements do not change. No vendored
file constructs a `Limits` (grep for `Limits.mk`, `{ word :=` and `: Limits :=`: no
construction), so the field `input` breaks nothing.

## Brief for the auditor

Restate every definition in your own words before reading its docstring, argue each sorried
theorem true in 2–5 sentences or exhibit a counterexample, and attempt at least five adversarial
instantiations (failure modes 1–4 of `audits/TEMPLATE.md`). Points to rule on:

1. **Fidelity of the bound shapes to the code**, including the three corrections to §15a that
   §15d records.
   - *No separate address width.* Check `WordRAM/Basic.lean:62-63` (`load` reads `m (m j).toInt`,
     `store` writes at `(m i).toInt`). A touched address is either a word's value (`W` bits) or
     an immediate operand of `P`. Is `f·(W + 1)`, with `A` absorbing the immediates' width, right
     when an immediate exceeds `2^W` (for example `.one (2^100)` with `W = 8`)?
   - *A linear seek.* Check `Build/InputCall.lean:270-310`: `C·(|w| + pos + p + 1)` steps, work
     envelope `C·(|w| + 1)`, and the precondition `p ≤ |x| + 1`, which the range test supplies.
     Is the per-step term `n` right, with the seek's `pos` the previous input position?
   - *The word size charged once*, as `TW n` and `SW n`.
   - Beyond them: is `W²` (shift-and-add) the right multiplication term on a multi-tape machine;
     is `(t + 1)` right (`HaltsWithin` counts the verdict step, and the start-up's `O(n + W²)` is
     absorbed because `t ≥ 1`); is the `W` in the space bound enough for the unary ruler and the
     scratch words; is the `logSpace n` term enough for the length copy?
2. **`WordSizeComputable` and its bridges.** Is it the right hypothesis (binary output as in
   `SpaceConstructible`; halting within `TW`; work space up to that time `≤ SW`)? The stage-2
   machine copies the output, `|bits W| ≤ W + 1` cells, onto a work tape at its own cost: is that
   absorbed by `A·W` in every case, `W = 0` included? Bridge 1: its time `a·(n + 1)` relies on a
   machine whose existing version (`b3a_log_machine`, `SpaceComplexity/Constructible.lean:329`,
   private) states space only; is the claim right? Bridge 2: `TW` is uncontrolled. Confirm that no
   consumer of the `c·S` word size needs a time bound (`mem_SPACE_mul_of_decides` does not).
3. **The nondeterministic form.** The hypothesis is uniform: one `t` and one `f` for every stream
   `ρ`, all lists, so that streams that run out read `false`. Acceptance is "some stream gives
   `true` within `t` and `f`". Check both against `Turing.FinNDTM.AcceptsWithin` (output exactly
   `[true]`, `ClassNP/NTIME.lean:93`), `Turing.NDTM.HaltsWithin` (all branches,
   `Nondeterministic.lean:190`), `Turing.FinNDTM.DecidesInSpace` (a per-input budget,
   `SpaceComplexity/NSPACE.lean:78`) and [AB09, §2.1.2, Definition 4.1]. Is uniformity in `ρ` too
   strong for C2's programs (a run on a bad stream must still stop within `t`), or exactly what
   NSPACE needs? Is there a gap between "each `coin` is one choice step, every other state has
   equal transitions" and the stated space clause over *all* branches of length `T`?
4. **The logspace grade.** `O(1)` cells and `W = c·logSpace` give `LOGSPACE` because the input
   is read in place and the output tape is not counted (`Turing.FinTM.ComputesInSpace`,
   `SpaceComplexity/Basic.lean:100`). Check the arithmetic in `mem_LOGSPACE_of_decides` and
   `mem_NL_of_accepts`, and that nothing in stage 2's space bound grows with the input except
   `logSpace n` and `SW`.
5. **The footprint statements.** Do `baseTouches` and `XInstr.touches` list every cell a step reads
   or writes (compare `WordRAM.step`, `Steps.lean:116-129`)? `stepsIn_straight`'s hypothesis
   quantifies over all memories, so for `load` and `store` it forces `K` to contain every
   address; is the row stated usefully, or should it take the run's memories? Is
   `Touchable = Writable ∪ Constants` enough for every read of compiled code, the epilogue's read
   of the return slot `cStack (q + F)` from the callee's frame `q + F + 1` and the variables'
   FP-relative loads included (`StatementCode.lean:136-241`)? Are `card_region`,
   `compileProgram_footprint`'s `n < ramSteps` and `haltsWithin_compileProgram`'s use of `Input`
   right? Is "touched" (user decision) consistent with the table bound, which needs only written
   cells?
6. **Wrapper versus in place.** The wrapper keeps `WordRAM/` byte-identical and reuses the
   vendored run calculus through `XProgram.proj`. It costs the compiler's code type (correction 2)
   and makes the vendored compiler import a non-vendored module. In place would break about 50
   anonymous `Cfg` literals (NOTES Q1, a regex estimate). The user decided; verify that the trade
   is stated fully, and report any consequence that the decision record misses.
7. **The corollaries.** For each of the nine, check that it follows from `exists_simulation` or
   `exists_ndSimulation` as stated, with the constants its sketch gives. In particular:
   `mem_P_of_decides` without a cell bound (through `HaltsWithin.touches_le`), with
   `T' n = (n + 1)^(3d + 1)`; `mem_SPACE_mul_of_decides` (needs `S ≥ 1`, from `logSpace ≤ S`);
   `computesInSpace_of_computes` against [AB09, Definition 4.16] (no polynomial length bound;
   declared).
8. **The `Exec` edit list's completeness.** Check the re-verified tables and the four corrections
   above against the vendored files. Is anything still missing: a site that matches on `Stmt` or
   inducts on `Exec`, a definition that fixes the code type, a lemma that destructures `Ends`?
9. **The nondeterministic slice lemma.** Are `runWith_eq_fixChoice_runFrom` and
   `spaceUsedWith_eq_fixChoice_spaceUsed` true as stated, `j < |w|` with the halted case
   included? Are they the form that `exists_ndSimulation`'s fill needs, with the stage-2 machine
   as the slice `N.tm.fixChoice false`? Should MIG-0b's contract-level variant be stated now?
10. **PROG-2's mirror.**
    - Is `XExec.det` true as stated (both consumed words prefixes of one `ρ`)?
    - Does `EndsIO` give the intended "for a fixed stream" reading, and is it right that a coin
      under too short a stream has no run (probe: no `EndsIO` for a coin under `[]`)?
    - Is the rule set complete enough for C2? There are no `EndsIO` counterparts of the
      loop-invariant rules `Ends.while`, `whileConst`, `whileVariant` (`Logic.lean:152-215`);
      they are derivable from `whileStep` and `whileDone`.
    - Is `XEnds.coin`'s existential reading safe for the 14 routines (they have no coins)?
    - `Exec.bounded` gains `1 ≤ lim.word`. Is `Compiler.XFits` redundant, as NOTES says, given
      `Input.arg1_le` (`WholeProgram.lean:216`)?
    - Should `inBit` and `half` be blocks (`Rules.lean:64-88`)?
    - Is `acceptProb` (runs needing more than `m` coins count as rejecting) the right probability?
11. **The alphabet.** The sketch builds the machine over `Bool` with fixed-width fields measured by
    the ruler. A richer alphabet would need a per-input alphabet reduction: the public
    `Turing.FinTM.alphabet_reduction` (`Robustness/AlphabetReduction.lean:586`) has
    length-indexed bounds, its per-input core `arTM_computes` (`:546`) is private, and there is
    no nondeterministic variant. Is the `Bool` route credible for the find-by-key and
    multiplication rows, or should this be a recorded fill obligation?
12. **Homes, names and sequencing.** Rule on the homes above, the topic name `RAMSimulation`, the
    namespace `WordRAM` for the Complexity-side modules, and `initMem`. PROG-3's compiler-level
    statements are stated for the vendored compiler, and PROG-2's code-type change restates them
    over `XStepsIn`. Should they land before PROG-2 (and be re-gated with it), or only with it?
    Stage 2's fill depends on MIG-0a (`Turing.Contract`) and on the slice lemmas. Should
    `acceptProb` move to the Complexity side, so that `TCSlib/Programs` keeps importing nothing
    from `TCSlib/Complexity`?
13. **Documentation and policy** (`policy.md`): module headers, statement prose, attribution
    ([AFM26] design adaptation; [AB09] locations), a literal proof sketch on every sorried
    theorem, deviations declared, 100-column lines.
14. Report anything else that the files, this pack, design §15d or NOTES misstate, in the table.

## Repository-side attestations (verify or challenge)

Source facts (checkable in the bundle) are separated from maintainer execution claims (the log).
- **Elaboration** (log §1): each of the three files, elaborated read-only against the snapshot
  `oleans-f7` (Lean `v4.25.0`), gives exit 0 and 0 errors. The only warnings are
  `declaration uses 'sorry'`: 36 (`Stage2`), 2 (`NDSlice`), 27 (`LanguageExtensions`).
- **The maintainer's re-check.** The maintainer re-elaborated, independently and with the same
  tool and snapshot, the three files, the six cut files, both probe files and the three negative
  controls: the same counts (each negative control fails with exactly one error, a `decide`
  refutation). A separate maintainer script checked that each cut file is the copyright block,
  its imports, the standard options and its closure's parts, verbatim and in file order.
- **Cut checks** (log §2): each of `Stage2`'s six landing modules, in exactly its own import
  closure, gives 0 errors: `Extended` 18 sorries, the `Simulation` edit 19, the `WholeProgram`
  edit 22, `WordSize` 3, `Simulation` 23, `Classes` 32 (each count includes its closure). The
  file's own imports are exactly the union of the parts' imports.
- **Semantic probes** (log §3): 24 `example`s over `Stage2` and 15 over `LanguageExtensions`
  check the definitions by `rfl`, `decide` or short proofs. They cover accept, reject and
  rejection past the end; `emit` of a zero and a nonzero cell; `rdIn` on the input, off it and at
  a negative position; `coin` with a stream, with an empty one, and its count; `half` at `-3` and
  `5`; `bltz`; an `add` through `effect`; a satisfiable `HaltsWithin`; the projection; `touches` of
  a `load`; the output modes; the bounds at a point; `XExec` derivations of a coin then an emit,
  for both bits; `inBitVal`; an `EndsIO` instance; I/O-freeness. Adversarial cases: a rejecting
  program never accepts; nothing halts within 0 steps; a coin has no `EndsIO` run under the empty
  stream. Three negative controls (a false `emit`, `half` and `inBitVal` value) each fail with 1
  error.
- **Style lint** (log §4): `scripts/campaign_style_lint.py` over the three files: 0 FAIL; 1 WARN,
  `Stage2` at 1024 lines, an elaboration unit whose largest landing module is about 400 lines.
- **Line widths** (log §5): no line over 100 characters.
- **Names** (log §6): 103 declarations, no full-name clash with any declaration of `TCSlib`, and no
  `WordRAM` short name that is also the last component of a `Light` or `Light.Compiler`
  declaration, which matters because the vendored compiler files `open WordRAM`. A positive
  control (the draft's `WordRAM.startMem`) is caught.
- **Cited names** (log §7): every backticked identifier in the files' comments was `#check`ed.
  Those that do not resolve are bound variables, module names, the vendored private lemmas (cited
  as private), names proposed in another unit or not landed in the snapshot (`Turing.Contract`,
  MIG-0a, landed since by PR #83; `oleans-f7` predates it), the
  mirrors' landing names, and names in modules that the unit does not import
  (`Turing.exists_inputSeekTM`, `Build/InputCall.lean:294`; `Light.mainStmt`,
  `ProgramCode.lean:77`; `Light.Compiler.Input.arg1_le`, `WholeProgram.lean:216`).
- **Draft correspondence** (log §8): as listed under "Changes from the drafts".
- **Nothing in the worktree was changed.** The files were written to a scratch directory, no git
  command and no `lake` command was run, and no olean was written.
- **Upstream's footprint file.** `audits/evidence/stage2-gate/upstream-Footprint.lean.txt` is a
  byte copy of upstream's `ThreeSumApsp/Machine/Footprint.lean` (129 lines; not vendored,
  PROG-1(e); SHA-256
  `0d6c6b09c4fa276671e2116246767aee9c478c7d72adfc49838c55fe015588f9`). It was taken from a
  scratch copy of the upstream tree whose `Machine/Steps.lean` and `Lang/Syntax.lean` match the
  SHA-256 recorded in `audits/evidence/programs-vendor/upstream-manifest.md`, so presumably at the
  pinned commit; without git this was not confirmed. It proves `step_mem` (a step changes at most
  one cell), `changed_cells` (a run of `t` steps changes at most `t` cells), `exec_congr` (it
  reads at most `2 t` cells) and `exec_unique`. Those are counts, not footprints within a given
  set: porting it would give a count like `HaltsWithin.touches_le`'s `3 t`, enough for P but not
  for L. So it complements `StepsIn` and does not replace it, which answers NOTES §4's open
  question.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/stage2-statements-findings.md`. The gate closes when a round reports zero blockers and
zero majors; the parts then land as cut (homes as ruled), and PROG-2's scripted edit is checked
against `LanguageExtensions` at its own fidelity gate.
