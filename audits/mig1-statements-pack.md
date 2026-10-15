# External audit pack — MIG-1, named witnesses for the existential machine rows (statement gate)

Campaign: the machine-library migration (`machine-library-design.md` §2, §16; backlog MIG-1, with
MIG-9, MIG-11, MIG-17, MIG-20), under the Arora-Barak chapters 3-4 plan. MIG-1 gives every
existential machine row of eight library files a **named public witness with spec theorems**,
makes each row a short corollary with its statement unchanged, deletes the 304 private `f2_`
copies (with the 45 `a2_` and 7 `catalog_redirect*` declarations) from `Build/Catalog.lean`, and
retires the six R3 canonical `_run` rows. The design and the measured inventory are
`audits/evidence/mig1/MIG1-design.md` and `MIG1-inventory.md`; the statement draft that this gate
completes is `audits/evidence/mig1/MIG1Draft.lean.txt`.

**This gate audits statements and definitions only.** The 26 witness definitions have their real
bodies; every spec theorem whose proof needs a private lemma is `sorry` under a proof sketch that
names the existing proof; the rest are proved. Nothing is landed. Files under audit:

| File (bundle path) | Content |
|---|---|
| `audits/evidence/mig1/gate/MIG1Statements.lean.txt` (2,950 lines) | **the unit**: eight parts, one per home file, each with its `-- @landing` module and `-- @imports` |
| `audits/evidence/mig1/gate/SpecProbe-tail.lean.txt` (1,162 lines) | **spec probe**: the unit followed by this tail proves 20 of the 31 sorried specs from verbatim statements of proved private lemmas |
| `audits/evidence/mig1/gate/BridgeProbe.lean.txt` (321 lines) | **bridge probe**: the old Catalog loop host is definitionally today's controller; four Catalog lemmas restate public ones |
| `audits/evidence/mig1/gate/data/deletion-plan.tsv` | **the deletion plan**: all 378 region declarations with source, identity, fate and new name |
| `audits/evidence/mig1/gate/data/r3-retirement.tsv` | the R3 retirement: six rows, five code citations, nine docstring mentions |

Supporting evidence: logs `audits/logs/mig1-statements-{elaboration,cutcheck,identity,axioms,
names,consumers,replay}.log`; scripts and manifests under `audits/evidence/mig1/gate/scripts/`
(`runall.sh` rebuilds the unit and the probes from their templates and reruns every check);
`audits/evidence/mig1/gate/AxiomProbe-tail.lean.txt`; `data/moved-names.json`; `data/consumers.json`
(every citation of the 63 measured names, by file and line).

**Bundle:** `audits/mig1-statements-bundle.md`: this pack, `audits/TEMPLATE.md`, `policy.md`,
`workflow.md`, the design document and the backlog, the files under audit, the logs, the MIG-1
design, inventory and draft, the H2 step-block draft (one shared lemma), and every library file
whose rows or bodies are involved (`BUNDLE-FILES.txt`; what is not bundled and why:
`BUNDLE-MISSING.txt`).

**Provenance (maintainer).** A maintainer sub-agent built and checked the files against the
read-only checkout `wt-g5mig1` at campaign commit `1781a230d2410ae2a09fbb961fe644512a6ba3c0`
(fills-8, PR #84; the hash is read from the worktree's git metadata file, not typed), with the
olean snapshot `oleans-f8` of that commit and Lean `v4.25.0` (the toolchain file). The work
started at `385d6e5a` with the snapshot `oleans-r8`; every result reported here was re-run at
`1781a230`. The MIG-1 inventory measured at `6aa9f67b`. Between `6aa9f67b` and `1781a230` the
eight files (and `Build/CertShell.lean`) are byte-identical (`diff` of the two checkouts); the Lean
changes are `SpaceComplexity/Hierarchy.lean`, the new `Build/Contract.lean` with its facade line,
`Build/RecordTable.lean` and `TuringMachine/CodeSimulator.lean`. RecordTable's new private
declarations cite none of the 63 names measured below; CodeSimulator's `copyTM_run` citation
moved from line 1291 to **1295**. Every `file:line` into those two files here is at `1781a230`.

**Maintainer note (since drafting).** MIG-0b's round-2 files are now in the repository: the pack
`audits/mig0b-r2-pack.md` and the notes `audits/evidence/mig0b/r2/NOTES-r2.md`, bundled here.
The three MIG-0b facts this pack uses (the core's imports, its edits to `Build/Catalog.lean` and
`CodeSimulator.lean`, and `workTapePos_runFrom_mem_Icc` in `Finite`) can be checked there.
MIG-0b round 2 is itself out for audit, so its landing set may still change.

## What the gate covers

1. **The 26 witnesses** and their homes: 15 made public in place by an asserted scripted rename
   (body unchanged), 11 new definitions whose bodies are today's witness terms.
2. **The 45 new public statements**: 31 spec theorems and supporting lemmas that are `sorry`
   here, 14 that are proved here (two generic run lemmas, two canonical-word endpoint lemmas,
   three buffered-composition specs, three pair-extractor forms, the constant machine's time,
   the binary evaluator's time, the code normal form's equivalence, the call's tape count).
3. **The 55 corollaries**: the 53 existential rows, `Complexity.timeConstructible_id`, and the
   twentieth Catalog space row `Turing.FinTM.redirectTM_spaceUsedByTape`, each stated as
   `type_of% @row` and proved from the specs.
4. **The deletion plan** (the region, the R3 retirement, two consolidations), the PR sequence and
   batching, the name screen and the replay closures.

Out of scope: the proofs of the sorried specs beyond their sketches and the probes; MIG-0's
`Turing.Contract` (MIG-11 and MIG-17 restate the named witnesses as instances later); the other
Build files' existential rows (design §1); MIG-9's counter unification.

## Decisions in force (verify that the files reflect them)

**User decisions of 2026-10-13, binding** (MIG1-design §14):
- **M1, first form.** The B5a continuations are integrated and no B5a worker is active, so MIG-1
  retires all six R3 canonical `_run` rows, including `copyTM_run`'s consumer edit at
  `CodeSimulator.lean:1295`, in its last PR. That edit is sequenced with the H2-M move, which
  also edits `CodeSimulator.lean` (PR sequence below).
- **M2.** Both consolidations: `computesFunInTime_pairDup` onto Encoding's `Turing.pairDiagTM`;
  `computesFunInTime_pairMapSnd` onto the forwarding controller of its own space row, retiring
  `pairMapTM`.
- **M3.** The 20 Catalog space rows stay in Catalog as corollaries; only witness-intrinsic proofs
  move; Catalog imports Primitives (no cycle: Primitives does not import Catalog, measured).
- **M4.** MIG-17's "named loop hosts" item is done by MIG-1 (`loopHostTM`, `emitLoopTM`,
  `callTM`); MIG-17 keeps the Contract rebase of the loop hosts and `splitSafe`/`SafeRun`.
- **Style.** Spec theorems in the existing style, not `Contract` instances. The decision is
  binding; its rationale, restated accurately (design §2): **reason 2, shape** — 28 of the 34
  home rows are whole-machine computations from `initCfg` to a halt, judged by the output, and
  today's proofs fix neither an exact halting time nor the endpoint's work tapes, so a
  `Contract` instance would carry `post := runFrom … time` and add no content; the space rows
  bound `spaceUsed` from `initCfg` at every time, not inside an interval envelope. **Reason 3,
  order** — a `Contract M …` needs a named `M`, so named witnesses are a prerequisite of MIG-11
  and MIG-17, not an alternative. **Reason 1, layering, is temporary**: it holds for
  `Build/Contract.lean` as landed today (it imports Catalog), but MIG-0b's round-2 draft splits
  it into a core `Build/Contract/Basic`, whose closure is `Configuration`, `Deterministic`,
  `Finite`, `Simulation`, `StateRenaming` (MIG-0b round-2 `NOTES-r2.md` §3 and §10 item 6, not
  yet in the repository; `BUNDLE-MISSING.txt`), plus
  `Contract/Seam`, `/Embed`, `/Catalog`, `/Lift` and a facade. After that split every MIG-1 home
  except Simulation could import the core; the decision does not rest on layering.

**Earlier rulings**: design §2, the named-witness rule (constructive layers export named machines
with spec theorems; existential packaging only at the consumer layer); §16 decision 1 (byte
identity of §8 and the byte-identical `Primitives` of 12.2 lifted) and decision 2, scenario B
(retire the R3 canonical rows with their consumers edited); user rule: file size alone is never a
reason to split.

## Measured corrections to the backlog row (all MEASURED at `1781a230` unless marked)

| Backlog MIG-1 says | Measured | Note |
|---|---|---|
| 66 existential rows | **53** public machine-existential rows in the eight files (34 home rows: Primitives 18, Composition 7, Loop 6, Encoding 2, Wrappers 1; 19 Catalog space rows), plus `timeConstructible_id`, whose definition hides the same existential | inventory §0, re-checked; the unit restates all 54 and the redirect space row |
| 304 `f2_` copies | **304**, all private, Catalog 1787–10678 | reproduced |
| 6,255 of their lines verbatim | **232** copies code-identical to a same-named home declaration once the prefix is removed (**4,351** lines with docstrings); 5 more statement-identical with a different proof; 20 with a different statement (the old loop host family, three split lemmas); 47 with no same-named source | `scripts/region.py`; the 6,255 is not reproduced by any method (inventory note b) |
| 22 space rows | **20** space rows (19 existential and `redirectTM_spaceUsedByTape`); the other two region publics, `rewind_scan_heads` and `rewind_heads`, are head lemmas, which move to Simulation | |
| R3 `_run` rows: 0 external consumers | **5** code citations in 2 files: `copyTM_run` at `CertShell.lean:571` and `CodeSimulator.lean:1295`; `transferTM_run` at `CertShell.lean:585, 589, 602`; and 9 docstring mentions (`data/r3-retirement.tsv`) | |
| −7.6k to −8.3k, +0.4k | about **−7.0k** (ESTIMATE, range −6.6k to −7.4k; below) | the design's −7.4k assumed the decision-loop space family moves; this pack drops it (open question 1) |

Further measured facts that change the design:
- **The four "space-threaded" split copies are not replacements.** `f2_splitBody_round` has the
  *same statement* as Primitives' `splitBody_round` (only a local `transport` lemma differs);
  `f2_splitSolve_of_body`, `_source` and `_closed` only add a space conjunct, which
  `splitSolveTM_spaceUsed` now carries. The Primitives originals stay; the design's "−260 for the
  replaced time-only originals" does not apply.
- **The decision-loop space row needs no space hypotheses.** The budget theorem (space at most
  `23·k·(T + 1)`, from time hypotheses alone, both modes) implies `exists_loopTM_spaceUsed`'s
  bound `c·(S + T + 1)`; its 14 `a2_` ledger lemmas (433 lines) are then dead.
- **Seven region declarations duplicate public ones.** Four are checked by Lean in the bridge
  probe (each copied statement proved in one term by the public declaration): `f2_sum_add` and
  `a2_map_sum` are Mathlib's `Fin.sum_univ_add`; `f2_loop_input_run_le` is
  `Turing.MultiTapeTM.timed_input_bound`; `f2_catalogPair_inverse` is
  `Turing.eq_pairEncode_of_pairDecode` with its binders reordered. Three by reading:
  `f2_finSumEquiv` and `a2_mapSumEquiv` are Mathlib's `finSumFinEquiv` (the same
  `Sum.elim (Fin.castAdd _) (Fin.natAdd _)`) and serve only the two sum lemmas;
  `f2_loop_input_move_le` is the inner step of `timed_input_bound` and serves only
  `f2_loop_input_run_le`. `Fin.sum_univ_add` needs `import Mathlib.Algebra.BigOperators.Fin`,
  which is not in Simulation's closure today.
- **Design risk 1 is resolved for definitions:** with verbatim copies of both families,
  `f2_loopHost body F anchor findMode = loopHostM body F anchor false findMode` holds by `rfl`
  (bridge probe), so the moved loop proofs are re-targeted by rewriting, not by re-proof.
- **H2 adds the same run lemma.** The H2 step-block draft (`StepBlockDraft.lean.txt:729`, from
  `CodeSimulator`'s private `h1Run_headBound`) proposes
  `Turing.MultiTapeTM.abs_workTapePos_runFrom_sub_le`, the absolute-value form of Catalog's
  `f2_head_steps`, and its design note O9 says it moves below StepBlock "with MIG-1". The unit
  adopts H2's name and statement (one lemma, two consumers). MIG-0b's round-2 draft adds a third
  form, `MultiTapeTM.workTapePos_runFrom_mem_Icc` in `Finite`, from which H2's statement follows
  in three lines; the PR sequence says which one lands.
- **Replay closure** of the ten edited files: **206 of 624** modules (205 of 623 at `6aa9f67b`;
  the new `Build/Contract.lean` imports Catalog). Catalog has **29** importers (28 before), of
  which **9** do not import Primitives (adds `Contract`).

## Homes and landing form

| Part (unit line) | Lands in | Namespace | What lands, and when |
|---|---|---|---|
| 1 (92) | `TuringMachine/Simulation.lean` | `Turing.MultiTapeTM`, `Turing.FinTM` | S: `abs_workTapePos_runFrom_sub_le` (proved; not landed if MIG-0b's interval form lands first, PR sequence), `ComputesInTime.spaceUsed_le` (proved), `branchTM_spaceUsed` (statement; proof moves at F-A), `rewind_scan_heads` and `rewind_heads` moved from Catalog (verbatim) |
| 2 (265) | `TuringMachine/Composition.lean` | `Turing.FinTM` | S: `idTM`, `constTM`, `ifEqTM`, `condTM` in place; `constTM_computes` and three `bufferedCompTM_*` specs (proved); `idTM_computes`, `ifEqTM_computes`, `condTM_computes_iff` (F-A) |
| 3 (508) | `Build/Wrappers.lean` | `Turing.FinTM` | S: `timedCondTM` in place; `timedCondTM_computes`, `timedCondTM_spaceUsed` (F-A); `redirectTM_runFrom` |
| 4 (624) | `TuringMachine/Encoding.lean` | `Turing` | S: `Turing.pairDiagTM` in place; `FinTM.toCodeTM` and its equivalence (proved); `pairDiagTM_computes` (F-A) |
| 5 (720) | `ClassP/TimeConstructible.lean` | `Complexity` (declarations under `_root_.Turing.FinTM`) | S: `lengthBitsTM` in place (today `Complexity.counterTM`); `lengthBitsTM_computes`, `lengthBitsTM_spaceUsed` (F-A) |
| 6 (801) | `Build/Loop.lean` | `Turing.FinTM` | S: `loopHostTM` (today's abbreviation `loopHost`) and `callTM` (today `emCallTM`) in place; `emitLoopTM`, `callEntry`, `callExit`, `callTM_k_pos`; `callTM_run`; `loopHostTM_contracts`, `_decides`, `_finds`, `_spaceUsed_le_budget`, `emitLoopTM_computes` (F-C) |
| 7 (1492) | `Build/Primitives.lean` | `Turing.FinTM` | S: `prependTM` (today `catalogPrefixTM`), `incFixedTM`, `pairValidTM`, `pairExtractTM`, `unaryTokenTM` (today `emitterTokenTM`), `appendBitTM` (today `emitterAppendTM`) in place, with four promoted private lemmas; `polyUnaryTM`, `polyBitsTM`, `pairLenCheckTM`, `stripLastTM`, `splitSolveTM`, `splitSolveWithTM` new; their specs; **F-B: `pairMapSndTM` and its two specs**, with the forwarding family that moves from Catalog |
| 8 (2605) | `Build/Catalog.lean` | `Turing`, `Turing.FinTM` | S: `Cfg.ofWords_copy_endpoint`, `Cfg.ofWords_transfer_endpoint` (proved, Part 1 of Catalog); F-D: the 20 space rows as corollaries, `import …Build.Primitives`, the region deleted, the R3 rows retired |

**Why one unit.** A file elaborated against the snapshot can import only existing modules, and
later parts use earlier parts' declarations. Each part's cut file is the copyright block, the
part's imports (the existing home module and the modules it imports that carry parts), the
standard options, and the bodies of the parts in its closure (`scripts/cutcheck.py`, the stage-2
gate's script, unchanged).

**Landing is a set of edits, not a cut.** (1) A witness that is today a private definition of its
home lands *in place*: `private` goes, the name changes by the rename map, the body is
unchanged, the docstring becomes the unit's; every other occurrence in the home file is renamed
by the same asserted script. Rename map (`scripts/renames.json`): `catalogPrefixTM → prependTM`,
`emitterTokenTM → unaryTokenTM`, `emitterAppendTM → appendBitTM`, `loopHost → loopHostTM`,
`emCallTM → callTM`, `Complexity.counterTM → Turing.FinTM.lengthBitsTM` (declared with
`_root_.`; the file's private lemmas then say `FinTM.lengthBitsTM` under `open Turing`), and the
four promotions `catalogPrefixTM_computes → prependTM_computes`, `pairExtract_computes →
pairExtractTM_computes`, `pairValid_computes → pairValidTM_computes`, `incFixed_computes →
incFixedTM_computes`. (2) The **gate shims** (between `-- @shim begin` and `-- @shim end`) are
verbatim copies of the private definitions a witness body uses; they exist only because private
declarations of another module cannot be named, and are dropped on landing. (3) New definitions
and specs are inserted before the first row they serve. (4) The `MIG1Gate.*` declarations are not
landed; at the fill stage each row's proof becomes its `MIG1Gate.row_*` proof.

## What the files state (verify)

Constants are explicit. "S1" marks a promoted private lemma (statement verbatim modulo the
rename), "S3" a statement verbatim from a proved Catalog lemma that moves, "probe" a spec that the
spec probe derives from verbatim statements of proved private lemmas, "proved" a spec proved in
the unit.

**Part 1, Simulation.** `abs_workTapePos_runFrom_sub_le M d t j : |(M.runFrom d t).workTapePos j -
d.workTapePos j| ≤ t` (proved; H2's statement and proof). `ComputesInTime.spaceUsed_le (h :
M.ComputesInTime x y T) t : M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (T + 1)` (proved;
`f2_space_of_time`). `branchTM_spaceUsed M₁ M₂ b x t : (branchTM M₁ M₂ b).tm.spaceUsed … t = if b
then M₁…spaceUsed … t + M₂.k else M₂…spaceUsed … t + M₁.k` (S3, `f2_branch_space`).

**Part 2, Composition.** `idTM` (0 tapes, copies the input), `constTM w` (0 tapes, emits `w`),
`ifEqTM w₀ u v` (0 tapes, compares with `w₀`, emits `u` or `v`), `condTM D M₁ M₂` (register
conditional). `idTM_computes x : idTM.ComputesInTime x x (|x| + 1)` (probe);
`constTM_computes w x : (constTM w).ComputesInTime x w (|w| + 1)` (proved);
`ifEqTM_computes : ComputesFunInTime (if · = w₀ then u else v) ((|w₀| + max |u| |v| + 3)(n + 1))`
(probe); `bufferedCompTM_computesFunInTime (h₁ h₂ hT₂) : (bufferedCompTM M₁ M₂).ComputesFunInTime
(g ∘ f) (2(T₁ n + T₂ (T₁ n) + 1))`, `bufferedCompTM_computesFunInTime_on_image : … g (2T₁ n + T₂ n
+ 2)`, `bufferedCompTM_computes_iff M₁ M₂ x w` (the halting relation of `exists_comp_partial`)
(all proved, the rows' bodies); `condTM_computes_iff (hD : D.Computes [p ·]) x w : (∃ t,
condTM… x w t) ↔ ∃ t, (cond (p x) M₁ M₂)… x w t` (probe).

**Part 3, Wrappers.** `timedCondTM D M₁ M₂` (captured decider, verdict read, rewind, branch
bank). `timedCondTM_computes (hD h₁ h₂) : … (if p x then f₁ x else f₂ x) (5(T₀ n + max (T₁ n)
(T₂ n) + 1))` (S3, `f2_cond_time`, the row's body); `timedCondTM_spaceUsed D M₁ M₂ x b T t (hD :
D.ComputesInTime x [b] T) : space ≤ D's space at T + branch space at t + 2` (S3,
`f2_cond_space`); `redirectTM_runFrom M haltOn x t`: the redirected run's state (the source state
with the last emitted bit while live; after the halt, halted iff that bit is `haltOn`, else the
live loop), input position, work tapes and heads equal the source run's, output `[]` (probe; the
public field form of the private `redirect_run`).

**Part 4, Encoding.** `Turing.pairDiagTM` (six states, 0 tapes, outputs `pairEncode α α`);
`pairDiagTM_computes x : … (pairEncode x x) (4|x| + 5)` (probe). `FinTM.toCodeTM : (M : FinTM
Bool) → M.k = 1 → CodeTM` (noncomputable; `⟨|Q| − 1, tm.relabelState e⟩` with `e =
Fintype.equivFinOfCardEq`); `toCodeTM_computesInTime_iff M hk x o t` (proved).

**Part 5, TimeConstructible.** `Turing.FinTM.lengthBitsTM` (one tape, four states, the binary
counter). `lengthBitsTM_computes : ComputesFunInTime (Nat.bits |x|) (5(n + 1))` (S3,
`f2_counter_computes`, the `timeConstructible_id` body); `lengthBitsTM_spaceUsed x t : space ≤
5(Nat.size |x| + 1)` (S3, `f2_counter_space`).

**Part 6, Loop.** `loopHostTM body F anchor findMode := loopHostM body F anchor false findMode`
(abbreviation, as today); `emitLoopTM body F anchor := emLoopHost body F anchor true` (the
forwarding host in find mode); `callTM M emit` (today `emCallTM`), `callEntry M emit :=
(callTM M emit).tm.q₀`, `callExit M emit := .inr (.inr 5)`. `loopHostTM_contracts` (today's
`loopHost_contracts` with `c = loopHost_bound = 10`, `Loop.lean:2113`); `loopHostTM_decides` and
`loopHostTM_finds` (`10(T n + 1)(R n + 2)`; probe, from the contract and the private summation
lemmas); `loopHostTM_spaceUsed_le_budget` (both modes, under the contract's hypotheses: space ≤
`23·k·(T |x| + 1)`; probe, from the extended contract and `f2_seamed_space`);
`emitLoopTM_computes` (`10(T n + 1)(R n + 2)`, the row's body); `callTM_k_pos` (proved);
`callTM_run M emit x arg cap T (hM : M.ComputesInTime arg cap T) : ∃ t ≤ (24 + 13·k_M)(T + |arg|
+ |cap| + 1), 0 < t ∧ (∀ j < t, state ≠ some (callExit M emit)) ∧ runFrom … t = {ofWords
(callExit M emit) (stateWord k (if emit then arg else cap)) with output := if emit then cap else
[]}` (probe: it *is* `emCall_first`).

**Part 7, Primitives.** S1: `prependTM_computes w : ComputesFunInTime (w ++ ·) (|w| + n + 1)`,
`incFixedTM_computes x : … ((incFixed x).getD []) (3(|x| + 1))`, `pairValidTM_computes x : …
[(pairDecode x).isSome] (|x| + 1)`, `pairExtractTM_computes first second x : … (5(|x| + 1))`;
proved: `pairExtractTM_fst`, `_snd`, `_concat` (`5(n + 1)`). `polyUnaryTM C : ℕ → FinTM Bool` (`0
↦ constTM (replicate C true)`, `d + 1 ↦` the private engine); `polyUnaryTM_computes C e : …
(replicate (C(|x| + 1)^e) true) ((C + 5e + 4)(n + 1)^e)` (probe), `polyUnaryTM_spaceUsed C e x t
: ≤ 5e(|x| + 1)` (probe). `polyBitsTM C e := if C = 0 then constTM (Nat.bits 0) else match e with
| 0 => constTM (Nat.bits C) | d + 1 => bufferedCompTM (polyUnaryTM C (d + 1)) lengthBitsTM`;
`polyBitsTM_computes C e : … (Nat.bits (C(|x| + 1)^e)) ((7C + 5e + 11)(n + 1)^e)` (proved).
`pairLenCheckTM C e := pairCountTM (bufferedCompTM (pairExtractTM true false) (polyUnaryTM C e))`,
`pairLenCheckTM_computes : … ((C + 5e + 17)((n + 1)^e + n + 1))` (probe). `stripLastTM :=
timedCondTM (bufferedCompTM (pairExtractTM false true) anyTrueTM) rawStripTM (constTM [])`,
`stripLastTM_computes : … (150(n + 1))` (probe). `pairMapSndTM Mg := fwdMapTM Mg true`,
`pairMapSndTM_computes (hg hTg) : … (22(n + 1 + Tg n))`, `pairMapSndTM_spaceUsed Sg hgs hSg x t
: ≤ Sg |x| + 22(|x| + 1)` (probe). `splitSolveTM C : ℕ → FinTM Bool` (find-mode loop host over
`splitBodyTM` with today's per-`e` source, fuel `lengthBitsTM`),
`splitSolveTM_computes : … (20((C + 1 + 5e)2^e + 46)(n + 1)^(e + 2))`, `splitSolveTM_spaceUsed :
≤ 23·k·((C + 1 + 5e)2^e + 46)(|x| + 1)^(e + 1)` (probe). `splitSolveWithTM E` (find-mode loop
host over `emitterP2BodyTM` of the two install calls `callTM E false`, `callTM lengthBitsTM
false`), `splitSolveWithTM_computes f E TE hTE hE : … (20(591 + 26·k_E)(n + 1)(TE (n + 1) + n +
2))` (probe). `unaryTokenTM_computes : … (3(n + 1))`, `appendBitTM_computes b x : … (x ++ [b])
(|x| + 1)` (probe).

**Part 8, Catalog.** `Cfg.ofWords_copy_endpoint q q' w src dst (hdst : w dst = [])`: the framed
copy endpoint started at `Cfg.ofWords q w` is `Cfg.ofWords q' (update w dst (w src))`;
`Cfg.ofWords_transfer_endpoint … (hne : src ≠ dst) (hdst)`: the transfer endpoint is
`Cfg.ofWords q' (update (update w src []) dst (w src))` (both proved). The 20 space rows: 48 of
the 55 corollaries are at most six lines; seven, all proved, take 8 to 24 lines of arithmetic
(`polyBits_spaceUsed`, `pairLenCheck_spaceUsed`, `pairLenCheck`, `stripLast_spaceUsed`,
`splitSolve_spaceUsed`, `cond_spaceUsed`, `exists_loopTM_spaceUsed`).

## Changes from the draft and the design (and why)

1. **Every witness has its real body** (the draft left `loopHostTM`, `callTM`, `callEntry`,
   `callExit`, `pairMapSndTM` and an engine `sorry`), checked against its source.
2. **Landing names directly** (draft: namespace `MIG1Draft`): a private declaration's name is
   module-local, so the public names can be declared against the snapshot; only the rows need
   gate names (`MIG1Gate.row_*`).
3. **The run-form head lemma is H2's** `abs_workTapePos_runFrom_sub_le` (design:
   `workTapePos_runFrom_le`), so that MIG-1 and H2 share one lemma; MIG-0b's interval form may
   make it a corollary (PR sequence, open question 3).
4. **`ComputesInTime.spaceUsed_le` is homed in Simulation** (design: Catalog): it is generic, and
   the moved space proofs and later Primitives space specs can then use it.
5. **The `_k` lemmas are dropped**: `rfl` gives every tape count; no consumer needs a name.
6. **`polyUnaryTM_computes` is sharp**: `(C + 5e + 4)(n + 1)^e`, without the draft's linear
   allowance, which only `f2_unary_sharp`'s reuse of the constant row's existential constant
   needed; there is no `polyUnaryEngineTM`, the engine stays the private `catalogPolyUnaryTM`.
7. **One clean-call contract** `callTM_run` for both modes, with today's full first-exit cut
   `∀ j < t` (design: `callTM_install`, `callTM_emit`, positive-only cut); the rows weaken it.
8. **The loop's space** is `loopHostTM_spaceUsed_le_budget` (both modes, time hypotheses only,
   `23·k·(T + 1)`), replacing the draft's decision-mode `loopHostTM_spaceUsed` (`19·k·(S + T +
   1)`, with fuel and body space hypotheses); `exists_loopTM_spaceUsed` is its corollary
   (open question 1).
9. **`redirectTM_runFrom` is stated field by field**, so that no private definition occurs in a
   public statement.
10. **`pairMapSndTM` lands at F-B**, not S: its body is Catalog's private controller, which can
    move to Primitives only together with its 24 lemmas.
11. **`splitSolveWithTM E` takes only the width machine**: the width function does not occur in
    the machine (design signature `(ℕ → ℕ) → FinTM Bool → FinTM Bool`).
12. **`polyBitsTM`** follows today's space proof's case split exactly (`constTM (Nat.bits 0)` at
    `C = 0`), and its time spec is proved here with the constant `7C + 5e + 11` at degree `e`
    (design ESTIMATE: degree `e + 1`).
13. **The composite constants are checked by Lean** (spec probe), not estimated: `150`,
    `C + 5e + 17`, `20((C + 1 + 5e)2^e + 46)`, `20(591 + 26·k_E)`, `23·k`.
14. **The R3 retirement uses two endpoint lemmas** (design §7), proved here; each retired row is
    re-derived from them in four lines (`MIG1Gate.retired_*`), which is the consumer edit.
15. **The deletion plan** has new fates: seven duplicates of public lemmas, the 14-lemma `a2_`
    ledger deleted with the S-form, the split originals kept (above).

## The deletion plan (data: `data/deletion-plan.tsv`, 378 rows)

Region: Catalog 1779–11361, 9,583 lines, 378 declarations (MEASURED). Lines include docstrings.

| Fate | Declarations | Lines |
|---|---|---|
| Delete: `f2_` copy code-identical to its home source (the original is used) | 232 | 4,351 |
| Delete: `catalog_redirect*` copies of Wrappers' private redirect family (code-identical) | 7 | 77 |
| Delete: statement-identical copy, different proof (`f2_loopHost_halt_return`, `f2_loopCall_frame`, `f2_loopHost_accept`, `f2_loopHost_round`, `f2_splitBody_round`) | 5 | 314 |
| Delete: modified copy; citations re-targeted at the original (`f2_loopHost` and 15 old-host phase lemmas) | 16 | 614 |
| Delete: duplicates a public declaration (seven, above) | 7 | 111 |
| Delete: dead, reached from no public declaration (11 `f2_` and `a2_heads_halted`, as the inventory) | 12 | 213 |
| Delete: used only by deleted declarations (`f2_loop_live_prefix`, `f2_loopHost_body_capture`, `_fuel_rewind`, `_payload_rewind`, `f2_splitEmbed_run`) | 5 | 142 |
| Delete: reached only from the decision-loop S-form proof (the `a2_` ledger) | 14 | 433 |
| Absorbed into a gated statement (`f2_head_steps`, `f2_space_of_time`, `f2_counter_computes`, `f2_counter_space`, `f2_cond_time`, `f2_cond_space`, `f2_branch_space`, `f2_unary_sharp`, `f2_strip_linear`, `f2_exists_loopFind_space`, `f2_splitSolve_of_body`, `_source`, `_closed`) | 13 | 512 |
| Move, renamed: forwarding map → Primitives (`a2_map… → fwdMap…`) | 28 | 721 |
| Move: polynomial space → Primitives (`polyHeads`, `polyHeads_bounds`, `poly_step`, `catalogPoly_space`) | 4 | 196 |
| Move: counter space → TimeConstructible (`Complexity.counter_count_space`, `counter_heads`) | 2 | 97 |
| Move: conditional ledger → Wrappers (`condHeads`, `control_heads`, `branch_heads`, `read_heads`, `cond_ledger`) | 5 | 109 |
| Move: loop budget → Loop (`loopCall_heads`, `segment_heads`, `space_radius`, `seamed_space`) | 4 | 101 |
| Move, replacing the original: `f2_loopHost_contracts` → Loop's `loopHost_contracts` (adds the seam and terminal head clauses) | 1 | 178 |
| Move: pair length → Primitives (`pairDecode_fst_length_le`) | 1 | 11 |
| Public: space rows, corollaries in place | 20 | 922 → about 540 (ESTIMATE: 413 statement and docstring lines kept, 126 proof lines from the unit) |
| Public: `rewind_scan_heads`, `rewind_heads` moved to Simulation | 2 | 70 |

Of the absorbed thirteen, the proofs of `f2_counter_space`, `f2_cond_space`, `f2_branch_space`,
`f2_exists_loopFind_space` (space half) and `f2_space_of_time` move as the specs' proofs (233
lines); the other eight are replaced by proofs over the named witnesses. The moved code is a
disclosed move, not a copy: the batches that receive it take it from the base Catalog, F-D deletes
it, and the full gate's duplication screen checks that each moved declaration occurs once.

**R3 retirement** (`data/r3-retirement.tsv`; Catalog unchanged, so MEASURED at `1781a230`):
`transferTM_run` (1297, 49 lines), `copyTM_run` (1382, 33), `clearTM_run` (1454, 33),
`compareTM_run` (1522, 36), `incrementTM_run_succ` (1604, 49), `incrementTM_run_overflow` (1651,
37): 237 lines, replaced by the two endpoint lemmas (about 75 lines). Five code sites change, each
to the four-line derivation of `MIG1Gate.retired_copyTM_run` or `retired_transferTM_run`
(`CertShell.lean:571, 585, 589, 602`; `CodeSimulator.lean:1295`); nine docstring mentions are
rewritten (`CertShell.lean:452, 706`; `Catalog.lean:1047, 1093, 1135, 1177, 1236, 1379, 11617,
11625`).

**Consolidations** (M2), with statement identity by `type_of%`: `row_computesFunInTime_pairDup`
and `row_computesFunInTime_pairDup_spaceUsed` are proved on `Turing.pairDiagTM`;
`row_computesFunInTime_pairMapSnd` and its space row on `pairMapSndTM`. Retired with them
(`scripts/retire.py`, MEASURED): `pairDupTM` with `scanCopy_run`, `scanCopy_finish`,
`pairDup_double`, `pairDup_computes` (5 declarations, 138 lines); `pairMapTM` with its 15 private
lemmas (16 declarations, 447 lines).

**Size** (ESTIMATE): Catalog −9,583 + about 550 (corollaries) − 237 + 75 ≈ **−9,200**, to about
3.55k lines; moved code into the homes **+1,720** (1,483 moved, 233 absorbed proofs) less the
replaced `loopHost_contracts` (146) ≈ **+1,570**; new statements and definitions ≈ **+1,090**
(987 theorem lines and 104 definition lines in the unit; the row bodies that become spec proofs
move, net zero); consolidations **−585**; consumer edits **+16**. Net about **−7.0k** (range
−6.6k to −7.4k).

## PR sequence and batching (design §8–§10, updated)

**Bold alert: H2-M and MIG-1 share `CodeSimulator.lean` and one lemma; land H2-M first.**

0. **H2-M** (maintainer; already scheduled for the coordinated window before the next B5a brief,
   `audits/fills-8-integration.md`): moves the H1 step block from `CodeSimulator.lean` (about
   lines 2869–4466) to `Build/StepBlock.lean`, including `abs_workTapePos_runFrom_sub_le`.

**MIG-0b and MIG-1: neither must land first.** MIG-1 uses no contract (style decision) and
MIG-0b uses no MIG-1 declaration; MIG-17 needs both. Either order keeps the import graph acyclic
(MIG-0b's core imports nothing above Simulation; Catalog's new Primitives import only enlarges
`Contract/Catalog`'s closure). The interactions are textual and one shared fact (MIG-0b's
landing set, `r2-mig0b/landing/`, MEASURED):
- **`Build/Catalog.lean`**: MIG-0b moves `MultiTapeTM.spaceUsedByTape_le_card_Icc` (`:392`) to
  `Finite` (12,752 → 12,732 lines); MIG-1 adds the endpoint lemmas in Part 1 (S) and deletes the
  region and the R3 rows (F-D). The edits are disjoint, no region declaration cites that lemma
  (inventory §2.1, re-checked), and the deletion plan is keyed by name, so the later PR rebases
  mechanically (`scripts/region.py` re-run gives the shifted line numbers).
- **`TuringMachine/CodeSimulator.lean`**: three PRs touch it — H2-M (the step block), MIG-0b (a
  one-token edit at `:5841`, its Q11) and MIG-1 F-D (`:1295`); the regions are disjoint, and the
  three land one after another, all before the next B5a brief.
- **The run head bound has three forms in flight**: Catalog's `f2_head_steps` (two
  inequalities), H2's `abs_workTapePos_runFrom_sub_le`, and MIG-0b's
  `MultiTapeTM.workTapePos_runFrom_mem_Icc` in `Finite` (over `Type*`), from which MIG-0b's
  fit file proves H2's statement in three lines (its §10 item 5). There should be one proof.
  If MIG-0b lands before MIG-1 S, MIG-1 S does not introduce the absolute-value lemma: its moved
  proofs cite `workTapePos_runFrom_mem_Icc` (`Finset.mem_Icc.mp` gives the two inequalities of
  `f2_head_steps`), and H2's statement, if wanted, is the three-line corollary. If MIG-1 S lands
  first, it introduces `abs_workTapePos_runFrom_sub_le` in Simulation as gated, and MIG-0b's
  landing re-proves it from the interval lemma (statement unchanged).
- MIG-0b's other files (`Finite`, `StateRenaming`, `Build/Embed`, `Build/Seam`, `CounterLoop`,
  `CfgRecord`, `AlphabetReduction`, `Zone` docstrings, the facades) are not MIG-1 files; its
  names do not clash with MIG-1's (`scripts/namescreen_extra.py` over the landing set: 1,211
  declarations, 0 matches with the 71 public and 45 moved names).
- *Recommendation:* land whichever closes its gate first; if both are ready, MIG-0b first, so
  that the head bound has its single home in `Finite` before MIG-1's fills move the proofs that
  cite it. Both replays are large (MIG-0b edits `Finite`); they are not merged.
1. **MIG-1 S, statements** (maintainer, one PR, this gate). Replay closure **206** modules.
   - The 15 in-place renames and the four promotions; the 10 new definitions other than
     `pairMapSndTM`; the 43 new statements other than `pairMapSndTM`'s two; the two head lemmas
     moved to Simulation; the endpoint lemmas in Catalog Part 1.
   - The head bound: if MIG-0b has landed, S introduces no head lemma and cites
     `workTapePos_runFrom_mem_Icc`; else if H2-M has landed, `abs_workTapePos_runFrom_sub_le`
     moves from StepBlock down to Simulation (name and statement unchanged; StepBlock imports
     Simulation); else S introduces it in Simulation and H2-M cites it.
   - **Proved at S** (26): the 14 proved in the unit, the 4 promotions (proofs unchanged), and 8
     whose proofs are citations of home lemmas and glue, shown by the probe: `callTM_run`,
     `redirectTM_runFrom`, `polyUnaryTM_computes`, `pairLenCheckTM_computes`,
     `stripLastTM_computes`, `splitSolveTM_computes`, `splitSolveTM_spaceUsed`,
     `splitSolveWithTM_computes` (the last three depend on `loopHostTM_finds` and the budget
     theorem, sorried until F-C). **Sorried at S** (17): the specs whose proofs are row bodies or
     moved Catalog proofs. **No row's proof changes at S**, so no row depends on a `sorry`.
2. **Fills**, four batches with disjoint files; every batch's screen population includes the base
   Catalog (the move source):
   - **F-A** (Composition, Simulation, Wrappers, Encoding, TimeConstructible; replay **206**):
     nine specs (`branchTM_spaceUsed`, `idTM`, `ifEqTM`, `condTM`, `timedCondTM` ×2, `pairDiagTM`,
     `lengthBitsTM` ×2); moves the counter-space and ledger families; adds
     `import Mathlib.Algebra.BigOperators.Fin` for `Fin.sum_univ_add`; swaps 11 rows
     (Composition 7, Wrappers 1, Encoding 2, `timeConstructible_id`).
   - **F-C** (Loop; replay **91**): five specs (contracts, decides, finds, budget, emitLoop); the
     extended contract replaces `loopHost_contracts` (re-targeted by `rfl`) with the budget family;
     swaps 6 rows.
   - **F-B** (Primitives; replay **80**): three specs (`polyUnaryTM_spaceUsed`, `unaryTokenTM`,
     `appendBitTM`); lands `pairMapSndTM`, its two specs and the 28-declaration forwarding family;
     moves the polynomial-space and pair-length families; swaps 18 rows; retires `pairDupTM` and
     `pairMapTM`.
   - **F-D** (Catalog, CertShell, CodeSimulator; replay **30**): deletes the region, writes the
     20 corollaries and the Primitives import, retires the six R3 rows with the five code sites
     and nine docstring mentions. **The CodeSimulator site is edited after H2-M has landed,
     rebased on it**; the site (`canonPreserveInstall`, `:1295`) is outside H2-M's region, so
     the rebase is mechanical. F-D should also land before the next B5a continuation is briefed,
     since B5a owns regions of CodeSimulator.
   - Integration order F-A, F-C, F-B, F-D (or one integration); F-D last, because every Catalog
     corollary cites specs of the other batches.
3. **Stage G, full gate**: freeze (every public statement of the ten files unchanged except the
   six retired rows and the gated additions), replay of **206** modules (61 colleague-owned
   `CircuitComplexity` modules and 6 `TimeHierarchy` modules among them, replayed, not edited),
   axioms of the 55 corollaries and the 45 statements, the duplication screen (no moved
   declaration twice, no `f2_`/`a2_` name left).

## Brief for the auditor

Restate every definition in your own words before reading its docstring; argue each sorried
theorem true in 2–5 sentences or exhibit a counterexample; attempt at least six adversarial
instantiations (failure modes 1–5 of `audits/TEMPLATE.md`). Points to rule on:

1. **Fidelity of the moved bodies.** Check the identity log (158 entries: 97 verbatim, 47
   statements, 7 substring checks, 3 transforms, 4 binder checks; three negative controls) and the
   rename map. Is every rename a pure renaming (injective, no capture)? Are the three transforms
   (`loopHostTM_contracts`: `∃ c` removed and `c ↦ 10`; `callTM_run`: the two anchor states
   named; the probe's extended contract) faithful, given `Loop.lean:2113` and
   `Catalog.lean:8167` (`refine ⟨loopHost_bound, ?_⟩`, `loopHost_bound = max 1 (max 9 (3 + 2 +
   5))`)?
2. **Each spec true as stated.** Twenty are derived in the spec probe from verbatim statements of
   proved lemmas, nine are such statements; check the remaining two (`loopHostTM_contracts`,
   `emitLoopTM_computes`) against their source proofs. Boundary cases: `e = 0` and `C = 0` in the
   polynomial family; empty input; `k = 0` machines; `R |x| = 0` in the loop; empty argument and
   result in the call.
3. **The loop budget theorem in decision mode.** Today's proof is for find mode
   (`f2_exists_loopFind_space`); its space half uses only the mode-independent extended contract.
   Is `23·k·(T |x| + 1)` right for `findMode = false` (probe), and does it make the decision-loop
   S-form and its 14 lemmas redundant (open question 1)?
4. **Each corollary derivable**: every `MIG1Gate.row_*` elaborates against `type_of% @row`
   (statement identity by construction). Are the witness changes (pairDup onto `pairDiagTM`,
   pairMapSnd onto the forwarding controller, polyBits onto the split witness) harmless to the
   35 consumer files, given that the rows are existential?
5. **The full first-exit cut** of `callTM_run` (`∀ j < t`, including `j = 0`) versus the rows'
   positive-only cut: is it true for both modes (it is `emCall_first`), and is one statement for
   both modes the right public surface?
6. **Public abbreviations over private definitions.** `loopHostTM` and `emitLoopTM` unfold to the
   private `loopHostM`/`emLoopHost`; `polyUnaryTM`, `pairLenCheckTM`, `stripLastTM`,
   `splitSolveTM`, `splitSolveWithTM`, `pairMapSndTM` to private machines. Acceptable outside the
   module system (design risk 7)?
7. **The deletion plan's completeness.** Every one of the 378 region declarations has one fate;
   check the "dead", "used only by deleted" and "duplicate" claims (the bridge probe checks four
   of the seven duplicates), and that no moved declaration needs a deleted one.
8. **The R3 retirement.** Are the endpoint lemmas stated so that every consumer site is a
   four-line edit (the two `retired_*` re-derivations), and is the H2-M sequencing right?
9. **Homes and names.** Simulation for `ComputesInTime.spaceUsed_le`; the head lemma's form and
   home, given H2 and MIG-0b; `_root_.Turing.FinTM.lengthBitsTM` inside TimeConstructible's
   `Complexity` namespace; `Cfg.ofWords_*_endpoint`; the proposed private names of moved
   declarations (`data/moved-names.json`).
10. **Documentation and policy**: statement prose on every public declaration, proof sketches on
    every sorried theorem, attribution, 100-column lines.
11. Report anything else that the files, this pack, the design or the inventory misstate.

## Repository-side attestations (verify or challenge)

Source facts are checkable in the bundle; execution claims are the logs'. All MEASURED.
- **Elaboration** (`mig1-statements-elaboration.log` §2): the unit gives exit 0, 0 errors, 31
  `declaration uses 'sorry'` warnings and 6 linter warnings, all inside verbatim shims (as in
  their sources). The spec probe (unit + tail): 0 errors, 70 sorry warnings (the unit's 31 and 39
  statement shims; the 20 probe theorems have none of their own). The bridge probe: 0 errors,
  0 warnings.
- **Cut checks** (`mig1-statements-cutcheck.log`): each of the eight landing parts in its own
  closure gives 0 errors (sorry warnings: Simulation 1, Composition 4, Wrappers 7, Encoding 2,
  TimeConstructible 4, Loop 13, Primitives 31, Catalog 31, each counting its closure); the unit's
  imports are exactly the union of the parts' imports.
- **Identity** (`mig1-statements-identity.log`): 158 entries, 0 failures; three single-token
  mutations of the unit give exactly three failures.
- **Bridge probe**: `f2_loopHost body F anchor findMode = loopHostM body F anchor false findMode`
  by `rfl`, and the four duplicate statements each proved by one public term.
- **Axioms** (`mig1-statements-axioms.log`): 130 public declarations; no axiom besides `propext`,
  `Classical.choice`, `Quot.sound` and `sorryAx`; 46 are free of `sorryAx`, among them all 26
  witnesses and the corollaries `computesFunInTime_const`, `_const_spaceUsed`, `_comp`,
  `exists_comp_on_image`, `exists_comp_partial`, `exists_codeTM`.
- **Names** (`mig1-statements-names.log`): 71 proposed public names; 0 full-name clashes with any
  declaration of the home, its import closure or any module importing it (a later private
  declaration of an existing public name is rejected by Lean, checked), nor with H2's proposed
  names except the shared lemma; 0 identifier occurrences of the short names in the
  colleague-owned files and the nine Catalog importers that newly see Primitives; 0 package hits;
  45 proposed private names, one clash, the intended replacement of `loopHost_contracts`. Against
  MIG-0b's round-2 landing set (15 files, 1,211 declarations): 0 matches.
  `Complexity.polyUnaryTM` (TMSAT, private) shares a last component in another namespace.
- **Consumers** (`mig1-statements-consumers.log`): the 53 rows have 221 external code citations in
  35 files, the 34 home rows 216 in 33, identical per row to the inventory's measurement at
  `6aa9f67b`; every name is declared once.
- **Replay** (`mig1-statements-replay.log`): 206 of 624 modules for the ten files; S 206, F-A 206,
  F-B 80, F-C 91, F-D 30.
- **Style**: no line over 100 characters; `scripts/campaign_style_lint.py` (a copy of the
  repository's) gives 0 FAIL and one WARN per elaboration unit (size; user rule: size alone is
  no reason to split).
- **Nothing in the worktree was changed.** No `lake`, no `git` command, no olean written; every
  elaboration went through `tools/leanelab.sh`; Python ran as `python3 -I`.
- **The maintainer's re-check.** The maintainer, with the same tool, checkout and snapshot,
  re-elaborated the unit, the eight cut files and the three probes, with the counts above. The
  axiom probe gives 130 prints: 46 are free of `sorryAx`, and none uses an axiom outside the
  standard three. The maintainer also re-ran `identity.py`, with 158 entries and 0 failures; the
  three-mutation control gives exactly 3 failures.

## Open questions for the user

1. **Drop the decision-loop S-form space family?** `loopHostTM_spaceUsed_le_budget` covers both
   modes from time hypotheses, and `exists_loopTM_spaceUsed` is its corollary.
   *Recommendation:* drop it; the 14 `a2_` ledger lemmas (433 lines) are deleted, not moved. If
   kept, add a decision-mode `loopHostTM_spaceUsed` and move the family to Loop.
2. **Prove eight citation specs at S** (list under PR 1). *Recommendation:* yes; the probe shows
   each proof, and the composite constants are then settled before any fill.
3. **The run head bound** (H2's absolute-value form, MIG-0b's interval form in `Finite`,
   Catalog's copy). *Recommendation:* one proof, MIG-0b's `workTapePos_runFrom_mem_Icc`, if
   MIG-0b lands before MIG-1 S; MIG-1 then gates no head lemma of its own and its moved proofs
   cite the interval form. Otherwise MIG-1 S lands `abs_workTapePos_runFrom_sub_le` in
   Simulation, shared with H2 (H2-M first, moved down at S), and MIG-0b re-proves it from the
   interval lemma.
4. **`Fin.sum_univ_add` for the copied `f2_sum_add`.** *Recommendation:* import
   `Mathlib.Algebra.BigOperators.Fin` in Simulation (F-A) rather than keep a public copy.
5. **Homes**: `ComputesInTime.spaceUsed_le` in Simulation (design: Catalog). *Recommendation:*
   Simulation.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/mig1-statements-findings.md`. The gate closes when a round reports zero blockers and zero
majors; stage S then lands as described, and each fill batch has its own gate.
