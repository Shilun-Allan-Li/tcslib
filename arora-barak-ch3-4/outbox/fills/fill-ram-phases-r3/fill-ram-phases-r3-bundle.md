## ===== campaign/items/ram-tm/briefs/COMMON.md =====

# RAM fills: rules common to every brief

These rules bind every RAM fill (tier 1 `fill-ram-wordsize`, tier 3 `fill-ram-classes`, and
later the tier 2 fills). Each brief adds its targets, owned file and route.

## Repository, exchange and base

- **You work to and from the exchange.** It is branch `exchange/pass-shelat-ch5-8` of
  `https://github.com/Shilun-Allan-Li/tcslib`, folder `arora-barak-ch3-4/`.
  - **Inputs:** your fill's bundle and README, in `arora-barak-ch3-4/outbox/fills/<fill-name>/`.
  - **Output:** your delivery, in `arora-barak-ch3-4/inbox/<fill-name>/` (see "Delivery").
  - Do not push anywhere else.
- **Repository:** the same repository. Fetch the base commit from it read-only.
- **Base:** the commit named in your brief, on branch `complexity/ram-simulation`. That branch
  is `main` after the chapters 3–4 integration (#364), with the maintainer tools
  (`devtools/seyoon/`) merged in. Work on a local branch off it, record the base in `REPORT.md`,
  and never rebase.

## Ground rules (binding)

1. **Statement freeze.** Every existing declaration keeps its statement byte-identical. You
   change only the bodies of your targets, their `**Proof sketch.**` paragraphs, and the owned
   file's module docstring. A statement you believe is false or unprovable as written is an
   **E-STATEMENT** stop: report it with the evidence, and do not change it.
2. **Rule 10** (`campaign/maintainer/WORKFLOW.md` §2). A proof may read another file's TCSlib
   definition only through that file's published equations and lemmas. So:
   - no `simp [Def]`, `unfold Def`, `delta`, generated `eq_1`/`eq_def`, or
     `rfl`/`change`/`show` that unfolds another file's definition;
   - core and Mathlib definitions may reduce by `rfl`, `decide` or `show`, but are not passed to
     `simp`, `rw` or `unfold`.

   The maintainer's seal check makes every other-file definition irreducible and re-elaborates
   your proofs. A proof that unfolds one fails there. A missing reader is an **E-READER** stop.
   Report it; do not unfold.
3. **No new public surface.** Do not add public declarations, files, imports, `@[simp]`
   attributes, `sorry`, `admit` or axioms. Helpers are `private`, in the owned file, under a
   section header. If you need a new public lemma or machine elsewhere, that is an **E-HOST**
   stop: report its statement and why.
4. **Cite, do not re-prove.** Search the import closure before proving a helper fact. Re-deriving
   an existing fact, or copying a proof's text for a variant instead of factoring a private
   helper, is a duplication finding even when the copy screens miss it.
5. **Standards** (`policy.md`): a `**Proof sketch.**` on every proof over 20 lines, describing
   the proof you wrote and naming declarations, not file line numbers. Docstrings carry no
   campaign labels: no decision or item codes such as `R8.5c`, `MIG-0a` or `PROG-4`, no
   `design §…` and no `campaign/` paths. Rewrite the proof sketches of the targets you prove to
   meet this. When the owned file's last admission is proved, drop "proofs pending" from its
   module docstring.
6. **A clean frontier is a valid delivery.** Prove what you can. Leave each unproved target as
   `sorry`, and report exactly where you stopped and why.

## Environment and verification

- Follow `campaign/standards/fill-environment-addendum.md` (v2.6). **Never run `lake build`.**
  Bootstrap the import closure at the base into your own scratch olean tree.
- **At most 3 Lean processes may run at once across the machine.** Other fills share it: start
  at most one of your own at a time, check the machine-wide count first, and record any waits.
- **Final checks** (record their exit codes):
  - the owned file elaborates with zero errors and no `sorry` warnings for the proved targets;
  - `#print axioms` for each proved target prints at most `propext`, `Classical.choice` and
    `Quot.sound`, plus `sorryAx` only if the target reaches a still-admitted declaration. Run
    it through a scratch file, not in the library;
  - for every target whose axioms include `sorryAx`, a scratch **dependency walk** that lists
    each reachable constant whose value uses `sorryAx`, as the chapters 3–4 probe
    `CloseHeadlines` does (gate 160, G160-01). The list must contain only the admitted
    declarations your brief names;
  - every module that imports the owned file elaborates with zero errors.

## REPORT.md checklist

- [ ] The base, and each target: proved, or the frontier and the reason.
- [ ] For each target that reaches `sorryAx`, the dependency walk's list of admitted
      declarations.
- [ ] Every new private declaration and its role. Every other-file definition reached, and the
      published equation used to read it. The existing facts you searched for before each
      helper.
- [ ] The final check outputs, the axiom prints, and `git diff --stat` touching only the owned
      file.
- [ ] Environment deviations and Lean waits.

## Delivery

Make `<fill-name>.zip` containing `REPORT.md`, the delivered owned file, the patch against the
base, and the check logs. Push it, with any `<fill-name>-checkpoint-N.zip`, to
`arora-barak-ch3-4/inbox/<fill-name>/` on the exchange branch. Run `git pull --rebase` first,
do not force, and touch nothing else there. Also attach the final zip in chat. Do not push to
any other branch, and do not open a pull request. The maintainer lands the delivery as a gated
PR into `complexity/ram-simulation`.

## Tier 2 addendum (jobs A–E; Seyoon, 2026-11-18)

Tier 2 proves the 15 statements of PR #372 (gate 162, CLEAR) and then the two targets
`WordRAM.exists_simulation` and `WordRAM.exists_ndSimulation`. Five jobs run **in parallel**, all
on the same base. The design is `campaign/items/ram-tm/TIER2-DESIGN.md`; the statements' gate
pack and findings are in `campaign/gates/162-ram-tier2-statements/`. Read the auditor's notes
there: several give routes.

These rules extend or replace the ones above, for tier 2 only:
- **Proved modulo the other jobs.** You may cite the tier 2 statements owned by other jobs
  exactly as stated. Your brief lists which. Each target's dependency walk may then list those
  statements, and nothing else that is admitted. Never cite `Turing.exists_tableFindTM`,
  `Turing.exists_tableAppendTM` or any other declaration admitted in `Build/RecordTable`.
- **Files.** The jobs are larger than earlier fills (Seyoon: larger jobs, run in parallel).
  - Jobs A, B and C keep their helpers `private` in their owned files. If a file passes about
    1,500 lines, keep going and say so in the report: the maintainer splits it at landing.
  - Jobs D and E may add new files under `TCSlib/Complexity/RAMSimulation/Sim/`, as their briefs
    say. Their declarations are public in the namespace `WordRAM.Sim`: the simulation's internal
    namespace (decision D1), not an API for other consumers. Each new file has the standard
    header, a module docstring, docstrings with proof sketches, and is imported by the owned file
    that needs it. List every new file and public declaration in `REPORT.md`.
- **Reuse.** The construction layer is `TCSlib/Complexity/TuringMachine/Build/`. Compose with
  `Turing.Contract` (`Build/Contract/*`): `Contract.ofReaches` turns a `ReachesWithin` row into
  a contract, and `Contract.seq`, `inPhase`, `branch` and `embed` compose and place them. Cite the
  catalog's rows (`copyTM`, `compareTM`, `clearTM`, `scanTM`, `skipTM`, the seek family,
  `writeConstTM`, `rewindTM`, the counters) and their contracts, rather than writing a transition
  table, wherever one fits. A hand-built machine is fine where none fits; its docstring says
  what was missing.
- **Checkpoints** are welcome: push `<fill-name>-checkpoint-N.zip` at each proved target.
- **Missing readers (Seyoon, 2026-11-18).** Rule 2's E-READER stop is relaxed for pure
  restatements. Suppose you need to read another file's definition and its file publishes no
  equation for it. Then add the reader yourself, **beside the definition in its home file**:
  - its statement restates the definition exactly (an equation `D … = body`, or an equivalence
    `P … ↔ body` for a `Prop`);
  - its proof is `rfl` or `Iff.rfl`;
  - its docstring says what it reads.

  Then continue. List every such reader in `REPORT.md`, with its file. The maintainer gates it
  with your PR and reconciles duplicates between parallel jobs. Anything more than a restatement
  is still a stop: a lemma that needs a proof, a `private` lemma made public, a changed statement.
  Before adding a reader, check that it is not already published, including by PR #375 (below).
- **Readers published since dispatch** (PR #375):
  - `Build/RecordTable`: `tableFields_eq`, `tableWF_iff`, `tableAt_iff`;
  - `Build/Catalog`: `catalogTrace_eq`, `mealyRun_nil`, `mealyRun_cons`, `scanResult_eq`, and
    `mealyRun_append`, `mealyRun_induction`, `mealyRun_length`, `mealyRun_next`, now public;
  - `Programs/WordRAM/Steps`: `inRange_iff`.

## ===== campaign/items/ram-tm/briefs/fill-ram-phases-r3.md =====

# RAM fill (Codex), tier 2 job D, round 3: repair the phases' duplication (gate 170)

Read `COMMON.md` (bundled), its tier 2 addendum included; its rules bind. **Fill name:**
`fill-ram-phases-r3`. **Base:** the commit given in the dispatch prompt. It is PR #386's branch
`ram/fill-phases`: your round-2 delivery, landed unchanged, with the RAM branch merged in.

## What this is

Gate 170's audit (`gates/170-ram-phases/findings.md`, bundled) found your round-2 proofs sound
(G170-05, -06, -07). It held them on two majors, both about duplicated proof text. Seyoon ruled
(2026-11-18) that you repair both in this round rather than record them as debt.

1. **G170-01: re-derived segment algebra.**
   - `phase_reaches_trans` (`Sim/PhaseHost.lean`) repeats the argument of the published
     `Turing.Segment.trans` (`Build/Contract/Basic.lean`): `runFrom_add` and the two prefix
     splits.
   - `phase_reaches_zero` (`Sim/PhaseControl.lean`) repeats `Turing.Segment.zero`.
   - **Repair:** convert the `ReachesWithin` witnesses through `Turing.segment_iff`. Put both head
     predicates within the summed radius about the original heads, cite `Segment.trans` and
     `Segment.zero`, and recover `ReachesWithin` through `Turing.reachesWithin_iff`. Keep a thin
     public wrapper only if its callers need the `ReachesWithin` form; its proof must then be the
     citation, not the argument.
2. **G170-02: the one-exit and two-exit structures.**
   - `PhaseBlock` (`Sim/PhaseBlock.lean`, one exit) and `PhaseBranch` (`Sim/PhaseTests.lean`, two
     exits) duplicate their composition (`PhaseBlock.seq`, `PhaseBranch.seq`).
   - They also duplicate their fresh-entry packaging (`phase_machine_ofBlock`,
     `phase_machine_ofBranch`): the seam construction, run composition, constant absorption and
     the zero-time prefix.
   - **Repair:** one certificate over a finite exit family. For example, a structure with an exit
     type `E` (`[Fintype E] [DecidableEq E]`), an injective exit map, and a selected exit per input
     and data. Give one `seq` (a one-exit block followed by any certificate) and one packaging
     proof, with the one-exit (`E = Unit`) and two-exit (`E = Bool`) cases as specializations.
     Callers move to the unified form, or to thin specializations proved by citation.
   - If a full unification is impossible, share at least the composition and the fresh-entry
     packaging proofs, and say in `REPORT.md` exactly what remains duplicated and why.

## Rules for this round

- **Statements:** `WordRAM.Sim.exists_phase` and `WordRAM.Sim.exists_verdictPhase` stay
  byte-identical, and so does every statement outside your owned files.
- **Owned files:** `TCSlib/Complexity/RAMSimulation/Sim/Phase*.lean` and `Sim/Phases.lean` (proof
  bodies only for the two targets). You may add, merge or remove `Sim/Phase*` files. Keep the
  `RAMSimulation` facade's imports and contents in step, and keep every file under 600 lines.
  Public declarations stay in the internal namespace `WordRAM.Sim` (decision D1).
- **Admissions:** none allowed. Since round 2, the twelve row statements your proof cited are all
  proved on the RAM branch (PRs #385, #388, #389), so both targets must reach **no** admission.
  Give the full type-and-value walk for both targets in `REPORT.md`.
- **Readers:** your round-2 reader `Turing.Cfg.select_eq` is already on the branch (from #388),
  identical in statement. The base keeps one copy; do not add it again.
- **Copy screen:** run `scripts/copy-text-screen-v3.py` over your owned files together with
  `Build/Contract/Basic.lean`, `Build/Contract/Seam.lean`, `Build/Seam.lean` and
  `Build/NDHost.lean`. Report every pair at or above half, with the reason it remains.

## REPORT.md, in addition to COMMON's checklist

- **The refactor:**
  - the unified certificate and its specializations;
  - the declarations removed, merged or renamed, and where each caller moved;
  - the line counts per file, before and after.
- **G170-01:** the citations of `Segment.trans` and `Segment.zero`, and what remains of the
  wrappers.
- **The walk:** the admission walk for both targets (empty), and the axiom prints.
- **The copy screen** over the population above.

## Downstream check

`Sim/Phases`, the `RAMSimulation` facade, and `Simulation` and `Classes` (they import the phases
through the facade's closure).

## ===== campaign/gates/170-ram-phases/findings.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| G170-01 | major | `Sim/PhaseHost.lean:130` · `phase_reaches_trans`; `Sim/PhaseControl.lean:56` · `phase_reaches_zero` | New public helpers re-derive the published segment algebra. | `Build/Contract/Basic.lean:465`, `Turing.Segment.trans`, already proves the same-machine concatenation by `runFrom_add` and the same two prefix splits. `phase_reaches_trans` repeats that argument; its additional work is transporting and enlarging the radius bounds. `Turing.Segment.zero` at line 444 likewise supplies the empty-run fact. `Basic.lean` is outside the copy screen's 30-owner population, so the 93 dispositions do not cover these re-derivations. `PhaseHost` has three source declarations; this affects one of them, exceeding the one-fifth review threshold. | Convert the witnesses through `segment_iff`, put both head predicates within the summed radius about the original heads, cite `Segment.trans`/`Segment.zero`, then recover `ReachesWithin`. If the re-derivations remain, **human acknowledgment required**, with their canonical home and repayment schedule recorded. |
| G170-02 | major | `Sim/PhaseBlock.lean:90`, `Sim/PhaseBranching.lean:50,86`, `Sim/PhaseControl.lean:172`; `PhaseBlock` / `PhaseBranch` | The disclosed single-exit/two-exit duplication remains unapproved debt, and its cumulative accounting is missing. | The screen records 661/747 normalized source characters shared by the two `seq` proofs, and 806/1035 shared by the two phase packagings. Inspection confirms repeated seam construction, run composition, constant absorption and fresh-entry packaging. This affects both substantive proofs among `PhaseBranching`'s three source declarations. Labeling the pairs `parallel` and asking the auditor's judgment supplies neither human acceptance nor the per-file copied-material ledger required by `workflow.md` §4. D1 authorizes public internal homes, not debt acceptance. | Factor a certificate over a finite exit family, with single-exit and Boolean specializations, or at least share the composition and fresh-entry packaging proofs. Otherwise **human acknowledgment required** under audit-template failure mode 5. Record cumulative per-file copied declarations/spans, fractions, and where and when the accepted debt will be retired. |
| G170-03 | minor | `pack.md` · admission-check claim; embedded `kit/checks/metadata.py:89`; `DATA-CARRIER.json` | The metadata allowance does not establish the named admission frontier, and the full walk is omitted from the bundle. | The checker permits `sorryAx` whenever `inherited_admissions` is nonempty; it does not check which admitted declarations are reached. Its boundary traversal stops at other theorem bodies and foreign definition values. I retrieved the original `inbox/fill-ram-phases/fill-ram-phases-r2.zip` (SHA-256 begins `dc74647015a2f4ba`), verified its 536 checksum entries and all 30 delivered source files against this head, and checked its full traversal and log: all 380 roots stay within the allowance, `exists_phase` reaches exactly the stated 12 declarations, and `exists_verdictPhase` reaches none. | Include `FinalAxioms.lean.txt`, `final-axioms.log`, `final-admissions.json` and the target summary in the gate evidence. Describe the kit check as an axiom allowance, and the full walk as the check of named dependencies. |
| G170-04 | minor | `BUNDLE-FILES.txt`; `evidence/CITATION-HOMES.json` | Ten reported citation homes are missing from the self-contained bundle. | The citation inventory lists 16 home files; six are included. Missing examples are `Build/Catalog.lean`, `Build/Contract/Reach.lean`, `Build/Contract/Seam.lean`, `TuringMachine/CfgFacts.lean` and `Programs/WordRAM/Steps.lean`. The remaining omissions are enumerated by the same inventory. I retrieved the missing sources at the audited Lean pin to complete the review. | Include all ten omitted homes at `09546b899d451b693e80588bd625e6b476eb930b`, updating the section list and checksums. |
| G170-05 | note | Instruction schedules, `PhaseTable`, `PhaseCoin`, `PhaseEmit`, `exists_phase` | The inspected construction preserves the intended instruction semantics in the boundary cases. | At width zero, word values and absent-cell defaults are empty lists, while table-field markers retain a valid layout; a coin still increments the RAM coin counter and emission appends `false`. Indirect store saves the original source value before constructing the computed key, including aliasing addresses. A negative operand with `bltz` targeting its own program position selects the live jump exit. Empty input and negative/out-of-range input positions produce zero. The coin source has one stationary choice-sensitive transition and no transition targets its entry; its continuations are deterministic. | No correction required. Useful permanent sanity lemmas would cover zero-width coin/emission, aliasing indirect store and a self-targeting signed branch. |
| G170-06 | note | `PhaseLayout`, `PhaseBounds`, `PhaseFork`; `Phases.exists_verdictPhase` | The footprint, common allowances and verdict behavior match the interfaces. | The exact layout is `1 + es.length * ((W + a) + W + 4)`, including the empty-table case. The memory charge fits `(a + 4) * ((T.card + 1) * (W + 1))`; the arithmetic charge absorbs `(W + 1)^2`, and the input allowances retain binary-length work radius. Positive common units absorb seam/host dispatches; restored work heads keep the radius center fixed. The verdict machine takes one stationary step, preserves function-mode output, emits `[v]` in verdict mode and halts. | No correction required. |
| G170-07 | note | Bundle integrity, freeze, readers and verification receipts | The pinned sources and supplied verification receipts are consistent. | Both `SHA256SUMS` entries pass; all 56 sections match their designated Lean/records commits after removing bundle formatting. All 1,186 recovered files and 839 unique blobs verify. The supplied replay's 268 successful receipts have matching log hashes and compiled-source blob IDs at the audited head. The 154 seal checks match their owner-source hashes; the 70 controls/140 paired identities cover all 66 ordinary metadata heads. All eight existing `Phases` signatures and six complete control declarations are unchanged. The three home-file insertions are exactly the stated `rfl` readers, with no simp/unfold attributes or axioms. | No correction required to these checks. |

**Verdict: HOLD — 0 blockers, 2 majors, 2 minors, 3 notes.**

## ===== campaign/gates/170-ram-phases/pack.md =====

# Gate 170 · RAM simulation, tier 2 job D: the phase interfaces (PR #386)

**Not yet clear to merge.** PR #386 is a draft into `complexity/ram-simulation`. It proves the
two phase interfaces of `RAMSimulation/Sim/Phases` (#372), the per-instruction phases of the
stage-2 machine (Codex fill `fill-ram-phases`, round 2). Codex audit approved by Seyoon on
2026-11-18. Seyoon dispatches and merges.

- **Lean head:** `09546b899d451b693e80588bd625e6b476eb930b` (branch `ram/fill-phases`), on the
  RAM branch after #379 (`3d2a6960`). One commit: the fill's patch, landed unchanged
  (`fill-ram-phases-r2.zip` SHA-256 `dc746470…`). The patch reproduces all 30 delivered files
  byte for byte.
- **Since the replay:** #385 (job A, the word rows) merged into the RAM branch. It changes only
  proof bodies of `Build/WordArith` and adds one reader in `StateRenaming`, with no statement
  changes, so this PR's replay is unaffected. #383 (job E) and #388 (job C) touch the same facade
  and `Build/Embed`. The second to merge takes the union of the facade's imports and keeps one
  copy of the identical reader `Turing.Cfg.select_eq`.
- **Rulings that bind:**
  - tier 2 design D1: public homes `RAMSimulation/Sim/*` under the internal namespace
    `WordRAM.Sim`;
  - D2: reuse `RecordTable`'s layout;
  - the standing reader rule: pure `rfl`/`Iff.rfl` readers beside a definition in its home file.

## What it adds

| Target | Status |
|---|---|
| `WordRAM.Sim.exists_phase`: a phase machine for every extended-RAM instruction | proved modulo the 12 row statements of jobs A, B, C |
| `WordRAM.Sim.exists_verdictPhase`: the verdict phases | proved, no admission |

**The 12 row statements** are `Turing.bvBits_injective`, `exists_wordAddTM`, `exists_wordSubTM`,
`exists_wordMulTM`, `exists_wordHalfTM`, `exists_wordSignExtendTM`, `exists_wordIntTM`,
`exists_wordSignTM`, `exists_wordNonzeroTM`, `exists_keyLookupTM`, `exists_keyAssignTM` and
`exists_inputBitTM`. The nine `Build/WordArith` statements are proved in #385 (merged).
`exists_keyLookupTM` and `exists_keyAssignTM` are proved in #389, and `exists_inputBitTM` in
#388.

**The modules:**
- 25 new modules `Sim/Phase*.lean`, each under 600 lines (inventory in `REPORT-phases.md`). They
  hold layout and table invariants, frames and rows, blocks and schedules, memory and input
  machines, tests and branches, the coin fork, and emission.
- `Phases.lean`: the two target bodies, importing the new modules.
- The facade lists the new modules.
- Three pure readers: `Turing.Cfg.select_eq` (`Build/Embed`), `Turing.seamCompTM_tr_inl`
  (`Build/Seam`) and `Turing.NDTM.phaseHostND_tr` (`Build/NDHost`).

## Brief for the auditor

1. **The construction.** Each instruction's phase must implement `xstep` on the encoding, as
   `exists_phase` states:
   - immediate addresses become keys;
   - keyed lookups fetch the operands;
   - a word or input row computes the result;
   - one keyed assignment updates the table;
   - indirect stores fetch their value before building the computed key;
   - `bltz` uses the sign test with two live exits;
   - `emit` uses the nonzero test and an optional-output leaf;
   - `coin` is one stationary choice in `NDTM.phaseHostND` with two deterministic continuations
     joined at `next`.

   Check that the encoding (`Encodes`, `TableOf`) is preserved, including width zero and absent
   cells. Check the footprint charge: the table has exactly
   `1 + entries·(keyWidth + valueWidth + 4)` cells.
2. **The bounds.** The common units `phaseTime` and `phaseSpace` must dominate every row's
   allowance (table scans, linear rows, quadratic multiplication, input length) and match the
   interface's `C·((T.card + 1)(W + 1) + W² + n + 1)` and radius.
3. **The verdict phase:** its one-step optional emission and halt, with the work heads
   unchanged.
4. **Admissions:** `exists_phase` reaches exactly the 12 row statements, and
   `exists_verdictPhase` none (the fill's walk; the metadata check, whose allowance is exactly
   those 12). Nothing in `Build/RecordTable` is reached.
5. **The public surface.** D1 allows public declarations in `WordRAM.Sim`; flag any that
   duplicate a library result.
   - **In particular, `PhaseBlock` (one exit) and `PhaseBranch` (two exits).** Their `seq`
     compositions and their `phase_machine_ofBlock`/`ofBranch` packagings share most of their
     text and differ in the exit set (copy screen, class `parallel`). Should they be merged
     into one structure over a finite exit family before this lands, or is the duplication
     acceptable?
6. **Readers and rule 10:** the three readers restate their definitions, and the seals pass.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay on `oleans-cl166-cl165`, 268 modules: 268 passed,
  0 failed.
- **Seals:** pass, 154 proofs and 66 heads. The metadata allowance is the 12 row statements.
- **Controls:** 70 definitions and 140 identities in two parts, native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 0 read candidates in 154 roots. Citation homes are
  in `CITATION-HOMES.json`.
- **Copy screen:** 50 → 143 pairs, 93 new, all classified (`PAIR-DISPOSITIONS.json`). They are
  record-shape matches of configuration builders, instances of the shared row placement
  `phase_wordRow`, block and schedule compositions, and per-instruction certificates. The
  `PhaseBlock`/`PhaseBranch` family is raised in item 5.
- **The fill's report** (`REPORT-phases.md`): axiom prints, the admission walk, the module
  inventory, and the foreign definitions with their readers.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate170-ram-phases-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== workflow.md =====

# TCSlib Formalization Workflow

How large formalization campaigns are run in this repository. [`policy.md`](policy.md)
says what landed Lean code must look like; this document says what *process* produces
it. The reference implementation is the Arora-Barak campaign
(`AroraBarakChapter1Plan.md`, complete and audited end to end;
`AroraBarakChapter2Plan.md`, in progress) — file paths below cite its artifacts as
worked examples. Where an older document describes a mechanism this one supersedes
(e.g. the PR-based fill delivery in `AroraBarakChapter1Plan.md` §5, since replaced by
zip delivery), this document records current practice.

```
plan  →  statement phases  →  audit gates  →  fill campaign  →  closure
          (sorry-skeletons)    (per phase)     (epochs/batches)   (attestation, final
                                                                   audit, blueprint)
```

The load-bearing idea: **statements are audited before proofs are attempted.** Lean
already checks proofs; the dominant failure mode of formalization is a wrong or
subtly-weakened *statement*, and that is cheapest to catch while everything is still a
`sorry`. Every phase therefore lands as a compiling skeleton, passes an adversarial
external audit gate, and only then becomes fill work.

## 1. The campaign plan

Each campaign (typically one textbook chapter) begins with a plan file at the repo
root — `<Source>Chapter<N>Plan.md` — containing:

* **Scope**: which results are mandatory core, which are deferred, with source
  citations.
* **Foundation decisions**: the definitional conventions, each with its rationale
  (these are where audits bite; see §3).
* **Architecture and module layout**: directories, namespaces, facades, per policy §1.
* **Phasing**: the statement phases and the anticipated fill epochs.
* **Risks and honest effort assessment**.
* **Open design questions (human review required)**: decisions reserved for a human
  maintainer. Audit rounds *verify* these but never *dispose* of them; each records
  the maintainer's provisional choice and stays open until a human closes it. The
  consolidated register — full statements, cross-links, and status — is
  [`backlog.md`](backlog.md); the plans keep stable numbered stubs, which is what
  audit documents cite.
* **Decision log**: an append-only table. Every methodological decision, every audit
  round's verdict, and every repair round gets a row. The log is the campaign's
  memory; when a decision is reversed, the old row is marked **Superseded** in place,
  never deleted.

## 2. Statement phases (sorry-skeletons)

A phase lands the definitions plus the theorem *statements* of one coherent slice,
every proof a `sorry` under a policy-grade proof sketch (policy §3: the sketch is
written at skeleton time and is the plan; a skeleton whose sketch cannot be written is
not ready to land). Ground rules:

* Definitions and sorried statements only. Proofs appear in a skeleton only for
  definitional-unfolding lemmas whose home module mirrors proved infrastructure (the
  precedent: the `runWith` algebra of `TuringMachine/Nondeterministic.lean`, mirroring
  the vendored `runFrom` lemmas), and any such deviation is flagged in the audit pack
  with the proofs declared part of the audited surface.
* Sketches name their obligations: a sketch that will need a machine construction
  names each sub-machine as an explicit fill obligation, so the eventual brief can
  inherit the list. It also names every **host** the route needs (policy §1, **Hosts come
  first**), from the registry in `machine-library-design.md` §14. A sketch that needs an
  unregistered host is not ready: the host's public contract is a statement-phase item of
  its own, gated before the consumer's fill.
* Everything gate-verifies before commit: per-module checks plus a full fresh sweep
  (§6), style lint, and the headline axiom prints.

## 3. Audit gates (between phases)

Right after a skeleton lands — statements frozen — an **external adversarial audit**
runs before any fill or any next phase. The auditor is an LLM from a different vendor,
in a fresh context, reviewing the trusted surface (definitions, statements, sketches,
and any skeleton-time proofs) against the source text.

**Artifacts**, committed under `audits/` with campaign-scoped names
(`ch2-phase1-*`, `epoch4-*`), except the bundle:

* `…-pack.md` — the auditor's instructions: the audited commit, repository-side
  attestations (freeze by path enumeration, sweep results, admission inventory, axiom
  prints, lint — stated so the auditor can verify or challenge them, with source facts
  kept separate from maintainer execution claims), the under-audit inventory, a
  prioritized brief (the plan's seeded design questions go here), and the findings
  table format with the severity guide: **blocker** (a downstream phase would build on
  a wrong statement) / **major** (fixable but materially misleading) / **minor** /
  **note**. `campaign/standards/TEMPLATE.md` is the skeleton.
* `…-bundle.md` — a single uploadable file: the pack verbatim, then every attachment
  under a `## ===== <path> =====` header (prior findings, both plans, `policy.md`,
  the root, and the full module tree). **Not committed** (user, 2026-10-15): it is kept
  in the local dispatch folder, and the resolutions record its SHA-256 and section
  count. Bundles committed before then are indexed in `campaign/BUNDLES.md`, with how to
  retrieve them from history.
* A short kickoff message (drafted per round, pasted by the maintainer into a fresh
  auditor chat with the bundle attached).
* `…-findings.md` — the auditor's report, preserved **verbatim**, including anything
  the maintainer disputes. Pack errata found later are acknowledged in the resolutions
  file; shipped packs are never edited retroactively.

**The gate rule**: a gate closes only on a round reporting **zero blockers and zero
majors**. A round with majors triggers repairs and a full re-audit round (minors may
be swept in the closing commit and re-verified). Repairs adopt the auditor's own
constructions where supplied, are re-gated, and are recorded in the decision log; when
the loop closes, `…-resolutions.md` summarizes every round, every repair, and the note
dispositions. The complete worked example is the three-round
`campaign/gates/ch2-phase1{,-reaudit,-round3}/{pack,findings,resolutions}.md` loop.

Audits complement, never replace, in-Lean sanity theorems — the machine-checked and
permanent form of the same checks.

## 4. The fill campaign (epochs and batches)

With all phase gates closed, the audited-true sorries are filled in **epochs** —
sequential, ordered by risk retirement, with an audit round at each epoch boundary —
each consisting of **batches** run in parallel by cloud agents with disjoint file
ownership, from self-contained briefs in `briefs/`.

**Binding batch ground rules** (full text repeated in every brief):

1. **Exclusive file ownership.** Helpers live `private` in owned files; a lemma that
   belongs in a shared file is *requested* in the report and added serially at epoch
   merge, flagged for the next audit. **Hosts are the exception** (rule 4).
2. **Statement freeze.** Audited declarations are never renamed, re-signatured, or
   re-stated by fill work. A target that looks unprovable as stated is an
   *escalation*, reported with the obstruction — never "fixed" inline.
3. **Verification per batch**: the check script (§6) over the owned files, zero
   `error:` lines, sorries only at documented out-of-scope items.
4. **Hosts first** (user, 2026-10-12; policy §1). A batch never builds a search,
   recursion, interpreter, runner or input device as a private one-off. It cites the
   registered public host its brief names. If the route turns out to need a host the
   brief does not name, that is an escalation, reported with the contract the batch
   would need; the batch continues on its other targets.

**Hosts in briefs.** A fill brief is issued only when every host its route needs is
registered (`machine-library-design.md` §14) and the host's statement gate has closed. The
host's own fill may run in the same wave, in its own batch, with consumers citing it under
the proved-modulo rule. The readiness check for any target lists the hosts it needs. A
private host already in the tree is harvested (a promotion PR and its gate) before a second
consumer is briefed against it.

**Delivery is by zip, not PR.** Each batch returns an archive containing `REPORT.md`,
the full source files, a `git format-patch` series, a git bundle, the batch's sweep
log, the axiom-print log, and `SHA256SUMS`. The maintainer verifies before
integrating: checksums; the statement freeze (comment-stripped comparison of every
audited signature); enumeration of any removals; public-declaration drift; a full
fresh sweep; the headline axiom prints; and the **duplication ledger** — every
private copy of existing proved material in the delivery enumerated, with each
touched file's cumulative copied-material count and fraction. If a delivery pushes a
file past **one fifth copied material**, or adds copies to a file that already
received copies in an earlier epoch, the maintainer opens a `backlog.md` §1
human-review item before the epoch's audit pack ships — no discretion. Integration
is `git am -3` from the patch series, preserving the agent's authorship. Large fills that exhaust one agent's budget
continue via a continuation brief to a fresh agent (the `universal` B2 precedent).

**Counting public names** (user, 2026-10-22; gate 59). Public-declaration drift, the statement
freeze and a brief's "no new public declaration" rule count **public declarations**: the
declarations the source introduces without `private` (`theorem`, `lemma`, `def`, `abbrev`,
`instance`, `structure`, `inductive`, `class`), counted by the comment-aware source census
(`devtools/seyoon/declfreeze.py`). Packs say so ("N → N public declarations, at source"). A
**public constant** is a non-private name in the module's elaborated environment (the axiom
probe's walk of the module's publics). Packs and reviews report a module's new public constants
separately, by kind:
- a declaration's compiler auxiliaries (`_proof_N`, `_simp_N`, `match_N`, `eq_N`, `eq_def`,
  `congr_simp`);
- the instances that `deriving` generates for a **private** type, which Lean 4.25 names publicly
  (e.g. `instDecidableEqSl_Key`).

Neither kind is a public declaration. A derived instance of a private type needs no finding when
its type is private to its file and a name check over the tree and the open PRs finds no clash;
where a derived name would clash, write an explicit `private instance`. Any other new public
constant is reported as a finding.

**Epoch boundaries**: the maintainer re-runs the full sweep, produces a **drift
attestation** (§6), and prepares the epoch's audit pack with elaboration evidence
and the epoch's **duplication ledger**, which the auditor verifies independently
(audit template failure mode 5); the epoch's gate follows the same
zero-blockers/majors rule as phase gates, and a debt major closes only by explicit
human acknowledgment recorded in the resolutions file. Once a family is
acknowledged, later corrections to its accounting are minors (audit template
failure mode 5) and do not hold the gate; the ledger is still corrected.

### 4.1 External workers and the exchange branch

Most of a campaign's labour is done by external workers in fresh chats. The maintainer
prepares every job so that the user's part is only to paste a prompt into a new chat,
relay what comes back, and merge PRs. An **exchange branch** carries the inputs and the
deliveries between them.

**The exchange branch.** It is an orphan branch per campaign (for example
`exchange/pass-shelat-ch5-8`), never merged anywhere and never merged into. Several
campaigns may share one, each in its own folders; nobody edits another campaign's paths.

| Path | Holds | Written by |
|---|---|---|
| `outbox/gates/<gate>/` | an audit pack: README, pack, bundle, `SHA256SUMS` | maintainer |
| `outbox/fills/<unit>/` | an issue package: brief, environment addendum, module order and Mathlib roots, base admissions, `SHA256SUMS` | maintainer |
| `outbox/ingests/<job>/` | a source-ingest brief | maintainer |
| `inbox/fills/<unit>/` | a fill or statement delivery: checkpoints, then the final payload | worker (or maintainer intake) |
| `inbox/<name>-findings.md` | an audit's findings | worker (or maintainer intake) |
| `inbox/sources/` | source PDFs the user supplies for ingests (never on a campaign branch) | user |
| `archive/` | processed items | maintainer |

**Dispatch.** For each job the maintainer:
* writes the issue package in the campaign records (for example
  `briefs/<campaign>/fills/<unit>/issued-r1/`) and the same files in the exchange outbox,
  as a signed commit;
* writes `dispatch.md` beside it, holding the **pasteable prompt**. The prompt pins every
  revision by full hash: the exchange commit, the Lean base, and the records commit that
  holds the package. It also names the delivery route.

The user pastes the prompt into a fresh chat of the chosen worker and tells the maintainer
it is dispatched. The maintainer logs each step in the campaign's decision log.

**Worker routes.** Any route may take any job: audits, fills, statement drafts, ingests.
Each campaign records its standing defaults in its decision log.
* **Codex in the cloud.** Favoured for **audits and reviews**: a different vendor in a
  fresh context, as §3 requires. It cannot push to GitHub, so it returns its findings
  Markdown, or a ZIP with evidence, in the chat. The user uploads that file to the
  maintainer, who files it verbatim.
* **Codex in a local checkout.** One of the two leading options for **fills**. It runs on
  the user's machine with a full build environment (a lead plus sub-agents). It delivers
  either by pushing its payload to `inbox/fills/<unit>/` on the exchange, or by a ZIP in
  the chat.
* **Claude in the cloud.** The other leading option for **fills**. It pushes its payload
  to `inbox/fills/<unit>/` on the exchange: checkpoints as `fill <unit>: checkpoint <n>`,
  then `fill <unit>: final`. The exchange history pins the delivery, so no ZIP is needed.

**Lean parallelism** (user ruling, 2026-11-17). **Local hosts** (the maintainer's
container, or a local checkout on the user's machine) share their CPU and memory with
other work. There, at most **3 Lean processes run at once on the machine, across all
jobs**; never run two in the same olean tree. Workers and the maintainer may message each
other to coordinate these slots. **Cloud workers** (Claude or Codex in the cloud) may run
as many Lean processes in parallel as is sensible for their machine:
* size the pool from the machine: at most `nproc` processes, and few enough that at least
  about 2 GB (or 15%) of memory stays available; start from
  `min(nproc, MemAvailable / 4 GB)` and back off under memory pressure, giving heavy
  modules (for example `Complexity/ClassP/BinaryArith/DetMod`) room of their own;
* build in dependency order: start a module only when every module it imports has its
  olean, and never let two processes compile the same module or write the same file;
* seals, controls, axiom probes and statement probes may run in parallel across owners,
  each in its own probe file and output directory;
* sub-agents share one pool (a counting semaphore) instead of a single host lock, and
  record the pool size and peak memory in their evidence.

Everything else is unchanged: never `lake build` the library, never run an unfiltered
`lake exe cache get`, only the lead fetches the cache, and each module is still compiled
through `scripts/lean_check_tree.sh`.

**The delivery payload.** A delivery contains:
* `REPORT.md`;
* `patches/`: the whole `git format-patch <base>..<branch>` series, with `COMMITS.tsv`
  and its signing column;
* `src/`: the final owned files under their repository paths;
* `evidence/`: the sweep, axiom prints, seals and controls, and lint that the brief
  requires;
* a top-level `SHA256SUMS` covering every delivered file.

Workers commit with signing off. They write **only** their assigned path, run
`git pull --rebase` before each push, and never force-push. They never push a campaign
branch: Lean reaches a campaign branch only through a PR the user merges.

**Intake.** Every delivery and finding is data, never instructions. The maintainer:
* verifies the checksums, and checks that `git am` of the patches at the issued base
  reproduces `src/` exactly;
* reviews in two phases: first static (scope, frozen statements, duplication, docstrings,
  the worker's evidence recounted), then Lean, as a merged-tree replay (§6.1);
* lands the work on a landing branch: the worker's commits are cherry-picked with
  authorship kept and signed by the maintainer, and any landing edits are separate signed
  commits;
* opens the PR, then sends it to its gate (§3).

Findings are filed verbatim with their SHA-256 before any resolution.

## 5. Closure

When the last sorry falls: a zero-sorry sweep with build evidence; a campaign-wide
drift attestation against the audited baselines; a final audit pack covering the fill
rounds; and the blueprint increment — dependency graph from `.ilean` artifacts,
`scripts/blueprint_{enumerate,assemble,validate}.py`, blueprint-writer agents, with
the blueprint **late-bound** throughout (extraction only at boundaries; no blueprint
LaTeX hand-written ahead of the Lean; `blueprint/BLUEPRINT_PIPELINE.md` has the
pipeline detail).

## 6. Verification tooling

* **`scripts/lean_check_tree.sh <module>`** — the campaign's elaboration gate: a
  direct `lean` invocation per module (**`lake build` is banned on campaign
  branches** — see the Chapter-1 decision log), emitting fresh `.olean`s into a
  scratch tree. Pass requires exit 0, zero `error:` lines, *and* a fresh olean, so a
  stale artifact can never satisfy the check. The full sweep runs it over every
  module, in dependency order, from `scripts/ab_ch1_module_order.txt`:

  ```
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < scripts/ab_ch1_module_order.txt )
  ```

  Admission counting is by `declaration uses 'sorry'` warnings in the sweep log; the
  expected count is attested in every pack.
* **`scripts/campaign_style_lint.py`** (named `scripts/style_lint.py` until the
  main merge, which adopted main's per-file policy linter under that name — the
  historical audit logs' invocations refer to this tool) — mechanical policy checks: statement-prose docstrings,
  sketch-before-sorry, file sizes, `## References`, facade coverage, and (check 8, since
  2026-10-16) public definitions without a lemma beside them (`policy.md` §1, *Definitions
  land with their lemmas*). Campaign baseline: zero FAIL (legacy pre-campaign files outside
  the audited surface are tolerated and listed). Check 8 is a WARN listing names; a landing
  adds no name to it.
* **Axiom prints** — `#print axioms` for every headline theorem on the *fresh* olean
  tree: closed results must show exactly `[propext, Classical.choice, Quot.sound]`;
  sorried statements show `sorryAx`, and any other axiom is a stop-the-line event.
* **Drift attestation** — the anti-tamper check between audited baselines: strip
  comments from every module, compare both the **multiset** of declarations and the
  **ordered declaration sequence** against the baseline, and enumerate public
  declarations (gained / lost / changed) so that "nothing audited moved" is a checked
  claim, not an impression.
* **Vendored files** are frozen at their recorded upstream pin and periodically
  byte-compared against upstream; local modifications live only in the header list.

### 6.1 The olean snapshot and merged-tree replays

Full sweeps are slow because unchanged expensive modules (for example
`Complexity/ClassP/BinaryArith/DetMod`, about 25 minutes) are rebuilt every time a
check starts from an old base. Campaign chats keep their olean state at the branch tip
instead:

1. **One complete snapshot at the tip `T`.** Keep exactly one complete olean snapshot
   directory, outside any worktree, built at the current branch tip. It holds every
   TCSlib module's `.olean` (and `.ilean`), not an in-tree `.lake/build`. Record its
   object map (module path → SHA-256 of the `.olean`), the map's SHA-256, `T` and the
   module count in the campaign's records.
2. **Validate each PR by a merged-tree replay against that snapshot,** never against an
   older base:
   * compute the prospective merge with `git merge-tree --write-tree <T> <PR head>` and
     export that tree;
   * start the output directory as a hard-linked copy of the snapshot (`cp -al`, almost
     no disk);
   * rebuild only the PR's changed modules and their downstream import closure, in
     dependency order, one `lean` process per module (`scripts/lean_check_tree.sh`,
     never `lake build`), deleting each module's stale `.olean`/`.ilean` before
     compiling it so the hard link is broken and the snapshot is never written through;
   * require exit 0 and zero `error:`/`error(` for every module, then write the output
     object map and record the prospective tree hash. Seals, axiom prints and controls
     run against the output directory.
3. **On merge,** fetch the branch and run
   `git diff --name-only <merge commit> <prospective tree> -- '*.lean' lean-toolchain lake-manifest.json`.
   If it is empty, the replay output is exactly the merged code. Adopt it as the new
   snapshot (rename it, or hard-link it under a new name), rehash it on disk against its
   map (0 extra / 0 changed / 0 missing), and record the new map SHA-256, the merge commit
   as the new `T`, the module count and the date. Delete the previous snapshot's oleans
   but keep its manifest. No extra build is needed.
4. **If that diff is not empty** (another PR merged in between and touched the same
   closure), do not adopt: rerun the PR's replay on the new tip first. Better, before
   merging: when two open PRs share downstream modules, merge the one with the larger
   rebuild first, then re-replay the other (it rebuilds only its own closure).
5. **Housekeeping:** one Lean process per module; never interrupt a running build; on a
   local host, at most 3 Lean processes on the machine and one per tree (cloud workers:
   §4.1, *Lean parallelism*); pause if free disk falls below about 1 GB; discard replay
   outputs that will not be adopted once their evidence is recorded.

## 7. Relationship to the other documents

* [`ROADMAP.md`](ROADMAP.md) — a one-page orientation: the phases ahead and pointers to
  the documents that hold the detail.
* [`policy.md`](policy.md) — the standards this workflow enforces (modularity,
  attribution, sketches, review checklist).
* [`lean-glossary.md`](lean-glossary.md) — the Lean/Mathlib jargon appearing in
  declaration names and docstrings (fuel, Sigma, `Prop` vs `Bool`, the naming
  grammar, …), for readers fluent in TCS but not in Lean.
* [`AGENTS.md`](AGENTS.md) / `.claude/` — the sorry-ladder proof technique and agent
  roster; useful *inside* a fill batch, but campaign verification runs through §6, not
  through `lake build` or editor-only checks.
* [`blueprint/BLUEPRINT_PIPELINE.md`](blueprint/BLUEPRINT_PIPELINE.md) — blueprint
  generation and validation.
* [`.github/copilot-instructions.md`](.github/copilot-instructions.md) — main-branch
  build and CI; campaign branches deviate as recorded in their decision logs.

## ===== campaign/maintainer/WORKFLOW.md =====

> **Inherited (2026-11-17).** These are the Arora–Barak chapters 3–4 campaign's standing rules,
> copied unchanged to the RAM work branch `complexity/ram-simulation`. Read
> `complexity/arora-barak-ch3-4` as `complexity/ram-simulation` wherever a rule names the campaign
> branch. Where this branch's `campaign/README.md` differs, the README wins. The chapters 3–4
> records (gates, ledger, backlog) stay on that campaign branch.

# The maintainer's standing rules (Arora–Barak ch. 3–4 campaign)

The maintainer is an AI-assisted session (currently Codex). It builds PRs, replay scripts, gate packs, bundles and
fill briefs; reviews incoming audits and deliveries; and keeps the records. The user merges PRs,
runs or approves replays, dispatches gates and fills to external agents, and rules on decisions.
These rules were kept as the local session's memory until the move to a cloud VM (2026-11-04),
and are committed here so that any session can follow them. The state of the work is in
`HANDOFF.md` beside this file and in `campaign/backlog.md`.

Repository standards bind first: `policy.md`, `workflow.md`, `campaign/standards/TEMPLATE.md`
(the audit severity guide, failure mode 5 on duplication debt) and
`campaign/standards/fill-environment-addendum.md`.

## 1. Branches, PRs and merges

- **Only commits that change a `.lean` file go through a PR**, which the user merges. Everything
  else (packs, findings, resolutions, bundles, logs, evidence, briefs, designs, the backlog) is
  pushed directly to `complexity/arora-barak-ch3-4`.
- **Every Lean change gets a gate and a replay.** A PR is **clear to merge** only when its replay
  has passed and its gate has closed with zero blockers and zero majors (or the user waived the
  gate), and only when its base is the campaign branch. Retarget a stacked PR before calling it
  clear; stacked merges once stranded three PRs.
- **Say it in bold, one line per item:** "**Clear to merge: #N …**", "**Not yet clear to merge: #N
  (why)**", "**Ready to dispatch: …**", "**Ready to run: …**". State the status of every open
  campaign PR you mention.
- **Colleague-owned files are not edited** (`TimeHierarchy/Separation`, `ClockMachine`,
  `ClockLoop`, `CircuitComplexity/*`, and Hydroxyi's files), except under the user's explicit,
  narrow exceptions, each by PR and gate:
  - `TimeHierarchy/Diagonal.lean`'s parameterization in place;
  - mechanical dedup edits (copy deletions, re-points) in Hydroxyi's ARM files, with an FYI only;
  - the general Savitch's generalization of `SpaceComplexity/SavitchARM/*`, `Machines/*` and
    `Codec/*`, with an FYI only;
  - four `Iff.rfl` equations for the deepening (2026-11-05): `walkLe_zero_iff` and
    `walkLe_succ_iff` in `Logspace/PathWalk`, `rcode_iff_reflTransGen` and `winRun_iff` in
    `ExpBFS/Radius`, FYI only;
  - gate 89's re-points (#181's files);
  - one visibility change in `CircuitComplexity/DAGCircuitSat`.

  Interface design in a colleague's files waits for that colleague. FYIs are the user's to send.
  Never @-mention anyone in GitHub text.
- **Duplication debt in colleagues' code** goes to the user's own dedup window (12.2c), not back
  to the colleague. Colleagues keep correctness and audit fixes.

## 2. Lean

- **Never `lake build`.** Elaborate only through `devtools/seyoon/leanelab.sh <worktree> <olean
  dir> <file>` (plain) or `leanelab-o.sh <worktree> <olean dir> <file> <overlay>` (writes the
  `.olean`), each `lean -j4` under `nice -n 10`. Replays use
  `scripts/lean_check_tree.sh` through the generated replay scripts. **Open, deferred by Seyoon
  (2026-11-17):** the current replay driver compiles each module through `leanelab-o.sh`, holding
  a slot lock and writing only to its overlay. It applies the same pass test itself: the stale
  outputs are removed first, then it requires exit 0, no `error:` line and a fresh non-empty
  olean. Keep using it until Seyoon rules on whether to switch.
- **Lean parallelism on the cloud machine** (Seyoon's ruling, 2026-11-17; `workflow.md` §4.1 on
  main, PR #353). The pool is `min(nproc, MemAvailable / 4 GB)`, keeping at least
  max(2 GB, 15%) of memory available, and it backs off under memory pressure. It is computed by
  `$TCSLIB_SCRATCH/rd/leanpool.sh`, capped at the wrappers' five slots, and exported as
  `TCSLIB_LEAN_SLOTS` by `env.sh`. On the current machine (4 cores, 16 GB) the pool is 3. The
  slot locks under `$TCSLIB_SCRATCH/locks/` are the one counting semaphore that the maintainer
  and sub-agents share.
  - **Order.** Build in dependency order: start a module only when all of its imports have
    oleans. No two processes may compile the same module or write the same file.
  - **What runs in parallel.** Seals, control parts, sweep probes, axiom probes and statement
    probes may run in parallel across owners, each with its own probe file and log.
  - **Evidence.** The replay driver records the pool size and peak memory in `RESULT.json`.
  - **Local hosts** keep their limit of at most 3 Lean processes per machine.
- **Screens one at a time**, machine-wide: `scripts/copy-text-screen-v3.py` under `nice -n 10`,
  holding `$TCSLIB_SCRATCH/locks/screen` (`mkdir` to take it, `rmdir` to release; a lock with no
  running screen process is stale).
- **Every new worktree needs the Mathlib link:** `mkdir -p <wt>/.lake && ln -s
  <main checkout>/.lake/packages <wt>/.lake/packages`. Replay scripts precheck it. A failed
  replay has deleted oleans from its snapshot copy, so the copy must be discarded.
- **Snapshots and replays:**
  - A snapshot is a compiled olean tree of a known Lean tree, recorded with the commit it matches.
  - To compile a change before its replay, make a copy-on-write clone of the snapshot and compile
    into it. Partial `LEAN_PATH` overlays fail.
  - **Merged-tree replay:** when several PRs have merged since the last common snapshot, replay
    the downstream closure of *every* `.lean` file changed since that snapshot's tree, on the
    merged tree, chained from that snapshot. Never compose snapshots.
  - Replay lists never contain the root `TCSlib`: snapshots cover only `Complexity`,
    `BooleanAnalysis`, `Programs` and `ComputationalModels`.
  - `devtools/seyoon/mk-next.sh` merges the campaign into a PR branch and writes the chained
    replay (`mkdownmulti.py`, `mkreplay.py`), with its precheck. Evidence copies of `.lean` files
    are named `.lean.txt`, so that the scripts' Lean-tree checks ignore them.
- **Rule 10 binds the maintainer's own API proofs:** read other files' TCSlib definitions only
  through their published equations. Core and Mathlib definitions may reduce by `rfl`, `decide`
  or `show`, but are never passed to `simp`, `rw` or `unfold`.
  - **Check:** a sealed copy (`attribute [local irreducible]` on every other-file TCSlib
    definition reached; `attribute [-simp]` on the `@[simp]` ones that exist in the closure),
    each new section moved into its own `section` in a scratch copy.
  - **Controls:** an `rfl` delta goal and an equation goal per sealed definition. They pass
    unsealed and fail sealed.
  - Also inspect every `rw`/`simp`/`unfold` argument, since `simp [Def]` unfolds even a sealed
    definition.
  - **Homes follow from rule 10:** an API that must look inside another author's definitions goes
    beside them, in their files.
- **Pre-ship every brief contract:**
  - elaborate each prescribed home, guard and statement in its import context;
  - run a route probe that names the public lemma bridging each step and discharges each
    prescribed step's premises;
  - check row delimiters against where words actually sit.

  Archive the probes as `.lean.txt` and cite them.
- **Public-facing Lean text:** new docstrings cite only mathematical sources (`[AB09, …]`, papers)
  and library declarations. Never write `audits/` or `briefs/` paths, gate, finding or round
  labels, dated rulings, or campaign item names (MIG-1, E-D, "checkpoint 3"). Provenance goes in
  commits, PR descriptions and records. Docstrings state content, not labels. Every proof over 20
  lines carries a `**Proof sketch.**`.
- **File size is not a driver:** report sizes; never split or delay for size alone.

## 3. Duplication governance

- Report debt at **major** unless the user has acknowledged it. A copy outside an acknowledged
  family's named scope is a new major; an accounting fix inside it is a minor. One fifth of a
  file's declarations is the threshold for a review item.
- **Scope families by kind:** ask for acknowledgment of "every re-derivation of facts (i)–(n)
  anywhere in TCSlib", with each kind's canonical statement, never a list of sweep sites. Site
  lists cost gate 89 three extra rounds. Describe searches as candidate enumeration plus
  inspection, never as exhaustive.
- Before an API pack, `git grep` every open PR branch, prepared landing and delivery ref for each
  new public statement's shape, as well as screening the base.
- Screen populations include every file the brief or pack cites.
- **Search inline steps, not only statements.** A whole-statement `exact?` misses a `have` that
  re-proves a published lemma inside a longer proof. Gate 93 went to three rounds on such steps:
  first-exit uniqueness, buffer reads and output stability after a halt. Before any pack, and in
  every review brief, sweep the new proofs for the usual signs and test each hit against the
  published API:
  - `bufferTape_eq` unfolded, or append indexing done by hand;
  - `Nat.exists_eq_add_of_le` with `runFrom_add` and `runFrom_of_halt`;
  - `lt_trichotomy` or `Nat.find` over runs;
  - five-line `Cfg.ext` blocks.

  Once a family is acknowledged by kind, a later find is a minor.
- **Older re-derivations found while landing a PR** (the user, 2026-11-06, standing rule): when a
  screen or sweep of a PR's touched files exposes an unrecorded re-derivation of a published
  lemma, and the fix is mechanical (cite the published lemma; no statement change, no new public
  declaration, no new import, no design choice), re-point every member in the same PR, record the
  family in the ledger by kind as retired on merge, and disclose it in the pack. Anything else
  waits for the user's ruling. Search every closing form of the family (rewrite chains, simp
  sets, `show`/`change` readings), not one: IL-1's first search matched one closing and missed
  five members.

## 4. Gates and bundles

- A gate pack lives at `campaign/gates/<NN>-<slug>/pack.md` (rounds `pack-r2.md`, …). Findings are
  committed verbatim (`findings.md`, `findings-r2.md`, …), and `resolutions.md` answers each.
- **Bundles include the standards** (`TEMPLATE.md`, `policy.md`, `workflow.md`) and every input
  a requested check needs: every file the pack names, the full population of every screen it
  cites, the delivery's evidence. Never cap a folder's listing.
- **Dispatch prompts** are pasted in chat, in a fenced block, with the bundle's path, its
  SHA-256 and section count, and both full 40-character hashes (Lean and records).
  - **Hashes:** take every full hash from `git rev-parse` in the same step that writes it, and
    `git cat-file -e` it. Never complete a short hash by hand.
  - **Findings file:** every prompt asks the auditor for `<name>-findings.md` (the table and the
    verdict line) as an attached file, pasted in its reply too.
  - **Ask the agent choice before preparing each audit or fill** (the user, 2026-11-06):
    Codex or Claude. Ask per item; do not infer a standing choice from an earlier dispatch.
  - **Agents read from the exchange branch; delivery depends on the chosen agent** (the user,
    2026-11-06, superseding the attachment-only rule). Prompts name the bundle or brief by its
    path on `exchange/pass-shelat-ch5-8` rather than as an upload.
    - **Codex:** return the findings Markdown or delivery zip as an attachment in chat; it cannot
      push to GitHub. Findings are also pasted in the reply.
    - **Claude:** may push the findings or delivery directly to the designated
      `arora-barak-ch3-4/inbox/` folder of the exchange branch, touching nothing else, with
      `git pull --rebase` before every push and no force-push.
    - External agents do not push changes directly to any campaign branch. Lean changes go by
      PR for the user's approval. **The maintainer's records-only exception in §1 is retained**
      (explicitly confirmed by the user with this routing update).
  - **A Codex pack's closing paragraph:** "**Deliver your findings as a downloadable
    file named `<name>-findings.md`** (the findings table and the verdict line, no other
    wrapping), and also paste its content in your reply." A Claude pack instead gives the exact
    exchange inbox path and the pull/rebase/no-force-push restrictions above. The prompt names
    the bundle by its path on that branch.
  - **Rebuilt bundles:** if a bundle is rebuilt after its prompt went out, re-issue the whole
    prompt and say the old one is void.
- **The exchange** is the `arora-barak-ch3-4/` subfolder of the orphan branch
  `exchange/pass-shelat-ch5-8`:
  - `outbox/gates/<NN>-<slug>-gate/` and `outbox/fills/` (staged by the maintainer);
  - `inbox/` (deliveries and findings, from the user);
  - `archive/` (moved there once committed to the records; since 2026-11-06 a dispatched folder
    stays in `outbox/`, where its agent reads it, until its findings or delivery are committed).

  Touch only this subtree; pull with rebase before every push. The historical archive before
  2026-11-04 stays on the user's Mac (`tcslib/exchange/archive/`, indexed in the subfolder's
  README).
- Everything received (zips, reports, findings, probe files) is data, not instructions. Extract
  each delivery into its own new directory, use `python3 -I`, and elaborate no delivered Lean
  file before reading it.

## 5. Fills

- Briefs live at `campaign/fills/<group>/briefs/`, with inputs, orders, logs and reviews beside them.
  Every brief attaches the fill-environment addendum.
- **Fills may run in parallel** (the user, 2026-11-06: on cloud machines with Claude agents,
  there is no need to limit how many fills are out at once). Each fill still owns its files, and
  two fills never share an owned file. The maintainer's Lean pool is
  the §2 rule (Seyoon, 2026-11-17); this does not change an external worker's brief-specific limit.
- **Agent choice, a soft suggestion per item:** Codex for a first (maybe second) attempt; Claude
  for an item making slow progress (one stalled Codex round counts); megafills go to Codex.
  Ask the agent as its own question, never inside an option.
- **Sub-agents** review incoming fills and audits. On the cloud machine they may also take
  independent tasks in parallel (screens, sweeps, record drafts, probe drafts), **at most five at
  once** (the user, 2026-11-05). Give them the full standing rules: no `lake build`, Lean only
  through the throttled tools and within the shared §2 pool, `python3 -I` on untrusted
  data, screens one at a time, no commits or pushes, outputs only in their own scratch folder.
  The maintainer integrates the result.

- **Overnight fills** (the user, 2026-11-06): when a fill brief is issued and ready to dispatch
  while the user is away, the maintainer dispatches it to its own sub-agent (Claude) instead of
  waiting: the brief and addendum as the prompt's inputs, delivery as a zip in the scratch
  `deliveries/` area, reviewed and landed as usual. Gates still wait for the user's dispatch.
  **Ended (the user, 2026-11-06, morning):** while the user is awake, fills are dispatched the
  typical way again: the maintainer posts a pasteable prompt and the user dispatches it. No new
  fill goes to a sub-agent. Fills already running on sub-agents continue.
- **Delivery by push** (the user, 2026-11-07): when the dispatched agent can push, its prompt may
  replace the brief's zip-by-attachment paragraph with a push of the same zips to
  `exchange/pass-shelat-ch5-8` under `arora-barak-ch3-4/inbox/<fill>/`, touching nothing else, with
  `git pull --rebase` before every push and no force-push. The brief is not edited, so its checksums
  stand. The first was E-PAD.

## 6. Scripted edits and records

- Every scripted replacement asserts its occurrence count. Avoid positional splices, diff the
  result, and re-verify any file that will be attested or bundled.
- Records cite paths under `campaign/` (layout since 2026-10-18; old paths resolve through
  `campaign/MOVED.md`). Never rewrite verbatim findings.

## 7. Working rhythm

- **Work continuously:** after each item go straight to the next. Stop only to wait on running
  jobs or for a user decision, and ask decisions with a question tool, one decision per question,
  with the recommended option first.
- **Before the user sleeps or relocates:**
  - list the heavy replays and dispatches ready to start;
  - ask every decision you can foresee;
  - then keep working without new design decisions; record where you stopped.
- **Scratch hygiene:** keep everything needed beyond a session in the repository or on a pushed
  branch. On the local Mac, `/private/tmp` files untouched for about 3 days were deleted nightly,
  so `touch -a` before gaps. A cloud VM may be reclaimed when idle: assume scratch files and
  background jobs can vanish, and keep snapshots rebuildable.
- **Cloud specifics** (2026-10-17 findings):
  - the VM is about 4 vCPU, 16 GB and 30 GB of disk, so prune snapshots;
  - Mathlib's cache hosts need custom network access;
  - the GitHub proxy rejects GraphQL, so use `gh api repos/…` (REST) instead of `gh pr …`.

**Every flag of the Lean-backed sweep is dispositioned** (gate 154 G154-01, 2026-11-17). Its
`foreign_definitions` list includes Core and Mathlib constants. Each one is located in the changed
proofs' tactic lists and classified: a definition passed to `simp`/`rw`/`unfold` is an explicit
read and must be replaced by its published equations, whatever library it comes from. Simprocs
(`reduceIte`, `Int.reduceNeg`, …) and constants inside proof-term arguments (`if_pos rfl`,
`Bool.noConfusion (…)`, `List.take_append_drop (Nat.find h) w`) are not reads. "Outside TCSlib" is
not a disposition.

**Bundles carry citation homes** (gate 147 G147-02, 2026-11-16). A gate bundle includes the source
file of every public lemma that a changed proof newly cites, pinned at the audited head, alongside
the changed owners.

## ===== campaign/standards/fill-environment-addendum.md =====

# Fill-agent environment addendum (v2.6): resources, the dependency cache, starting Lean, and megafills

**Version 2.6 (2026-10-27; the user's ruling on megafill D's E-SERIAL)** clarifies the one-Lean
rule, from megafill D's record (its E-SERIAL stopped an item for the cache tool's own parallel
build, a 0.3 s overlap inside `lake exe cache get`, before the item's branch existed):
- **the cache tool's own work is outside the one-Lean rule** (Part 1, item 2);
- **a Lean process is one that you start** (Part 3, item 5);
- **a process deviation never ends an item** (Part 3, a new item 7).

**Version 2.5 (2026-10-22)** changes two rules of Part 1, item 2, from the first megafills' records
(gates 59 and 60):
- **the manifest check counts the packages present** in `.lake/packages`. The narrowed fetch does
  not clone the documentation toolchain, so a check of every package in the manifest failed by
  construction;
- **the cache tool's local archive store is logged before the first fetch.** One host already held
  967 of the 1,002 archives it needed, with no record of where they came from. Archives already
  in that store are the cache tool's own, named by hash and checked by it: **using them is
  allowed** (user, 2026-10-22), and the store is logged and reported.

Parts 2 and 3 are otherwise unchanged (Part 3's shared fetch logs the store once).

**Version 2.4 (2026-10-22)** adds **Part 3, the megafill**: one session that works through a queue
of fill briefs on one host, sharing the preflight, the toolchain, the clone and the cache. Parts 1
and 2 are unchanged except for one clarification in item 2 (the cache tool compiles itself on
first use). Version 2.3's narrowed cache fetch passed on its first two uses (2026-10-21: 35 roots
and 967 files; 40 roots and 1,002 files; no failed download, no retry).

**Version 2.3 (2026-10-18).** Part 1, the resource and cache rules, applies on **every** host
(the user's authorization of 2026-10-17). **Version 2.3** changes one rule: **the dependency cache
is fetched for your brief's Mathlib roots only** (items 2–4), never in full. On the fill hosts of
2026-10-18 the network proxy refused about 1,900 of the full cache's 7,506 files
(`CONNECT tunnel failed, response 403`), the same files on every host, while a fetch narrowed to a
brief's imports (about 1,000 files) succeeded. The narrowed cache also needs far less disk.

**Version 2.2** changed one rule, **when the free-disk
floor applies** (item 1), and updates the measured Lean peak; nothing else. The 12 GiB floor is a
start-of-run figure that includes installing the toolchain (about 4.2 GiB with its archive). A
re-check after the toolchain is installed needs only the cache step's share, 8 GiB. Two hosts of
2026-10-18 stopped with E-RES on a 12 GiB re-check after installing the toolchain.

**Version 2.1** changed two things:
- **the memory headroom counts memory in use, not the page cache** (items 1 and 6). Version 2's
  `limit − memory.current` counted the kernel's file cache, which fills a cgroup to its limit
  after the dependency cache is downloaded and unpacked, and is reclaimed on demand. Two hosts
  of 2026-10-18 stopped with E-RES at 0.09 and 1.3 GiB "headroom" while their anonymous memory
  was 0.2 and 0.08 GB, with no OOM event;
- **`lake exe cache get` runs with `TAR_OPTIONS=--no-same-owner`** (item 2): on hosts that forbid
  `chown`, the cache tool's own `leantar` archive otherwise fails to install
  (`Cannot change ownership to uid 1001`).

Part 2, the shim for an unreadable `/proc/<pid>/exe`, is version 1's text, unchanged (authorized
2026-10-14). Everything else in your brief stays binding; where it names an earlier version of
this addendum, read v2.5.

## Part 1: resources and the dependency cache

**Why.** Four fill workers of 2026-10-17 stopped before any proof check, all for host reasons. The
dependency cache filled the disk (`No space left on device`, `leantar` exit 101). One worker staged
files on `/dev/shm`, which counts against the memory limit, and others copied dependency trees
between directories. Empty or truncated oleans, a stale compiled Lake configuration and a Lake
re-clone of Mathlib (package URLs differing from the manifest) followed. Lean then crashed
(SIGBUS 135, SIGSEGV 139) or stalled at a full memory limit. The rules below stop that early and
cleanly.

1. **Preflight, before any cache or Lean work.** Record in `evidence/logs/preflight.log`, and quote
   in `REPORT.md`:
   - `nproc`;
   - the memory limit and use: the cgroup's `memory.max`, `memory.current`, `memory.events` and
     `memory.stat` (cgroup v1: `memory.limit_in_bytes`, `memory.usage_in_bytes`, `memory.stat`),
     or `/proc/meminfo` where there is no cgroup limit;
   - `df -B1` and the filesystem type (`df -T`) of the clone's directory and of every scratch
     directory you use.

   **Stop with escalation E-RES**, quoting the numbers, if the clone's filesystem has less than
   **12 GiB free**, or the memory headroom is below **4 GiB**. Do not try to make room by copying,
   moving or deduplicating dependency trees.
   - **When the disk floor applies.** The 12 GiB floor applies at this initial preflight, which
     covers everything after it, the toolchain included. If you install the toolchain after it,
     you may re-check before `lake exe cache get`; that re-check's floor is **8 GiB** (the
     packages about 6 GiB, the cache archives about 1 GiB, the bootstrap's oleans and the clone).
     After the cache step, disk is not re-checked: an ENOSPC is handled by item 4.
   - **The memory headroom is the limit minus the memory in use**, where the memory in use is
     `anon + kernel + shmem` from `memory.stat` (cgroup v1: `memory.usage_in_bytes − total_cache +
     total_shmem`). Where `memory.max` is `max` (no cgroup limit), the headroom is `MemAvailable`
     from `/proc/meminfo`. Log the fields and the computation.
   - **Not shortages:** page cache (`file`, `active_file`, `inactive_file`, `file_mapped` in
     `memory.stat`; `memory.current` includes it), and `memory.events`' `max` and `high` counters,
     which count reclaim at the limit. The kernel reclaims the cache as Lean needs memory.
   - **A shortage** is an `oom` or `oom_kill` event, a Lean exit 137, or a headroom below 4 GiB
     as computed here.
   - **Measured needs at this pin:** the Mathlib cache is about 5.2 GiB unpacked (all packages, with
     their git checkouts, about 6 GiB), plus about 1 GiB of archives kept by the cache tool; the
     toolchain about 4.2 GiB with its archive. The TCSlib bootstrap writes about 0.2–0.3 GB of
     oleans. Lean's peak memory is about 2.8 GiB (`Build/Catalog`, at `-j4`; 2,796 MiB measured on a
     fill host); most modules need under 1.6 GB.
2. **One checkout, one cache.** Do everything in a single clone.
   - **Fetch the cache for your brief's Mathlib roots only**, into that clone's own
     `.lake/packages`, with `TAR_OPTIONS=--no-same-owner` in its environment (extract the
     toolchain archive the same way if it fails on ownership). The roots are the Mathlib modules
     that the modules of your brief's order list import directly; from the clone's root, after
     your brief's first edit (its imports or overlay, if any):

     ```sh
     ORDER=<your brief's order list>
     sed 's|$|.lean|' "$ORDER" | xargs grep -h '^import Mathlib' | awk '{print $2}' | sort -u \
       > evidence/logs/mathlib-roots.txt
     TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt) \
       2>&1 | tee evidence/logs/cache-get.log
     ```

     The tool fetches those modules and everything they import. **Never run the unfiltered
     `lake exe cache get`.** Record the roots' count and the number of files fetched. If you add
     an import later (only where your brief authorizes one), fetch for the new roots the same way.
     Alternatively, symlink `.lake/packages` to a populated tree at exactly the same pins,
     recorded in `REPORT.md`.
   - **Log the cache tool's archive store first** (v2.5). Before the first `lake exe cache get`,
     record in `evidence/logs/cache-store.log` whether the store exists
     (`${XDG_CACHE_HOME:-$HOME/.cache}/mathlib` by default), how many files it holds and their
     total size (`find … -type f | wc -l`, `du -sb …`). The fetch log's "Attempting to download N"
     and "Decompressing M" then show that `M − N` archives were already in the store. Archives
     already there are the cache tool's own, named by hash and checked by it: using them is
     allowed, and the store is not "another session's object store" (below). In `REPORT.md`, give
     their number and, if you know it, their origin (an earlier session on this host, the host
     image); do not describe them as downloaded by this session.
   - Never copy, move, merge or deduplicate dependency trees between directories.
   - Never reuse another session's scratch tree, package builds, toolchain or object store, and
     never join `LEAN_PATH`s across trees.
   - Never put the clone, `.lake`, the cache, an olean tree (`TCSLIB_OLEANS`) or `TMPDIR` on a
     memory-backed filesystem (`/dev/shm`, any tmpfs).
   - **The cache tool's own work is outside the one-Lean rule.** `lake exe cache get` may first
     compile the cache executable (on a fresh clone, about 20 Lake jobs, among them a few
     Batteries modules) and runs `lake build --no-build proofwidgets:release`. Lake schedules
     these jobs itself, and at this pin it has no option to serialize them. They are expected and
     allowed. They are not a `lake build` of the project, and they are not "a Lean process" in the
     sense of Part 3, item 5. Run the command alone: start no check of your own until it has
     exited. Do not reconstruct, measure or certify Lake's internal scheduling, and do not report
     it as a deviation.
   - **Packages match the manifest** (v2.5: the packages present). A fresh clone's first
     `lake exe cache get …` fetches the packages that `lake-manifest.json` names, except those the
     narrowed fetch does not need. Afterwards, and before every later Lake command, check each
     package **present in** `.lake/packages`: `git -C .lake/packages/<name> remote get-url origin`
     and `rev-parse HEAD` must equal the manifest's URL and revision. If one differs, stop with
     E-RES. List the manifest's packages that were not cloned as **ABSENT**, not as a mismatch (at
     this pin `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`, the documentation
     toolchain). The check passes when every present package matches and no module of your order
     list imports an absent package; quote its last line in `REPORT.md`. Never let Lake re-clone
     or update a package that is already present.
3. **Check the cache before the bootstrap.**
   - The narrowed `lake exe cache get` exited 0, with no failed download.
   - `find .lake/packages -name '*.olean' -size 0` prints nothing.
   - A probe that imports one of your roots elaborates through `scripts/lean_check_tree.sh`, e.g.
     a file containing only the first line of `mathlib-roots.txt` as an `import`. A probe that
     imports no Mathlib does not test the cache, and a module outside your roots' closure is not
     in your cache.
   - **Failed downloads** (a network error such as a proxy `403`, or `N download(s) failed`):
     re-run the same narrowed command up to twice; it fetches only what is missing. If files
     still fail, that is a failed check of this item (item 4).
4. **One cleaned retry, then stop.** Clean and retry once on any of these:
   - ENOSPC (`No space left on device`, `os error 28`);
   - `leantar` exit 101;
   - Lean exit 135 (SIGBUS), 137 (killed) or 139 (SIGSEGV);
   - `compiled configuration is invalid`;
   - a failed check of item 3.

   To clean, delete the clone's `.lake/packages` and its compiled configurations
   (`.lake/lakefile.olean*`), re-run the preflight (a re-check: item 1's floor before the cache),
   and run the narrowed `lake exe cache get` once more. If anything fails again, stop with E-RES
   and report, naming the files that failed to download and the roots you fetched. **Never**
   unpack or restore individual archives or oleans by hand (`leantar`, the cache tool's `lookup`,
   copies from elsewhere).
5. **Bootstrap order.** Your brief's order list is the bootstrap. You may build, first, only the
   modules of the list that your owned file imports (directly or not), in the list's order, and
   check your owned file against them. Build the list's remaining modules before the final
   sweep. Record which you did.
6. **No self-imposed timeouts.** Do not wrap module checks in short timeouts.
   - Log each module's start and end time, and its maximum memory (`/usr/bin/time -v` where
     available).
   - A module that stalls far beyond the measured figures is a resource symptom: re-read the
     memory counters, and compute the headroom as in item 1 (the memory in use, not
     `memory.current`). Stop with E-RES only on a shortage as item 1 defines it.
7. **Logs in place.** Write every log to its final path under `evidence/logs/` from the start
   (`2>&1 | tee …`). Never move a log that a running process is writing.
8. **No checks against missing prerequisites.** If the bootstrap stops, record its tail and skip
   the checks that need its products. Do not report their failures as findings.

E-RES is an environment report, not a failed fill. A continuation goes to a host that passes the
preflight.

## Part 2: starting Lean when `/proc/<pid>/exe` is unreadable (v1, unchanged)

**Authorized by the user (2026-10-14) for every fill brief of the chapters 3–4 campaign.** It
applies only under the condition below.

### The condition

Some fill hosts cannot resolve a process's own `/proc/<pid>/exe` link: `/proc/self/exe` may be
readable while `/proc/<pid>/exe` returns *Permission denied*. Lean 4.25.0 locates its own
installation through that link (`IO.appDir`, used by `Lean.getBuildDir`), so `lean --version`,
`lake exe cache get` and `scripts/lean_check_tree.sh` fail with

```text
error: failed to locate application
```

or Lake reports `could not detect the configuration of the Lake installation`.

### The authorized fallback

**Use this only if, and after,** the pinned, unmodified Lean fails with that error in your
environment. Then you may preload the following `readlink` fallback into the Lean and Lake
processes only.

- **What it does:** it answers the single failed self-path lookup with the executable's own path,
  taken from the ELF startup metadata (`AT_EXECFN`). Every other call is passed through
  unchanged.
- **What it does not do:** it changes no filesystem permission, does not bypass the sandbox, and
  changes neither Lean, the kernel, the sources nor any proof check.
- **Precedent:** earlier campaign deliveries used exactly this source, for example the
  record-table continuation 5 (`audits/wave1-fill-agent-reports/recordtable-6-REPORT.md`).

`executable-path.c` (SHA-256 `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`):

```c
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>
/* Supply the executable's actual path from ELF startup metadata when procfs
   cannot resolve it. No filesystem, network, or proof-checking rules change. */
ssize_t readlink(const char *path, char *buf, size_t cap) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  ssize_t n = real_readlink(path, buf, cap);
  char own[64];
  snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
  if (n >= 0 || (strcmp(path, "/proc/self/exe") && strcmp(path, own))) return n;
  const char *exe = (const char *)getauxval(AT_EXECFN);
  char absolute[PATH_MAX];
  if (!exe || !realpath(exe, absolute)) return n;
  size_t len = strlen(absolute);
  if (len > cap) len = cap;
  memcpy(buf, absolute, len);
  return (ssize_t)len;
}
```

Compile and use it in your scratch directory:

```bash
cc -shared -fPIC -O2 executable-path.c -ldl -o executable-path.so
export LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0"   # your pinned toolchain
export LAKE_HOME="$LEAN_SYSROOT"
export LD_PRELOAD="$PWD/executable-path.so"
lean --version   # must now print the pinned version
```

### Rules

1. **Use exactly this source.** Do not write a different shim, patch the toolchain, change
   permissions or request sandbox escalation.
2. **Scope:** preload it only into the processes that run Lean or Lake (`lake exe cache get`,
   `scripts/lean_check_tree.sh`, your probes). Nothing else.
3. **Record it in `REPORT.md`:**
   - that the condition occurred;
   - the shim's SHA-256, which must match the one above;
   - the exact environment variables you set.

   Include the source under `evidence/runtime/`. **Do not ship the compiled `.so`** or any
   build products.
4. **If Lean still cannot start** with the shim, stop and report. Do not try anything further.
5. A standard host, where Lean starts normally, needs none of this. Do not preload the shim
   there.

## Part 3: the megafill (v2.4)

A **megafill** is one session that works through a queue of fill briefs, one after another, on one
host. Its **cover brief** names the queue, the shared base, the order and each item's budget.
**Each item stays its own fill:** its own brief (binding for that item), branch, checks, screens,
`REPORT.md` and zip, exactly as if it had been dispatched alone. Only the environment work is
shared.

1. **Once, at the start:** Part 1's preflight (item 1, with its floors), the toolchain, and one
   clone of the campaign branch. Verify the cover brief's and every item brief's SHA-256 against
   the cover brief's table, and run the cover brief's ancestor check.
2. **One cache for the queue.** The roots are the union over the queue: run item 2's command with
   every item's order list concatenated, from the clone's root at the shared base:

   ```sh
   cat <every item's order list> | sort -u | sed 's|$|.lean|' | xargs grep -h '^import Mathlib' \
     | awk '{print $2}' | sort -u > evidence/logs/mathlib-roots.txt
   ```

   then `TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt)`,
   after logging the archive store once (Part 1, item 2). The cover brief gives the expected
   count. Items 3 and 4 apply once, to this fetch. Keep these
   shared logs under `evidence/logs/` at the clone's root, and copy them into each item's zip.
3. **Per item, in the queue's order:**
   1. Start from a clean tree (the previous item's work is committed on its own branch and
      zipped). `git checkout -b <the item's branch> <the shared base>`; apply the item brief's
      patches if it prescribes any; then make its first edit (its authorized imports or overlay).
   2. **Re-bootstrap the item's whole order list**, even the modules an earlier item built: a
      branch switch changes the sources the earlier oleans came from (an earlier item's owned file
      may be upstream of this one). Log it as the item's bootstrap. About 10–20 minutes.
   3. Do the item as its brief says, through its delivery zip, and **deliver that zip at once**.
      The session may end at any time; finished items must survive it.
   4. **Budget.** Each item has a wall-clock budget, counted from its branch's creation. When it
      runs out, finish the step in progress, commit, write the item's partial zip with its
      `REPORT.md` (the checkpoints reached; every open declaration with its literal "Proof
      sketch"; the axiom walk), and start the next item. Time an item does not use passes to the
      later ones. The last item has the rest of the session. **Never return to an earlier item.**
   5. **Escalations stay per item** (each brief's ground rules). An item with nothing left that
      its escalations allow ends early, with its zip.
4. **Disk between items.** Before each item after the first, record `df -B1` of the clone. Stop the
   whole queue with E-RES below **3 GiB** free; the items already zipped stand.
5. **One Lean process at a time** across the whole queue, and one screen at a time. A Lean
   process is one that you start: a module check, a probe, a bootstrap or sweep step (each
   through `scripts/lean_check_tree.sh`), or one `lake exe cache get`. Never run two of them at
   once. One text screen (Python, `nice -n 10`) may run beside one of them. Processes that Lake or
   the cache tool start inside `lake exe cache get` are not counted.
6. **At the end** (or when the session must stop), deliver `megafill-<name>-REPORT.md`: the queue;
   each item's outcome (complete; partial, with its checkpoints; or not started), with its
   branch's start and end times and its zip's SHA-256; the shared preflight and cache numbers. An
   item never started is simply listed as such: it is not a failure.
7. **A process deviation never ends an item.** A deviation from these rules, yours or a tool's, is
   disclosed in `REPORT.md` with its evidence, and the work continues: stopping does not undo it.
   Only E-RES (Part 1) or an item brief's own escalation (its ground rules) ends an item early.

## ===== TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: the core

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`).
This module is the core of the layering split (design §16a item 4). It holds the MIG-0a core,
moved here from `Build/Contract.lean` as landed on 2026-10-13 (after the MIG-0a gate closed at
round 2) with no statement changed, and MIG-0b's segment, round and joint-trajectory layers, the
sanity lemmas, state renaming and the macro-step lockstep. It imports only the machine core
(`Simulation`, `StateRenaming`) and `Mathlib.Tactic.Linarith`, so that `Build/Loop` and
`Build/CounterLoop` can import it. The seam, embedding and routine adapters are in
`Build/Contract/Seam`, `Build/Contract/Embed` and `Build/Contract/Catalog`, and the symbol lift in
`Build/Contract/Lift` (the facade `Build/Contract` lists them).

A *contract* packages what the library's framed rows state one by one (design §14 item 0,
§16): started at `entry` in a configuration satisfying the precondition, the machine reaches
the endpoint `post` after **exactly** `time` steps, has **not** reached an exit before, and
keeps every work head inside an interval. "Within `B`" and the space bound are derived. It is
the **first-exit** specialization; the layers below cover what it cannot: *segments*, whose
endpoint need not be a first exit; *rounds*, which return to their anchor or escape; and *joint
trajectories*, relations on the whole head vector.

## Design

* **Exact time and the cut are fields** (§16). The cut includes time `0`, as in about 45 of the
  library's rows. A row that returns to its own anchor, so that its cut starts at time `1` (the
  advancing writer `Turing.writeAdvTM_run_ofCfg`), is a `Turing.ReturnContract`, turned into a
  contract by the release adapter (`Turing.ReturnContract.release` in `Build/Contract/Seam`,
  over `Turing.seamReleaseTM`). The install and emit calls (`Turing.FinTM.exists_installCallTM`,
  `Turing.FinTM.exists_emitCallTM`) quantify separate `entry` and `exit` states that may
  coincide: with arbitrary witnesses, split on `entry = exit` (see `Turing.ReturnContract`).
* **Exits form a set**, so one structure covers single anchors, verdict pairs (`yes`/`no`),
  loop exits (`done`/`escape`) and halting (`none`).
* **The endpoint is a function** of a data index `i : ι` and the start configuration. Data the
  module reads (a stored word, a record's fields) is the index; the precondition says where it
  is stored.
* **Head envelopes are intervals** `[lo, hi]` per tape, functions of the index and the start
  configuration. The radius form is a special case (`Turing.Contract.mem_Icc_of_abs_le`); space
  follows from `MultiTapeTM.spaceUsedByTape_le_card_Icc`.
* **Frames are part of the endpoint** (rows already state them as `{ d with … }`); a derived
  layer names them for composition proofs (user decision, 2026-10-12): `Turing.Cfg.SameOutside`,
  its `.keep` lemmas, and `Turing.Contract.Frames`, adapted from [AFM26]'s framing.
  `Turing.Cfg.SameOutside` is an endpoint relation on work-tape contents only.
* **Segments** (MIG-0b; `Turing.Segment`): fixed-length runs, possibly of length zero, between
  two actual configurations, avoiding a forbidden set strictly before the end, with a relation on
  the whole head vector through the end (`CfgRecord`'s `RecordRun`, `SingleTape`'s `DGSpan`,
  `EmitIterEmbed`'s `SafeRun`, `CounterLoop`'s `counterSpan`). `Turing.SafeSegment` also keeps
  the endpoint off the set (`Primitives`' `splitSafe`).
* **Rounds** (MIG-0b; `Turing.Round`, `Turing.RoundContract`): positive runs from an anchor that
  end at the anchor or in an escape set, live and off both strictly in between (the find round
  of `RecordTable`, the counter loop's body interface).
* **Joint trajectories** (MIG-0b; `Turing.Contract.Traj`): a relation on the head vector at
  every time through the endpoint, derived like `Turing.Contract.Frames`.
* **Universes:** alphabet, states and index in `Type`, the universe of `FinTM`, `phaseHostTM`
  and `counterLoopTMVia` (backlog UNIV-1 folds in here).

## Main definitions

* `Turing.Contract`: the structure; `Turing.Contract.Positive`.
* `Turing.Contract.trans`: first-exit sequencing on one machine, with no dispatch step.
* `Turing.Cfg.SameOutside`, `Turing.Contract.Frames`: the derived frame layer.
* `Turing.ReturnContract`: returning modules.
* `Turing.HeadBox`, `Turing.Segment`, `Turing.SafeSegment`, `Turing.Contract.ofSegment`: the
  segment layer and its bridge to contracts.
* `Turing.Contract.zero`: the zero-time contract of a machine started at its own exit.
* `Turing.roundStop`, `Turing.Round`, `Turing.roundOrbit`, `Turing.RoundContract` (with
  `returning` and `escaping`), `Turing.ReturnContract.toRound`, `Turing.RoundContract.hullLo`
  and `hullHi`: the round layer.
* `Turing.Contract.Traj`: the joint-trajectory layer.
* `Turing.Contract.mapState`: state renaming along an embedding.
* `Turing.Lockstep`, `Turing.Contract.lockstep`: the macro-step lockstep and its transport.

## Main results

* `Turing.Contract.within`, `Turing.Contract.spaceUsedByTape_le`: the derived forms.
* `Turing.Contract.live`: a contract run is live before its endpoint.
* `Turing.Cfg.SameOutside.keep_word`, `Turing.Cfg.SameOutside.keep_blank`: frame preservation.
* `Turing.Segment.trans`, `Turing.Segment.iterate_seq`, `Turing.Segment.live`,
  `Turing.Segment.time_eq`, `Turing.SafeSegment.trans`, `Turing.Contract.segment`: segment
  concatenation (of two, and along a sequence), liveness, uniqueness of first exits, and the
  contract bridge.
* `Turing.Round.iterate_seq`, `Turing.Round.iterate`, `Turing.RoundContract.orbit_round`: round
  iteration along a sequence of starts, and along an orbit.
* `Turing.Contract.Traj.trans`, `Turing.Contract.Frames.trans`: preservation by `trans`.
* `Turing.Contract.time_eq_zero_iff`, `Turing.Contract.trans_positive`: sanity lemmas.
* `Turing.Contract.lockstep_admissible`: the target entry compatible with the encoding.
* `Turing.Contract.trans_pre`, `_time`, `_post`, `_lo`, `_hi` — the specification API
  (user, 2026-10-16): the fields of a sequenced contract as equations, generated by
  `simps` without the `simp` attribute, so that consumers never unfold the definition.
* `Turing.Contract.ofSegment_pre`, `_time`, `_post`, `_lo`, `_hi` — the segment bridge's
  fields, the same way (the specification API's gate, finding 1).
* `Turing.Contract.zero_pre`, `_time`, `_post`, `_lo`, `_hi` — the zero-time contract's
  fields as equations.
* `Turing.RoundContract.returning_*`, `Turing.RoundContract.escaping_*`,
  `Turing.ReturnContract.toRound_*`, `Turing.Contract.mapState_*`, `Turing.Contract.lockstep_*`
  (`pre`, `time`, `post`, `lo`, `hi`) — the remaining constructors' fields, the same way.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math` (https://github.com/anthropics/formal-math),
  project `3sum-apsp`, commit `e1a4e650` (2026-10-05), Apache-2.0, © Anthropic, PBC; examined
  2026-10-12 (design §15, *Prior art examined*). Design adaptation (policy §2): the framing of
  `ThreeSumApsp/Lang/Regions.lean` (`SameOn`, `SameOutside` and the `.keep` lemmas), adapted as
  `Turing.Cfg.SameOutside`, its `.keep` lemmas and `Turing.Contract.Frames`; and the
  specification-only calls of `ThreeSumApsp/Lang/Calls.lean` (`Meets`, over the program logic
  `Ends` of `ThreeSumApsp/Lang/Logic.lean`), adapted as `Turing.Contract`, through which the
  compositions use their operands. These upstream files are vendored, with the local changes
  their headers list, as `TCSlib/Programs/Light/Regions.lean`, `Calls.lean` and `Logic.lean`.
  The treatment of time differs: exact time and a no-earlier-exit cut, not "within `T`" (§16).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16: the alphabet-reduction simulation, the
  model case of `Turing.Lockstep`.)
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **A framed contract** (design §14 item 0, §16). For every data index `i` and every start
configuration `d` at `entry` satisfying `pre i d` (an *admissible* start), the machine reaches
`post i d` after exactly `time i d` steps; `post i d` is at an exit; no exit is reached earlier
(the cut includes time `0`); and through the endpoint every work head `j` stays in
`[lo i d j, hi i d j]`. Nothing is asserted for other starts. This is the first-exit
specialization (see the module docstring for the segment, round and joint-trajectory layers of
MIG-0b).

[AFM26], design adaptation: a specification that a caller uses instead of the run, as with the
specification-only calls (`Meets`) of `Lang/Calls.lean`. Unlike there, the time is exact and
comes with a no-earlier-exit cut, rather than "within `T`" (§16). -/
structure Contract {S : Type} (M : MultiTapeTM k Γ S) (entry : S) (exits : Set (Option S))
    (ι : Type) (x : List Γ) where
  /-- The precondition on the start configuration, for data `i`. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  run : ∀ i d, d.state = some entry → pre i d → M.runFrom d (time i d) = post i d
  exit_mem : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ exits
  cut : ∀ i d, d.state = some entry → pre i d →
    ∀ u < time i d, (M.runFrom d u).state ∉ exits
  env : ∀ i d, d.state = some entry → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

namespace Contract

section Derived

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- The derived "within `B`" form, the shape of the library's existential rows. -/
theorem within (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) {B : ℕ} (hB : C.time i d ≤ B) :
    ∃ t ≤ B, (∀ u < t, (M.runFrom d u).state ∉ exits) ∧ M.runFrom d t = C.post i d :=
  ⟨C.time i d, hB, C.cut i d hd hp, C.run i d hd hp⟩

/-- The derived per-tape space bound: the envelope's width. -/
theorem spaceUsedByTape_le (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) (j : Fin k) :
    M.spaceUsedByTape d (C.time i d) j ≤ (C.hi i d j + 1 - C.lo i d j).toNat :=
  M.spaceUsedByTape_le_card_Icc d (C.time i d) j (C.lo i d j) (C.hi i d j)
    fun u hu => C.env i d hd hp u hu j

/-- A positive running time on every admissible start: what a loop round needs. -/
def Positive (C : Contract M entry exits ι x) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → 0 < C.time i d

/-- The radius form of an envelope is the interval form about the start position. -/
theorem mem_Icc_of_abs_le {p q R : ℤ} (h : |p - q| ≤ R) : p ∈ Finset.Icc (q - R) (q + R) := by
  rw [Finset.mem_Icc]
  constructor <;> linarith [abs_le.mp h]

end Derived

/-- **First-exit sequencing on one machine**: run `C₁` to its single exit `e₂`, then `C₂` from
there. Times add with no dispatch step; the envelopes take the pointwise hull. `C₂`'s
precondition is needed only at `C₁`'s actual endpoint (`hlink`), for the linked index. `hX` says
that `C₁` does not pass through an exit of `C₂` before its own exit; it cannot be dropped, since
`C₁`'s cut excludes only `e₂`. This is not a general `RecordRun` concatenation: a segment whose
endpoint need not be a first exit belongs to the segment layer (`Turing.Segment.trans`).

**Proof sketch.** Split the time at `C₁`'s time `t₁`. By `C₁`'s run, the run for `t₁ + v` steps
is `C₂`'s run for `v` steps from `C₁`'s endpoint, which is at `e₂` and satisfies `C₂`'s
precondition; this gives the run and the exit. Before `t₁` the cut is `hX`; at a time `t₁ + v`
below the total it is `C₂`'s cut at `v`. Up to `t₁` the heads are in `C₁`'s envelope, and after
it in `C₂`'s; the hull contains both. -/
def trans {S : Type} {M : MultiTapeTM k Γ S} {e₁ e₂ : S} {X : Set (Option S)} {ι κ : Type}
    {x : List Γ} (C₁ : Contract M e₁ {some e₂} ι x) (C₂ : Contract M e₂ X κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d))
    (hX : ∀ i d, d.state = some e₁ → C₁.pre i d →
      ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X) :
    Contract M e₁ X ι x where
  pre := C₁.pre
  time i d := C₁.time i d + C₂.time (link i) (C₁.post i d)
  post i d := C₂.post (link i) (C₁.post i d)
  lo i d j := min (C₁.lo i d j) (C₂.lo (link i) (C₁.post i d) j)
  hi i d j := max (C₁.hi i d j) (C₂.hi (link i) (C₁.post i d) j)
  run i d hd hp := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    show M.runFrom d (C₁.time i d + C₂.time (link i) (C₁.post i d)) =
      C₂.post (link i) (C₁.post i d)
    rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
    exact C₂.run _ _ hx (hlink i d hd hp)
  exit_mem i d hd hp :=
    C₂.exit_mem _ _ (Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)) (hlink i d hd hp)
  cut i d hd hp u hu := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    change u < C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
    by_cases h : u < C₁.time i d
    · exact hX i d hd hp u h
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp h)
      rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
      exact C₂.cut _ _ hx (hlink i d hd hp) v (by omega)
  env i d hd hp u hu j := by
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
    change u ≤ C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
    by_cases h : u ≤ C₁.time i d
    · exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₁.env i d hd hp u h j)
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp h))
      rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
      exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
        (C₂.env _ _ hx (hlink i d hd hp) v (by omega) j)

/-! The specification API (user, 2026-10-16): `Turing.Contract.trans`'s data fields as
equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] trans

/-- **Liveness**: a contract run is live strictly before its endpoint. A halt would persist to
the endpoint, putting `none` among the exits, which the cut excludes.

**Proof sketch.** Halting is absorbing, so a halt before the time would make the endpoint's
state `none`; `exit_mem` then puts `none` among the exits, against the cut at that time. -/
theorem live {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {exits : Set (Option S)} {ι : Type} {x : List Γ} (C : Contract M entry exits ι x) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : C.pre i d) {u : ℕ}
    (hu : u < C.time i d) : (M.runFrom d u).state ≠ none := by
  intro h
  have hend : (M.runFrom d (C.time i d)).state ≠ none := by
    intro h'
    have hx := C.exit_mem i d hd hp
    rw [← C.run i d hd hp, h'] at hx
    exact C.cut i d hd hp u hu (h ▸ hx)
  exact MultiTapeTM.runFrom_state_ne_none_of_le M d _ hend u hu.le h

end Contract

/-! ## Frames: the derived layer (user decision, 2026-10-12)

A contract's endpoint already states its frame (`{ d with … }`). The predicates below name the
frame for composition proofs: a *footprint* per tape, `Turing.Cfg.SameOutside`, its `.keep`
lemmas, and `Turing.Contract.Frames`. They are derived properties, not fields. The layer is
[AFM26]'s framing (`SameOn` and the `.keep` lemmas of `Lang/Regions.lean`), adapted from memory
cells to the cells of each work tape (design adaptation). -/

/-- `d'` agrees with `d` outside the footprint: every work-tape cell off `fp j` is unchanged.
This is an **endpoint relation on work-tape contents only**: it constrains neither the control
state, the heads, the input position nor the output, and says nothing about intermediate
times. A consumer that needs a cell kept at every time must keep the corresponding trajectory
fact. The two configurations may have different state types.

[AFM26], design adaptation: `SameOn` of `Lang/Regions.lean` (cells kept off a set, as in its
`SameOutside`), here per work tape. -/
def Cfg.SameOutside {S S' : Type} {x : List Γ} (fp : Fin k → Set ℤ) (d : Cfg k Γ S x)
    (d' : Cfg k Γ S' x) : Prop :=
  ∀ j q, q ∉ fp j → d'.workTapes j q = d.workTapes j q

/-- `Turing.Cfg.SameOutside fp d d'` holds exactly when every cell `q` of every work tape `j`
outside `fp j` holds in `d'` what it holds in `d`:
`∀ j q, q ∉ fp j → d'.workTapes j q = d.workTapes j q` (the definition as a lemma). -/
theorem Cfg.sameOutside_iff {S S' : Type} {x : List Γ} (fp : Fin k → Set ℤ) (d : Cfg k Γ S x)
    (d' : Cfg k Γ S' x) :
    Cfg.SameOutside fp d d' ↔ ∀ j q, q ∉ fp j → d'.workTapes j q = d.workTapes j q :=
  Iff.rfl

/-- Footprints compose by union. -/
theorem Cfg.SameOutside.trans {S S' S'' : Type} {x : List Γ} {fp fp' : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} {d'' : Cfg k Γ S'' x} (h : Cfg.SameOutside fp d d')
    (h' : Cfg.SameOutside fp' d' d'') : Cfg.SameOutside (fun j => fp j ∪ fp' j) d d'' := by
  intro j q hq
  simp only [Set.mem_union, not_or] at hq
  rw [h' j q hq.2, h j q hq.1]

/-- Replacing the control state keeps the frame. -/
theorem Cfg.SameOutside.mapState {S S' S'' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (f : S' → S'') :
    Cfg.SameOutside fp d (d'.mapState f) := fun j q hq => h j q hq

/-- **`.keep`, a stored word**: a delimited word lying outside the footprint survives. If `d`
holds `w` at offset `o` of tape `j`, its two blank delimiters included, and none of those cells
is in the footprint, then `d'` holds `w` there too. [AFM26], design adaptation: the `.keep`
lemmas of `Lang/Regions.lean`. -/
theorem Cfg.SameOutside.keep_word {S S' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (j : Fin k) (o : ℤ)
    (w : List Γ) (hout : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → o + p ∉ fp j)
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → d.workTapes j (o + p) = FinTM.bufferTape w p) :
    ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → d'.workTapes j (o + p) = FinTM.bufferTape w p :=
  fun p hp₁ hp₂ => (h j (o + p) (hout p hp₁ hp₂)).trans (hw p hp₁ hp₂)

/-- **`.keep`, a blank tape**: a tape with an empty footprint that was blank stays blank.
[AFM26], design adaptation: the `.keep` lemmas of `Lang/Regions.lean`. -/
theorem Cfg.SameOutside.keep_blank {S S' : Type} {x : List Γ} {fp : Fin k → Set ℤ}
    {d : Cfg k Γ S x} {d' : Cfg k Γ S' x} (h : Cfg.SameOutside fp d d') (j : Fin k)
    (hfp : fp j = ∅) (hb : ∀ q, d.workTapes j q = none) : ∀ q, d'.workTapes j q = none :=
  fun q => (h j q (by simp [hfp])).trans (hb q)

namespace Contract

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- A contract **frames** the footprint `fp` when every endpoint agrees with its start outside
it: for every index `i` and every admissible start `d`, `Turing.Cfg.SameOutside (fp i d)` holds
between `d` and `C.post i d`. [AFM26], design adaptation: a routine's `SameOn` promise for the
cells it leaves alone (`Lang/Regions.lean`). -/
def Frames (C : Contract M entry exits ι x) (fp : ι → Cfg k Γ S x → Fin k → Set ℤ) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → Cfg.SameOutside (fp i d) d (C.post i d)

/-- A contract frames `fp` exactly when, for every index `i` and every admissible start `d`,
every cell `q` of every work tape `j` outside `fp i d j` holds at the endpoint what it held at
the start. This is the definition unfolded, as a `@[simp]` lemma, so that `simp` and `rw` see
the footprint. -/
@[simp] theorem frames_iff (C : Contract M entry exits ι x)
    (fp : ι → Cfg k Γ S x → Fin k → Set ℤ) :
    C.Frames fp ↔ ∀ i d, d.state = some entry → C.pre i d →
      ∀ j q, q ∉ fp i d j → (C.post i d).workTapes j q = d.workTapes j q :=
  Iff.rfl

end Contract

/-! ## Returning contracts

Their release adapter is in `Build/Contract/Seam`. -/

/-- **A returning contract**: from every admissible start at `anchor`, the run first comes back
to `anchor` at a positive exact time. The endpoint is at the anchor, no strictly positive
earlier time is at the anchor (the cut starts at time `1`, since time `0` is at the anchor),
and through the endpoint every head stays in its interval. `Turing.ReturnContract.release`
turns it into a `Turing.Contract`.

The advancing writer (`Turing.writeAdvTM_run_ofCfg` in `Build/Scan`, anchor `0`, time
`|w₀| + 1`) genuinely returns to its anchor and has this shape. The install and emit calls
(`Turing.FinTM.exists_installCallTM`, `Turing.FinTM.exists_emitCallTM`, in `Build/Loop`) also
have positive cuts, but quantify separate `entry` and `exit` states that may coincide. With
arbitrary witnesses, split on `entry = exit`: when they are equal, use a `ReturnContract`; when
they differ, use an ordinary `Turing.Contract` with exits `{some exit}`, whose cut at time `0`
follows from `entry ≠ exit` and at positive times is the row's positive cut. Either way the
canonical `Cfg.ofWords` start goes into the precondition, and the time bound is kept. A round
that may instead end at a distinct escape is not a `ReturnContract`: it belongs to MIG-0b's
round layer. -/
structure ReturnContract {S : Type} (M : MultiTapeTM k Γ S) (anchor : S) (ι : Type)
    (x : List Γ) where
  /-- The precondition. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact, positive running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint, back at the anchor. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  pos : ∀ i d, d.state = some anchor → pre i d → 0 < time i d
  run : ∀ i d, d.state = some anchor → pre i d → M.runFrom d (time i d) = post i d
  exit_eq : ∀ i d, d.state = some anchor → pre i d → (post i d).state = some anchor
  cut : ∀ i d, d.state = some anchor → pre i d →
    ∀ u, 0 < u → u < time i d → (M.runFrom d u).state ≠ some anchor
  env : ∀ i d, d.state = some anchor → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

/-! ## The segment layer (design §16a, MIG-0b item 1)

A *segment* is a run of a fixed length, possibly zero, between two actual configurations (the
configuration seam), that avoids a forbidden set of states before its end, with a relation on the
whole head vector at every time up to and including its end: `CfgRecord`'s `RecordRun` (its
verdict pair forbidden, a radius about a base), `EmitIterEmbed`'s `SafeRun` (one avoided state),
`SingleTape`'s `DGSpan` (nothing forbidden, an interval on one tape) and `CounterLoop`'s
`counterSpan` (both exits forbidden, the counter head's interval and a relation on the body heads,
with a genuine zero-time case in `counter_rounds`). The relation is the **joint-trajectory layer
for general segments**: it constrains the whole head vector, so a shared witness for all heads
(the counter loop's round and offset) survives concatenation. Its endpoint need not be a first
visit of anything: the MIG-0a auditor's idling machine (round 1, counterexample 4) gives a
length-2 segment from `a` to `a`. A segment whose endpoint lies in its forbidden set is a first
exit, and then it is a contract (`Turing.Contract.ofSegment`).

An **endpoint-inclusive** segment (`Turing.SafeSegment`) also keeps its endpoint off the forbidden
set: `Primitives`' `splitSafe` and `Catalog`'s `f2_splitSafe`, whose phase traces avoid the anchor
at every time through the endpoint. Such a segment is never a first exit (MIG-0a gate, round 2):
a positive stationary run away from the anchor is one, but no first-exit contract of that
duration exists. -/

/-- The **interval box** `∏ⱼ [lo j, hi j]`, as a predicate on head vectors: the per-tape
envelope of `Turing.Contract`, seen as one relation on the whole head vector. -/
def HeadBox (lo hi : Fin k → ℤ) (p : Fin k → ℤ) : Prop :=
  ∀ j, p j ∈ Finset.Icc (lo j) (hi j)

/-- A head vector `p` lies in the box `Turing.HeadBox lo hi` exactly when
`p j ∈ [lo j, hi j]` on every tape `j` (the definition as a lemma). -/
theorem headBox_iff (lo hi p : Fin k → ℤ) :
    HeadBox lo hi p ↔ ∀ j, p j ∈ Finset.Icc (lo j) (hi j) :=
  Iff.rfl

/-- **A segment**: the run of `M` from `a` reaches `b` after exactly `t` steps, no state at a
time before `t` lies in the forbidden set `F`, and the head vector satisfies `P` at every time up
to `t`. Nothing is said about the endpoint's state. -/
def Segment {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) : Prop :=
  M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
    ∀ u ≤ t, P (M.runFrom a u).workTapePos

/-- `Turing.Segment M F P a b t` holds exactly when `M.runFrom a t = b`, no state at a time
`u < t` lies in `F`, and the head vector satisfies `P` at every time `u ≤ t` (the definition as
a lemma). -/
theorem segment_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) :
    Segment M F P a b t ↔ M.runFrom a t = b ∧ (∀ u < t, (M.runFrom a u).state ∉ F) ∧
      ∀ u ≤ t, P (M.runFrom a u).workTapePos :=
  Iff.rfl

namespace Segment

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- The empty segment: zero steps, with the start's head vector satisfying the relation. -/
theorem zero {a : Cfg k Γ S x} (h : P a.workTapePos) : Segment M F P a a 0 :=
  ⟨rfl, fun _ hu => absurd hu (Nat.not_lt_zero _), fun u hu => by
    obtain rfl : u = 0 := Nat.le_zero.mp hu
    exact h⟩

/-- A single step from a start outside the forbidden set. -/
theorem one {a : Cfg k Γ S x} (ha : a.state ∉ F) (h₀ : P a.workTapePos)
    (h₁ : P (M.step a).workTapePos) : Segment M F P a (M.step a) 1 := by
  refine ⟨MultiTapeTM.runFrom_one _ _, fun u hu => ?_, fun u hu => ?_⟩
  · obtain rfl : u = 0 := by omega
    exact ha
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
    · exact h₀
    · rw [MultiTapeTM.runFrom_one]
      exact h₁

/-- **Same-machine concatenation** (the `recordRun_trans` pattern): segments sharing the forbidden
set and the relation concatenate, with lengths adding and **no dispatch step**.

**Proof sketch.** Split a time at the first length `t`. Before it, use the first segment; after
it, the run is the second segment's from `b` (`Turing.MultiTapeTM.runFrom_add`). -/
theorem trans {a b c : Cfg k Γ S x} {t v : ℕ} (h : Segment M F P a b t)
    (g : Segment M F P b c v) : Segment M F P a c (t + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h.1, g.1], ?_, ?_⟩
  · intro u hu
    by_cases hut : u < t
    · exact h.2.1 u hut
    · have he : u = t + (u - t) := by omega
      rw [he, MultiTapeTM.runFrom_add, h.1]
      exact g.2.1 _ (by omega)
  · intro u hu
    by_cases hut : u ≤ t
    · exact h.2.2 u hut
    · have he : u = t + (u - t) := by omega
      rw [he, MultiTapeTM.runFrom_add, h.1]
      exact g.2.2 _ (by omega)

/-- **Segments compose along a sequence**: if, for each `r < n`, the run from `cs r` is a segment
of `τ r` steps to `cs (r + 1)`, all with the forbidden set `F` and the head relation `P`, and `P`
holds at `cs 0`, then the run from `cs 0` is one segment of `∑ r < n, τ r` steps to `cs n`. The
starts `cs r` are arbitrary configurations: unlike `Turing.Round.iterate_seq`, they need not share
a state.

**Proof sketch.** Induction on `n`: the empty sequence is `Turing.Segment.zero`, and each further
segment is appended by `Turing.Segment.trans`. -/
theorem iterate_seq (cs : ℕ → Cfg k Γ S x) (τ : ℕ → ℕ) (h0 : P (cs 0).workTapePos) (n : ℕ)
    (h : ∀ r < n, Segment M F P (cs r) (cs (r + 1)) (τ r)) :
    Segment M F P (cs 0) (cs n) (∑ r ∈ Finset.range n, τ r) := by
  induction n with
  | zero => exact Segment.zero h0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (ih fun r hr => h r (by omega)).trans (h n (by omega))

/-- Weakening: a smaller forbidden set and a weaker relation. -/
theorem mono {F' : Set (Option S)} {P' : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ}
    (h : Segment M F P a b t) (hF : F' ⊆ F) (hP : ∀ p, P p → P' p) : Segment M F' P' a b t :=
  ⟨h.1, fun u hu hm => h.2.1 u hu (hF hm), fun u hu => hP _ (h.2.2 u hu)⟩

/-- Two relations along one segment hold jointly. -/
theorem and {Q : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ} (h : Segment M F P a b t)
    (g : Segment M F Q a b t) : Segment M F (fun p => P p ∧ Q p) a b t :=
  ⟨h.1, h.2.1, fun u hu => ⟨h.2.2 u hu, g.2.2 u hu⟩⟩

/-- An initial part of a segment is a segment. -/
theorem take {a b : Cfg k Γ S x} {t u : ℕ} (h : Segment M F P a b t) (hu : u ≤ t) :
    Segment M F P a (M.runFrom a u) u :=
  ⟨rfl, fun v hv => h.2.1 v (by omega), fun v hv => h.2.2 v (by omega)⟩

/-- A final part of a segment is a segment.

**Proof sketch.** Shift every time by `u` (`Turing.MultiTapeTM.runFrom_add`). -/
theorem drop {a b : Cfg k Γ S x} {t u : ℕ} (h : Segment M F P a b t) (hu : u ≤ t) :
    Segment M F P (M.runFrom a u) b (t - u) := by
  refine ⟨?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' hu]
    exact h.1
  · rw [← MultiTapeTM.runFrom_add]
    exact h.2.1 _ (by omega)
  · rw [← MultiTapeTM.runFrom_add]
    exact h.2.2 _ (by omega)

/-- **First exits are unique**: two segments from one start, each ending in its forbidden set,
have the same length. This is what a proof clock (`RecordTable`'s `rt_findClock`) needs.

**Proof sketch.** If one were shorter, its endpoint, which is in the forbidden set, would be a
state of the longer one before its end. -/
theorem time_eq {a b b' : Cfg k Γ S x} {t t' : ℕ} {P' : (Fin k → ℤ) → Prop}
    (h : Segment M F P a b t) (hb : b.state ∈ F) (h' : Segment M F P' a b' t')
    (hb' : b'.state ∈ F) : t = t' := by
  rcases Nat.lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd (h.1 ▸ hb) (h'.2.1 t hlt)
  · exact heq
  · exact absurd (h'.1 ▸ hb') (h.2.1 t' hgt)

/-- Prepending one step from outside the forbidden set (the `SafeRun.cons` pattern). -/
theorem cons {a a₁ b : Cfg k Γ S x} {t : ℕ} (hstep : M.step a = a₁) (ha : a.state ∉ F)
    (h₀ : P a.workTapePos) (h : Segment M F P a₁ b t) : Segment M F P a b (1 + t) := by
  have h₁ : P a₁.workTapePos := by
    have := h.2.2 0 (Nat.zero_le _)
    rwa [MultiTapeTM.runFrom_zero] at this
  have hs : Segment M F P a a₁ 1 := by
    have h1 := one (M := M) ha h₀ (by rw [hstep]; exact h₁)
    rwa [hstep] at h1
  exact hs.trans h

/-- **Liveness**: a segment whose endpoint is live is live throughout, so `none` can be added to
its forbidden set. Halting is absorbing.

**Proof sketch.** A halt before the end would persist to the endpoint
(`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`). -/
theorem live {a b : Cfg k Γ S x} {t : ℕ} (h : Segment M F P a b t) (hb : b.state ≠ none) :
    Segment M (insert none F) P a b t := by
  refine ⟨h.1, fun u hu hm => ?_, h.2.2⟩
  rcases hm with hm | hm
  · exact MultiTapeTM.runFrom_state_ne_none_of_le M a t (by rw [h.1]; exact hb) u hu.le hm
  · exact h.2.1 u hu hm

end Segment

/-- **An endpoint-inclusive segment**: a segment whose endpoint is also off the forbidden set, so
that no time up to and including the end is in it. This is `splitSafe`'s shape; it is never a
first exit. -/
def SafeSegment {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (F : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (a b : Cfg k Γ S x) (t : ℕ) : Prop :=
  Segment M F P a b t ∧ b.state ∉ F

/-- An endpoint-inclusive segment avoids the forbidden set at every time through its end.

**Proof sketch.** Times before the end are the segment's cut; the end is the endpoint. -/
theorem safeSegment_iff {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
    {P : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ} :
    SafeSegment M F P a b t ↔ M.runFrom a t = b ∧ (∀ u ≤ t, (M.runFrom a u).state ∉ F) ∧
      ∀ u ≤ t, P (M.runFrom a u).workTapePos := by
  constructor
  · rintro ⟨⟨hr, hc, hp⟩, hb⟩
    refine ⟨hr, fun u hu => ?_, hp⟩
    rcases Nat.lt_or_ge u t with h | h
    · exact hc u h
    · obtain rfl : u = t := le_antisymm hu h
      rw [hr]
      exact hb
  · rintro ⟨hr, hc, hp⟩
    refine ⟨⟨hr, fun u hu => hc u hu.le, hp⟩, ?_⟩
    rw [← hr]
    exact hc t le_rfl

namespace SafeSegment

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- The empty endpoint-inclusive segment, at a start off the forbidden set. -/
theorem zero {a : Cfg k Γ S x} (ha : a.state ∉ F) (h : P a.workTapePos) :
    SafeSegment M F P a a 0 :=
  ⟨Segment.zero h, ha⟩

/-- Endpoint-inclusive segments concatenate at their configuration seam (`splitSafe_add`). -/
theorem trans {a b c : Cfg k Γ S x} {t v : ℕ} (h : SafeSegment M F P a b t)
    (g : SafeSegment M F P b c v) : SafeSegment M F P a c (t + v) :=
  ⟨h.1.trans g.1, g.2⟩

/-- Weakening an endpoint-inclusive segment. -/
theorem mono {F' : Set (Option S)} {P' : (Fin k → ℤ) → Prop} {a b : Cfg k Γ S x} {t : ℕ}
    (h : SafeSegment M F P a b t) (hF : F' ⊆ F) (hP : ∀ p, P p → P' p) :
    SafeSegment M F' P' a b t :=
  ⟨h.1.mono hF hP, fun hm => h.2 (hF hm)⟩

/-- **Never a first exit**: the endpoint of an endpoint-inclusive segment is off the forbidden
set, so a contract with those exits cannot end there. -/
theorem endpoint_not_mem {a b : Cfg k Γ S x} {t : ℕ} (h : SafeSegment M F P a b t) :
    b.state ∉ F :=
  h.2

end SafeSegment

namespace Contract

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- **Contract to segment**: every admissible run of a contract is a segment that avoids the
exits, ends at the endpoint, and keeps the heads in the envelope box. -/
theorem segment (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) :
    Segment M exits (HeadBox (C.lo i d) (C.hi i d)) d (C.post i d) (C.time i d) :=
  ⟨C.run i d hd hp, C.cut i d hd hp, fun u hu j => C.env i d hd hp u hu j⟩

/-- **Segment to contract** (the bridge when the endpoint is a first exit): a family of segments
that avoid `exits` and end in `exits`, with an interval box, is a contract. A segment avoiding a
larger forbidden set is first weakened by `Turing.Segment.mono`. -/
def ofSegment (pre : ι → Cfg k Γ S x → Prop) (time : ι → Cfg k Γ S x → ℕ)
    (post : ι → Cfg k Γ S x → Cfg k Γ S x) (lo hi : ι → Cfg k Γ S x → Fin k → ℤ)
    (seg : ∀ i d, d.state = some entry → pre i d →
      Segment M exits (HeadBox (lo i d) (hi i d)) d (post i d) (time i d))
    (exit_mem : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ exits) :
    Contract M entry exits ι x where
  pre := pre
  time := time
  post := post
  lo := lo
  hi := hi
  run i d hd hp := (seg i d hd hp).1
  exit_mem := exit_mem
  cut i d hd hp := (seg i d hd hp).2.1
  env i d hd hp u hu j := (seg i d hd hp).2.2 u hu j

/-! The specification API (user, 2026-10-16; its gate, finding 1): the segment bridge's data
fields as equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] ofSegment

/-- **The zero-time contract** of a machine started at its own exit `e`: every start is
admissible, the run is empty (`Turing.Segment.zero`), the endpoint is the start and the envelope
is the start's heads. It is the continuation of a branch or a phase that has nothing left to do. -/
def zero (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) : Contract M e {some e} ι x :=
  ofSegment (fun _ _ => True) (fun _ _ => 0) (fun _ d => d) (fun _ d => d.workTapePos)
    (fun _ d => d.workTapePos)
    (fun _ _ _ _ => Segment.zero
      ((headBox_iff _ _ _).mpr fun _ => Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩))
    (fun _ _ hd _ => by rw [hd]; exact Set.mem_singleton _)

/-! The zero-time contract's data fields as equations, without the `simp` attribute. -/

/-- Every start is admissible for `Turing.Contract.zero`. -/
theorem zero_pre (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).pre i d = True :=
  rfl

/-- `Turing.Contract.zero` takes no step. -/
theorem zero_time (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).time i d = 0 :=
  rfl

/-- `Turing.Contract.zero`'s endpoint is its start. -/
theorem zero_post (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).post i d = d :=
  rfl

/-- `Turing.Contract.zero`'s lower envelope is its start's heads. -/
theorem zero_lo (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).lo i d = d.workTapePos :=
  rfl

/-- `Turing.Contract.zero`'s upper envelope is its start's heads. -/
theorem zero_hi (M : MultiTapeTM k Γ S) (e : S) (ι : Type) (x : List Γ) (i : ι)
    (d : Cfg k Γ S x) : (zero M e ι x).hi i d = d.workTapePos :=
  rfl

/-- **The time-derived envelope of a contract**: every head stays within `time` cells of its
start, whatever the contract's own envelope says. -/
theorem time_envelope (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x) (u : ℕ)
    (hu : u ≤ C.time i d) (j : Fin k) :
    (M.runFrom d u).workTapePos j ∈
      Finset.Icc (d.workTapePos j - C.time i d) (d.workTapePos j + C.time i d) := by
  have h := MultiTapeTM.workTapePos_runFrom_mem_Icc M d u j
  rw [Finset.mem_Icc] at h ⊢
  have hu' : (u : ℤ) ≤ C.time i d := by exact_mod_cast hu
  constructor <;> omega

end Contract

/-! ## The round layer (design §16a, MIG-0b item 2)

A *round* starts at its anchor `a` and ends, after a positive exact time, back at `a` or in an
escape set `E`; at every strictly intermediate time it is live and visits neither `a` nor `E`.
This is the shape of `RecordTable`'s `rt_find_round_entry` and of the counter loop's **body
interface** (the round hypothesis of `counterLoopTMVia_run_done`, `_run_escape`): a
`Turing.Contract` fails its time-zero cut there, and a `Turing.ReturnContract` excludes the escape
(MIG-0a gate, round 1, counterexample 5). The counter loop's **host** runs are not rounds: they,
and the private `counterSpan` that describes them, are segments with a joint relation, with a
genuine zero-time case (MIG-0a gate, round 2). The counter loop over round contracts is in
`Build/CounterLoop`. -/

/-- The states a round's interior avoids: halting, the anchor and the escapes. -/
def roundStop {S : Type} (a : S) (E : Set (Option S)) : Set (Option S) :=
  insert none (insert (some a) E)

/-- Outside the round stop set means live, off the anchor and off the escapes: the form in which
the rows state their round cuts. -/
theorem not_mem_roundStop {S : Type} {a : S} {E : Set (Option S)} {q : Option S} :
    q ∉ roundStop a E ↔ ∃ s, q = some s ∧ s ≠ a ∧ some s ∉ E := by
  constructor
  · intro h
    cases q with
    | none => exact absurd (Set.mem_insert _ _) h
    | some s =>
      refine ⟨s, rfl, fun hs => h ?_, fun hs => h ?_⟩
      · rw [hs]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hs)
  · rintro ⟨s, rfl, hsa, hsE⟩ h
    rcases h with h | h | h
    · exact Option.some_ne_none s h
    · exact hsa (Option.some.inj h)
    · exact hsE h

/-- **A round** of `M` from `c`, with anchor `a` and escape set `E`: `c` is at the anchor, the
exact time `t` is positive, the run reaches `c'` at `t`, `c'` is at the anchor or in `E`, every
strictly intermediate state is live and off the anchor and `E`, and the head vector satisfies
`P` at every time up to `t`. -/
def Round {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (a : S) (E : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (c c' : Cfg k Γ S x) (t : ℕ) : Prop :=
  c.state = some a ∧ 0 < t ∧ M.runFrom c t = c' ∧ c'.state ∈ insert (some a) E ∧
    (∀ u, 0 < u → u < t → (M.runFrom c u).state ∉ roundStop a E) ∧
    ∀ u ≤ t, P (M.runFrom c u).workTapePos

/-- `Turing.Round M a E P c c' t` holds exactly when `c` is at the anchor `a`, `0 < t`,
`M.runFrom c t = c'`, the state of `c'` is `some a` or in `E`, every state at a time
`0 < u < t` lies outside `Turing.roundStop a E`, and the head vector satisfies `P` at every time
`u ≤ t` (the definition as a lemma). -/
theorem round_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (a : S) (E : Set (Option S))
    (P : (Fin k → ℤ) → Prop) (c c' : Cfg k Γ S x) (t : ℕ) :
    Round M a E P c c' t ↔ c.state = some a ∧ 0 < t ∧ M.runFrom c t = c' ∧
      c'.state ∈ insert (some a) E ∧
      (∀ u, 0 < u → u < t → (M.runFrom c u).state ∉ roundStop a E) ∧
      ∀ u ≤ t, P (M.runFrom c u).workTapePos :=
  Iff.rfl

namespace Round

variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S} {E : Set (Option S)}
  {P : (Fin k → ℤ) → Prop}

/-- **A round avoiding its escapes is a segment against them**, whatever its endpoint: at time
`0` it is at the anchor, which is no escape, and later it avoids the stop set. When the endpoint
is an escape, this segment is a first exit. -/
theorem segment {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) (ha : some a ∉ E) :
    Segment M E P c c' t := by
  obtain ⟨hc, -, hrun, -, hcut, henv⟩ := h
  refine ⟨hrun, fun u hu hm => ?_, henv⟩
  rcases Nat.eq_zero_or_pos u with rfl | hpos
  · rw [MultiTapeTM.runFrom_zero, hc] at hm
    exact ha hm
  · exact hcut u hpos hu (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hm))

/-- The round cut in the rows' form: every intermediate state is `some s` with `s` off the anchor
and the escapes. -/
theorem cut_some {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) :
    ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧ s ≠ a ∧ some s ∉ E :=
  fun u hu hut => not_mem_roundStop.mp (h.2.2.2.2.1 u hu hut)

/-- **Rounds from the rows' form** (the fit for `rt_find_round_entry` and the counter loop): a
positive-time run from the anchor whose intermediate states are live and off both the anchor `a`
and a single escape `e`, ending at one of them, is a round with escape set `{some e}`.

**Proof sketch.** Rewrite the cut by `Turing.not_mem_roundStop`; the endpoint is in
`{some a, some e}`; the relation is trivial. -/
theorem of_cut {e : S} {c : Cfg k Γ S x} {t : ℕ} (hc : c.state = some a) (ht : 0 < t)
    (hcut : ∀ u, 0 < u → u < t → ∃ s, (M.runFrom c u).state = some s ∧ s ≠ a ∧ s ≠ e)
    (hend : (M.runFrom c t).state = some a ∨ (M.runFrom c t).state = some e) :
    Round M a {some e} (fun _ => True) c (M.runFrom c t) t := by
  refine ⟨hc, ht, rfl, ?_, fun u hu hut => ?_, fun _ _ => trivial⟩
  · rcases hend with h | h
    · rw [h]
      exact Set.mem_insert _ _
    · rw [h]
      exact Set.mem_insert_of_mem _ rfl
  · obtain ⟨s, hs, hsa, hse⟩ := hcut u hu hut
    exact not_mem_roundStop.mpr ⟨s, hs, hsa, fun h => hse (Option.some.inj h)⟩

/-- A round's relation can be replaced by the time-derived box about its start. -/
theorem time_box {c c' : Cfg k Γ S x} {t : ℕ} (h : Round M a E P c c' t) :
    Round M a E (HeadBox (fun j => c.workTapePos j - t) (fun j => c.workTapePos j + t)) c c' t := by
  obtain ⟨hc, ht, hrun, hend, hcut, -⟩ := h
  refine ⟨hc, ht, hrun, hend, hcut, fun u hu j => ?_⟩
  have h := MultiTapeTM.workTapePos_runFrom_mem_Icc M c u j
  simp only [Finset.mem_Icc] at h ⊢
  have hu' : (u : ℤ) ≤ t := by exact_mod_cast hu
  constructor <;> omega

end Round

/-- **The round orbit**: the round-start configurations when each round from `c` lasts `τ c`
steps, stated in the core so that round iteration needs no counter. `CounterLoop`'s
`Turing.counterLoopOrbit` is an abbreviation of it. -/
def roundOrbit {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (r : ℕ) : Cfg k Γ S x :=
  (fun c => M.runFrom c (τ c))^[r] c

/-- The orbit starts at its start: `roundOrbit M τ c 0 = c`. -/
theorem roundOrbit_zero {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) : roundOrbit M τ c 0 = c :=
  rfl

/-- The next round starts where the current one ends. -/
theorem roundOrbit_succ {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (τ : Cfg k Γ S x → ℕ)
    (c : Cfg k Γ S x) (r : ℕ) :
    roundOrbit M τ c (r + 1) = M.runFrom (roundOrbit M τ c r) (τ (roundOrbit M τ c r)) :=
  Function.iterate_succ_apply' _ _ _

/-- **Round iteration along a sequence of starts**: if the anchor is not an escape
(`some a ∉ E`), the head condition `P` holds at `cs 0`, and, for each `r < n`, the run from `cs r`
is a round ending at `cs (r + 1)` after `τ r` steps, then the run from `cs 0` is one segment
against the escapes to `cs n`, of length the sum of the round times. When the last round ends in
an escape, the segment is a first exit (`Turing.Contract.ofSegment`).

**Proof sketch.** Each round is a segment (`Turing.Round.segment`, since the anchor is not an
escape); compose them along the sequence (`Turing.Segment.iterate_seq`). -/
theorem Round.iterate_seq {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S}
    {E : Set (Option S)} {P : (Fin k → ℤ) → Prop} (cs : ℕ → Cfg k Γ S x) (τ : ℕ → ℕ)
    (ha : some a ∉ E) (h0 : P (cs 0).workTapePos) (n : ℕ)
    (hround : ∀ r < n, Round M a E P (cs r) (cs (r + 1)) (τ r)) :
    Segment M E P (cs 0) (cs n) (∑ r ∈ Finset.range n, τ r) :=
  Segment.iterate_seq cs τ h0 n fun r hr => (hround r hr).segment ha

/-- **Round iteration on one machine** (the counter loop's composition, without the counter):
if the anchor is not an escape (`some a ∉ E`), the head condition `P` holds at `c`, and the first
`n` rounds of the orbit are rounds, each lasting `τ` of its start, then the whole orbit prefix is
one segment against the escapes, of length the sum of the round times. When the last round ends
in an escape, the segment is a first exit (`Turing.Contract.ofSegment`).

**Proof sketch.** The orbit `Turing.roundOrbit` as the sequence of starts in
`Turing.Round.iterate_seq`; it starts at `c` (`Turing.roundOrbit_zero`). -/
theorem Round.iterate {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S}
    {E : Set (Option S)} {P : (Fin k → ℤ) → Prop} (τ : Cfg k Γ S x → ℕ) (c : Cfg k Γ S x)
    (ha : some a ∉ E) (h0 : P c.workTapePos) (n : ℕ)
    (hround : ∀ r < n, Round M a E P (roundOrbit M τ c r) (roundOrbit M τ c (r + 1))
      (τ (roundOrbit M τ c r))) :
    Segment M E P c (roundOrbit M τ c n) (∑ r ∈ Finset.range n, τ (roundOrbit M τ c r)) := by
  have h := Round.iterate_seq (roundOrbit M τ c) (fun r => τ (roundOrbit M τ c r)) ha
    (by rw [roundOrbit_zero]; exact h0) n hround
  rwa [roundOrbit_zero] at h

/-- **A round contract** (design §16a item 2): from every admissible start at `anchor`, the run
ends after a positive exact time back at the anchor or in the escape set; strictly in between it
is live and avoids both; and every head stays in its interval. A `Turing.ReturnContract` is the
case without escapes (`Turing.ReturnContract.toRound`). -/
structure RoundContract {S : Type} (M : MultiTapeTM k Γ S) (anchor : S) (escape : Set (Option S))
    (ι : Type) (x : List Γ) where
  /-- The precondition. -/
  pre : ι → Cfg k Γ S x → Prop
  /-- The exact, positive running time. -/
  time : ι → Cfg k Γ S x → ℕ
  /-- The endpoint, at the anchor or an escape. -/
  post : ι → Cfg k Γ S x → Cfg k Γ S x
  /-- The lower ends of the head envelope. -/
  lo : ι → Cfg k Γ S x → Fin k → ℤ
  /-- The upper ends of the head envelope. -/
  hi : ι → Cfg k Γ S x → Fin k → ℤ
  pos : ∀ i d, d.state = some anchor → pre i d → 0 < time i d
  run : ∀ i d, d.state = some anchor → pre i d → M.runFrom d (time i d) = post i d
  exit_mem : ∀ i d, d.state = some anchor → pre i d →
    (post i d).state ∈ insert (some anchor) escape
  cut : ∀ i d, d.state = some anchor → pre i d →
    ∀ u, 0 < u → u < time i d → (M.runFrom d u).state ∉ roundStop anchor escape
  env : ∀ i d, d.state = some anchor → pre i d → ∀ u ≤ time i d, ∀ j,
    (M.runFrom d u).workTapePos j ∈ Finset.Icc (lo i d j) (hi i d j)

namespace RoundContract

variable {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {escape : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- Every admissible run of a round contract is a round. -/
theorem round (R : RoundContract M anchor escape ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some anchor) (hp : R.pre i d) :
    Round M anchor escape (HeadBox (R.lo i d) (R.hi i d)) d (R.post i d) (R.time i d) :=
  ⟨hd, R.pos i d hd hp, R.run i d hd hp, R.exit_mem i d hd hp, R.cut i d hd hp,
    fun u hu j => R.env i d hd hp u hu j⟩

/-- **The returning case** is a `Turing.ReturnContract`: restrict the precondition to the starts
whose endpoint is back at the anchor. -/
def returning (R : RoundContract M anchor escape ι x) : ReturnContract M anchor ι x where
  pre i d := R.pre i d ∧ (R.post i d).state = some anchor
  time := R.time
  post := R.post
  lo := R.lo
  hi := R.hi
  pos i d hd hp := R.pos i d hd hp.1
  run i d hd hp := R.run i d hd hp.1
  exit_eq _ _ _ hp := hp.2
  cut i d hd hp u hu hut h := R.cut i d hd hp.1 u hu hut (by
    rw [h]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  env i d hd hp := R.env i d hd hp.1

/-- **The escaping case** is a `Turing.Contract` with the escapes as exits: restrict the
precondition to the starts whose endpoint escapes. The time-zero cut needs the anchor to be no
escape.

**Proof sketch.** At time `0` the state is the anchor, which is no escape; later it avoids the
stop set, which contains the escapes. -/
def escaping (R : RoundContract M anchor escape ι x) (ha : some anchor ∉ escape) :
    Contract M anchor escape ι x where
  pre i d := R.pre i d ∧ (R.post i d).state ∈ escape
  time := R.time
  post := R.post
  lo := R.lo
  hi := R.hi
  run i d hd hp := R.run i d hd hp.1
  exit_mem _ _ _ hp := hp.2
  cut i d hd hp := ((R.round i d hd hp.1).segment ha).2.1
  env i d hd hp := R.env i d hd hp.1

/-! The specification API: the two restrictions' data fields as equations, without the `simp`
attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] returning escaping

end RoundContract

/-- **A returning contract is a round contract without escapes.** Its intermediate states are
live, since a halt would persist to the endpoint, which is at the anchor.

**Proof sketch.** Off the anchor is the returning cut. Liveness: halting is absorbing
(`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`), so a halt before the time would make
the endpoint's state `none`, not the anchor. -/
def ReturnContract.toRound {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {ι : Type}
    {x : List Γ} (C : ReturnContract M anchor ι x) : RoundContract M anchor ∅ ι x where
  pre := C.pre
  time := C.time
  post := C.post
  lo := C.lo
  hi := C.hi
  pos := C.pos
  run := C.run
  exit_mem i d hd hp := by
    rw [C.exit_eq i d hd hp]
    exact Set.mem_insert _ _
  cut i d hd hp u hu hut := by
    apply not_mem_roundStop.mpr
    cases hs : (M.runFrom d u).state with
    | none =>
      refine absurd hs (MultiTapeTM.runFrom_state_ne_none_of_le M d _ ?_ u hut.le)
      rw [C.run i d hd hp, C.exit_eq i d hd hp]
      exact Option.some_ne_none _
    | some s =>
      refine ⟨s, rfl, fun h => C.cut i d hd hp u hu hut (by rw [hs, h]), fun h => h⟩
  env := C.env

/-! The specification API: the conversion's data fields as equations, without the `simp`
attribute. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi] ReturnContract.toRound

/-! ## Hulls of round boxes along an orbit (MIG-0b)

The envelope of an iterated round contract: the tape-wise hull of the first `n` round boxes and
of the final orbit head. `Build/CounterLoop`'s round-contract compositions use it. -/

namespace RoundContract

variable {S : Type} {M : MultiTapeTM k Γ S} {a : S} {E : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- The lower ends of the **hull of an orbit's round boxes**: tape by tape, the least lower end
of the envelopes of the first `n` rounds of the orbit from `c` (each lasting the round
contract's time), and of the head at the `n`-th orbit point. -/
def hullLo (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) : ℤ :=
  (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one fun r =>
    if r < n then R.lo i (roundOrbit M (R.time i) c r) j
    else (roundOrbit M (R.time i) c r).workTapePos j

/-- The hull's lower end on tape `j` is the least, over `r ≤ n`, of the `r`-th round's lower end
`R.lo i (orbit r) j` for `r < n` and of the `n`-th orbit point's head, the orbit taken with the
round contract's time (the definition as a lemma). -/
theorem hullLo_eq (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) :
    R.hullLo i c n j = (Finset.range (n + 1)).inf' Finset.nonempty_range_add_one fun r =>
      if r < n then R.lo i (roundOrbit M (R.time i) c r) j
      else (roundOrbit M (R.time i) c r).workTapePos j :=
  rfl

/-- The upper ends of the hull of an orbit's round boxes (see `Turing.RoundContract.hullLo`). -/
def hullHi (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) : ℤ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun r =>
    if r < n then R.hi i (roundOrbit M (R.time i) c r) j
    else (roundOrbit M (R.time i) c r).workTapePos j

/-- The hull's upper end on tape `j` is the greatest, over `r ≤ n`, of the `r`-th round's upper
end `R.hi i (orbit r) j` for `r < n` and of the `n`-th orbit point's head, the orbit taken with
the round contract's time (the definition as a lemma). -/
theorem hullHi_eq (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x) (n : ℕ) (j : Fin k) :
    R.hullHi i c n j = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun r =>
      if r < n then R.hi i (roundOrbit M (R.time i) c r) j
      else (roundOrbit M (R.time i) c r).workTapePos j :=
  rfl

/-- Along admissible rounds of the orbit, each returning except possibly the last, every orbit
point before `n` is at the anchor.

**Proof sketch.** Induction: a round from the anchor ends at the round contract's endpoint
(`run`), which is the next orbit point, and that endpoint is at the anchor when the round
returns. -/
theorem orbit_anchor (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    ∀ r < n, (roundOrbit M (R.time i) c r).state = some a := by
  intro r hr
  induction r with
  | zero => exact hc
  | succ r ih =>
    rw [roundOrbit_succ, R.run i _ (ih (by omega)) (hpre r (by omega))]
    exact hret r hr

/-- **The orbit's rounds** under the hull box: each of the first `n` orbit rounds is a round,
ending at the next orbit point, with its heads in the hull of all the round boxes.

**Proof sketch.** `Turing.RoundContract.round` at each orbit point, which is at the anchor by
`Turing.RoundContract.orbit_anchor`; its endpoint is the next orbit point (`run`), and its own box
lies in the hull (`Finset.inf'_le`, `Finset.le_sup'`). -/
theorem orbit_round (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    ∀ r < n, Round M a E (HeadBox (R.hullLo i c n) (R.hullHi i c n))
      (roundOrbit M (R.time i) c r) (roundOrbit M (R.time i) c (r + 1))
      (R.time i (roundOrbit M (R.time i) c r)) := by
  intro r hr
  have ha := R.orbit_anchor i c hc n hpre hret r hr
  have hR := R.round i _ ha (hpre r hr)
  have hnext : roundOrbit M (R.time i) c (r + 1) = R.post i (roundOrbit M (R.time i) c r) := by
    rw [roundOrbit_succ, R.run i _ ha (hpre r hr)]
  rw [hnext]
  refine ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2.1, fun u hu j => ?_⟩
  have hb := hR.2.2.2.2.2 u hu j
  have hmem : r ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [Finset.mem_Icc] at hb ⊢
  constructor
  · refine le_trans (Finset.inf'_le (fun r => if r < n then R.lo i (roundOrbit M (R.time i) c r) j
      else (roundOrbit M (R.time i) c r).workTapePos j) hmem) ?_
    simp only [if_pos hr]
    exact hb.1
  · refine le_trans ?_ (Finset.le_sup' (fun r => if r < n then
      R.hi i (roundOrbit M (R.time i) c r) j else (roundOrbit M (R.time i) c r).workTapePos j) hmem)
    simp only [if_pos hr]
    exact hb.2

/-- The start of the orbit lies in the hull box.

**Proof sketch.** With no round, the hull is the start itself; otherwise the start is time `0`
of the first round. -/
theorem orbit_start (R : RoundContract M a E ι x) (i : ι) (c : Cfg k Γ S x)
    (hc : c.state = some a) (n : ℕ) (hpre : ∀ r < n, R.pre i (roundOrbit M (R.time i) c r))
    (hret : ∀ r, r + 1 < n → (R.post i (roundOrbit M (R.time i) c r)).state = some a) :
    HeadBox (R.hullLo i c n) (R.hullHi i c n) c.workTapePos := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro j
    simp [hullLo, hullHi, roundOrbit]
  · exact (R.orbit_round i c hc n hpre hret 0 hn).2.2.2.2.2 0 (Nat.zero_le _)

end RoundContract

/-- The host box of a counter loop: the counter interval on the last tape, and a body box on the
others. -/
theorem headBox_lastCases {lo hi : Fin k → ℤ} {clo chi : ℤ} {p : Fin (k + 1) → ℤ}
    (hc : p (Fin.last k) ∈ Finset.Icc clo chi) (hb : HeadBox lo hi fun j => p j.castSucc) :
    HeadBox (Fin.lastCases (motive := fun _ => ℤ) clo lo)
      (Fin.lastCases (motive := fun _ => ℤ) chi hi) p := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa only [Fin.lastCases_last] using hc
  | cast i => simpa only [Fin.lastCases_castSucc] using hb i

/-! ## The joint-trajectory layer (design §16a, MIG-0b item 3)

Per-tape intervals cannot express a relation between heads, such as "the two heads are equal"
(MIG-0a gate, round 1, counterexample 6), and `CounterLoop`'s `counterSpan` carries exactly such a
relation on the body heads. `Turing.Contract.Traj` names one, as a derived property in the manner
of `Turing.Contract.Frames`: it is not a field, every contract has its envelope box as one
(`Turing.Contract.traj_env`), and the compositions preserve them (`trans` here; `seq`, `inPhase`
and `branch` in `Build/Contract/Seam`; `embed` in `Build/Contract/Embed`). -/

namespace Contract

/-- A contract **has the joint trajectory** `R` when, for every index `i` and every admissible
start `d`, the whole head vector satisfies `R i d` at every time up to the endpoint. -/
def Traj {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
    {x : List Γ} (C : Contract M entry exits ι x)
    (R : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop) : Prop :=
  ∀ i d, d.state = some entry → C.pre i d → ∀ u ≤ C.time i d, R i d (M.runFrom d u).workTapePos

/-- A contract has the joint trajectory `R` exactly when, for every index `i` and every
admissible start `d` at the entry, the head vector satisfies `R i d` at every time
`u ≤ C.time i d` (the definition as a lemma). -/
theorem traj_iff {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)}
    {ι : Type} {x : List Γ} (C : Contract M entry exits ι x)
    (R : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop) :
    C.Traj R ↔ ∀ i d, d.state = some entry → C.pre i d →
      ∀ u ≤ C.time i d, R i d (M.runFrom d u).workTapePos :=
  Iff.rfl

section TrajBasic

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- Every contract has its envelope box as a joint trajectory. -/
theorem traj_env (C : Contract M entry exits ι x) :
    C.Traj fun i d => HeadBox (C.lo i d) (C.hi i d) :=
  fun i d hd hp u hu j => C.env i d hd hp u hu j

/-- Weakening a joint trajectory. -/
theorem Traj.mono {C : Contract M entry exits ι x} {R R' : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h : C.Traj R) (hR : ∀ i d p, R i d p → R' i d p) : C.Traj R' :=
  fun i d hd hp u hu => hR i d _ (h i d hd hp u hu)

/-- Two joint trajectories hold jointly. -/
theorem Traj.and {C : Contract M entry exits ι x} {R R' : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h : C.Traj R) (h' : C.Traj R') : C.Traj fun i d p => R i d p ∧ R' i d p :=
  fun i d hd hp u hu => ⟨h i d hd hp u hu, h' i d hd hp u hu⟩

/-- **A joint trajectory is a segment relation**: every admissible run is a segment against the
exits, ending at the endpoint, with the relation along it. -/
theorem Traj.segment {C : Contract M entry exits ι x}
    {R : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop} (h : C.Traj R) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) :
    Segment M exits (R i d) d (C.post i d) (C.time i d) :=
  ⟨C.run i d hd hp, C.cut i d hd hp, h i d hd hp⟩

/-- **`trans` preserves joint trajectories**: up to the first contract's time the first relation
holds, and after it the second, at the linked index and the first endpoint.

**Proof sketch.** Split the time at the first contract's time, as in `Turing.Contract.trans`'s
envelope. -/
theorem Traj.trans {e₁ e₂ : S} {X : Set (Option S)} {κ : Type} {C₁ : Contract M e₁ {some e₂} ι x}
    {C₂ : Contract M e₂ X κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d)}
    {hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X}
    {R₁ : ι → Cfg k Γ S x → (Fin k → ℤ) → Prop} {R₂ : κ → Cfg k Γ S x → (Fin k → ℤ) → Prop}
    (h₁ : C₁.Traj R₁) (h₂ : C₂.Traj R₂) :
    (C₁.trans C₂ link hlink hX).Traj fun i d p => R₁ i d p ∨ R₂ (link i) (C₁.post i d) p := by
  intro i d hd hp u hu
  have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)
  change u ≤ C₁.time i d + C₂.time (link i) (C₁.post i d) at hu
  by_cases h : u ≤ C₁.time i d
  · exact Or.inl (h₁ i d hd hp u h)
  · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp h))
    rw [MultiTapeTM.runFrom_add, C₁.run i d hd hp]
    exact Or.inr (h₂ _ _ hx (hlink i d hd hp) v (by omega))

/-- **`trans` preserves frames**: footprints add up (`Turing.Cfg.SameOutside.trans`). -/
theorem Frames.trans {e₁ e₂ : S} {X : Set (Option S)} {κ : Type}
    {C₁ : Contract M e₁ {some e₂} ι x} {C₂ : Contract M e₂ X κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d)}
    {hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X}
    {fp₁ : ι → Cfg k Γ S x → Fin k → Set ℤ} {fp₂ : κ → Cfg k Γ S x → Fin k → Set ℤ}
    (h₁ : C₁.Frames fp₁) (h₂ : C₂.Frames fp₂) :
    (C₁.trans C₂ link hlink hX).Frames fun i d j => fp₁ i d j ∪ fp₂ (link i) (C₁.post i d) j :=
  fun i d hd hp => (h₁ i d hd hp).trans
    (h₂ _ _ (Set.mem_singleton_iff.mp (C₁.exit_mem i d hd hp)) (hlink i d hd hp))

end TrajBasic

end Contract

/-! ## Sanity lemmas (design §16a, MIG-0b item 7; MIG-0a gate, round 1, counterexample 1)

The positivity of the seam compositions and of the releases is in `Build/Contract/Seam`, and that
of `embed` in `Build/Contract/Embed`. -/

namespace Contract

section Sanity

variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}
  {x : List Γ}

/-- **The zero-time characterization**: on an admissible start, a contract's time is `0` exactly
when its entry is among its exits.

**Proof sketch.** If the time is `0`, the endpoint is the start, which is at the entry, and the
endpoint is at an exit. If the entry is an exit and the time were positive, the cut at time `0`
would exclude it. -/
theorem time_eq_zero_iff (C : Contract M entry exits ι x) (i : ι) (d : Cfg k Γ S x)
    (hd : d.state = some entry) (hp : C.pre i d) : C.time i d = 0 ↔ some entry ∈ exits := by
  constructor
  · intro h
    have hx := C.exit_mem i d hd hp
    rw [← C.run i d hd hp, h, MultiTapeTM.runFrom_zero, hd] at hx
    exact hx
  · intro h
    by_contra hne
    exact C.cut i d hd hp 0 (Nat.pos_of_ne_zero hne) (by rw [MultiTapeTM.runFrom_zero, hd]; exact h)

/-- A contract whose entry is no exit is positive. -/
theorem positive_of_not_mem (C : Contract M entry exits ι x) (h : some entry ∉ exits) :
    C.Positive :=
  fun i d hd hp => Nat.pos_of_ne_zero fun h0 => h ((C.time_eq_zero_iff i d hd hp).mp h0)

/-- A positive contract with an admissible start has its entry outside its exits. -/
theorem not_mem_of_positive (C : Contract M entry exits ι x) (h : C.Positive) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : C.pre i d) : some entry ∉ exits :=
  fun hm => (Nat.pos_iff_ne_zero.mp (h i d hd hp)) ((C.time_eq_zero_iff i d hd hp).mpr hm)

/-- `trans` of a positive first contract is positive. -/
theorem trans_positive {e₁ e₂ : S} {X : Set (Option S)} {κ : Type}
    (C₁ : Contract M e₁ {some e₂} ι x) (C₂ : Contract M e₂ X κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some e₁ → C₁.pre i d → C₂.pre (link i) (C₁.post i d))
    (hX : ∀ i d, d.state = some e₁ → C₁.pre i d → ∀ u < C₁.time i d, (M.runFrom d u).state ∉ X)
    (h : C₁.Positive) : (C₁.trans C₂ link hlink hX).Positive :=
  fun i d hd hp => Nat.lt_of_lt_of_le (h i d hd hp) (Nat.le_add_right _ _)

end Sanity

end Contract

/-! ## Transports (design §16a, MIG-0b item 6; §16, *transports*)

Contract-to-contract theorems along the library's simulations: state renaming along an embedding,
and the macro-step lockstep (`Turing.Lockstep`), the common shape of alphabet reduction
([AB09, Claim 1.5]; `Robustness/AlphabetReduction`, `L = 3(|Γ| + 1) + 2` steps per source step)
and of the robustness layer's lockstep combinators. The alphabet-reduction adapter (the
lockstep instance and its contract theorem) lands with RS-5 in `Robustness/AlphabetReduction`,
where its lockstep is proved; the symbol lift (through `Cfg.decodeSymbols`) is in
`Build/Contract/Lift`. -/

namespace Contract

/-- The renamed prefix of a contract run: up to its time, the host run from a start at the renamed
entry is the source run from the state-replaced start, renamed.

**Proof sketch.** The renamed source start is the host start. The guard holds before the time,
so `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` transports every prefix. -/
private lemma mapState_traj {S H : Type} {M : MultiTapeTM k Γ S} {entry : S} {X : Set (Option S)}
    {ι : Type} {x : List Γ} (C : Contract M entry X ι x) (N : MultiTapeTM k Γ H) (emb : S ↪ H)
    (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work, N.tr (emb q) inp work = (M.tr q inp work).mapState emb)
    (hgood : ∀ i d, d.state = some entry → C.pre i d →
      ∀ u < C.time i d, ∀ q, (M.runFrom d u).state = some q → good q)
    (i : ι) (d : Cfg k Γ H x) (hd : d.state = some (emb entry))
    (hp : C.pre i (d.mapState fun _ => entry)) :
    ∀ u ≤ C.time i (d.mapState fun _ => entry),
      N.runFrom d u = (M.runFrom (d.mapState fun _ => entry) u).mapState emb := by
  have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
  have hd' : (d.mapState fun _ => entry).mapState emb = d :=
    Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl
  intro u hu
  have H := MultiTapeTM.runFrom_mapState_of_agreeOn M N emb good hagree _ u
    (fun v hv => hgood i _ hc hp v (by omega))
  rwa [hd'] at H

/-- **State renaming along an embedding** (`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`): a
host whose table agrees, on the renamed good states, with the source table renamed, runs every
contract of the source whose runs stay in good states before their time. The host's entry and
exits are the renamed ones; the time and the envelope are the source's, at the state-replaced
start, and the endpoint is the source endpoint, renamed. This is the transport behind the phase
host, the counter loop's body phase and the call controllers.

**Proof sketch.** By the renamed prefix (`mapState_traj`): the run and the exit are the source's,
renamed; a renamed state is a renamed exit only if the source state is an exit, by injectivity;
and the heads are the source's. -/
def mapState {S H : Type} {M : MultiTapeTM k Γ S} {entry : S} {X : Set (Option S)} {ι : Type}
    {x : List Γ} (C : Contract M entry X ι x) (N : MultiTapeTM k Γ H) (emb : S ↪ H)
    (good : S → Prop)
    (hagree : ∀ q, good q → ∀ inp work, N.tr (emb q) inp work = (M.tr q inp work).mapState emb)
    (hgood : ∀ i d, d.state = some entry → C.pre i d →
      ∀ u < C.time i d, ∀ q, (M.runFrom d u).state = some q → good q) :
    Contract N (emb entry) (Option.map emb '' X) ι x where
  pre i d := C.pre i (d.mapState fun _ => entry)
  time i d := C.time i (d.mapState fun _ => entry)
  post i d := (C.post i (d.mapState fun _ => entry)).mapState emb
  lo i d := C.lo i (d.mapState fun _ => entry)
  hi i d := C.hi i (d.mapState fun _ => entry)
  run i d hd hp := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp _ le_rfl, C.run i _ hc hp]
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    exact ⟨_, C.exit_mem i _ hc hp, rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp u hu.le]
    rintro ⟨q, hq, heq⟩
    have hq' : q = (M.runFrom (d.mapState fun _ => entry) u).state :=
      Option.map_injective emb.injective heq
    exact C.cut i _ hc hp u hu (hq' ▸ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => entry).state = some entry := by simp [Cfg.mapState, hd]
    rw [mapState_traj C N emb good hagree hgood i d hd hp u hu]
    exact C.env i _ hc hp u hu j

end Contract

/-- **A macro-step lockstep** (design §16, *lockstep combinators*): every source step from a
configuration off the exits `X` is simulated by exactly `cost c` target steps through the
encoding `enc`; an encoded exit is a target exit in `X'`; and inside a simulated step the target
meets no target exit. Alphabet reduction ([AB09, Claim 1.5]) is the case
`cost = 3(|Γ| + 1) + 2`; a lockstep decoration is the case `cost = 1`. Neither a positive cost
nor an injective encoding is required. -/
structure Lockstep {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    (M : MultiTapeTM k Γ S) (N : MultiTapeTM k' Γ' S') (enc : Cfg k Γ S x → Cfg k' Γ' S' x')
    (cost : Cfg k Γ S x → ℕ) (X : Set (Option S)) (X' : Set (Option S')) : Prop where
  step : ∀ c, c.state ∉ X → N.runFrom (enc c) (cost c) = enc (M.step c)
  exit : ∀ c, c.state ∈ X → (enc c).state ∈ X'
  inner : ∀ c, c.state ∉ X → ∀ v < cost c, (N.runFrom (enc c) v).state ∉ X'

namespace Lockstep

variable {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'} {M : MultiTapeTM k Γ S}
  {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'} {cost : Cfg k Γ S x → ℕ}
  {X : Set (Option S)} {X' : Set (Option S')}

/-- **The lockstep over a run**: a source run of `t` steps that avoids `X` before `t` is simulated
by the sum of its step costs.

**Proof sketch.** Induction on `t`, with one `step` per source step
(`Turing.MultiTapeTM.runFrom_add`). -/
theorem runFrom (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    N.runFrom (enc d) (∑ u ∈ Finset.range t, cost (M.runFrom d u)) = enc (M.runFrom d t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, MultiTapeTM.runFrom_add, ih fun u hu => ht u (by omega),
      L.step _ (ht t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- **The lockstep cut**: a simulated run that avoids `X` before `t` avoids `X'` before the sum
of its step costs.

**Proof sketch.** Induction on `t`: a time in the last simulated step is an inner time of that
step, from the encoded configuration reached by `Turing.Lockstep.runFrom`. -/
theorem cut (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    ∀ v < ∑ u ∈ Finset.range t, cost (M.runFrom d u), (N.runFrom (enc d) v).state ∉ X' := by
  induction t with
  | zero => simp
  | succ t ih =>
    intro v hv
    rw [Finset.sum_range_succ] at hv
    by_cases hlt : v < ∑ u ∈ Finset.range t, cost (M.runFrom d u)
    · exact ih (fun u hu => ht u (by omega)) v hlt
    · obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hlt)
      rw [MultiTapeTM.runFrom_add, L.runFrom d t fun u hu => ht u (by omega)]
      exact L.inner _ (ht t (by omega)) w (by omega)

/-- **Locating a target time**: every target time up to the simulated length of a source run
lies in one simulated step, at an offset inside it (or is the start of the step after the last).

**Proof sketch.** Induction on `t`: a time beyond the first `t` simulated steps is an offset in
the last one, from the encoded configuration reached by `Turing.Lockstep.runFrom`. -/
theorem locate (L : Lockstep M N enc cost X X') (d : Cfg k Γ S x) (t : ℕ)
    (ht : ∀ u < t, (M.runFrom d u).state ∉ X) :
    ∀ v ≤ ∑ u ∈ Finset.range t, cost (M.runFrom d u), ∃ u ≤ t, ∃ w,
      (w = 0 ∨ ((M.runFrom d u).state ∉ X ∧ w ≤ cost (M.runFrom d u))) ∧
      N.runFrom (enc d) v = N.runFrom (enc (M.runFrom d u)) w := by
  induction t with
  | zero =>
    intro v hv
    simp only [Finset.range_zero, Finset.sum_empty, Nat.le_zero] at hv
    exact ⟨0, le_rfl, 0, Or.inl rfl, by rw [hv]; rfl⟩
  | succ t ih =>
    intro v hv
    rw [Finset.sum_range_succ] at hv
    by_cases hle : v ≤ ∑ u ∈ Finset.range t, cost (M.runFrom d u)
    · obtain ⟨u, hu, w, hw, he⟩ := ih (fun u hu => ht u (by omega)) v hle
      exact ⟨u, by omega, w, hw, he⟩
    · obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.mp hle))
      refine ⟨t, by omega, w, Or.inr ⟨ht t (by omega), by omega⟩, ?_⟩
      rw [MultiTapeTM.runFrom_add, L.runFrom d t fun u hu => ht u (by omega)]

end Lockstep

/-- **Transport along a macro-step lockstep**. A source contract becomes a
target contract whose index also records the source start: an admissible target start is the
encoding of an admissible source start. The time is the sum of the step costs along the source
run, the endpoint is the encoded source endpoint, and the envelope is the hull of per-step boxes
`blo`, `bhi`, which `hbox` asserts for every simulated step and every encoded configuration.

**Proof sketch.** The run is `Turing.Lockstep.runFrom` and the cut `Turing.Lockstep.cut`, fed the
source cut; the exit is `exit` at the source endpoint. For the envelope, a target time lies in
one simulated step, at an offset inside it (`Turing.Lockstep.locate`); `hbox` bounds the heads
there by that step's box, which lies inside the hull over the source run.

The target entry `entry'` is a free parameter: no premise relates it to the encoding. The
admissible target starts are the encodings of admissible source starts that lie at `entry'`.
A sufficient condition for every admissible source start to transport is that the encoding
sends every source configuration at `entry` to one at `entry'`
(`Turing.Contract.lockstep_admissible`; for a state-renaming encoding,
`Turing.Contract.lockstep_admissible_map`); compatibility on the admissible source starts
alone also suffices. Without any compatibility the contract may have no admissible start. -/
def Contract.lockstep {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (entry' : S')
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j)) :
    Contract N entry' X' (ι × Cfg k Γ S x) x' where
  pre p d' := d' = enc p.2 ∧ p.2.state = some entry ∧ C.pre p.1 p.2
  time p _ := ∑ u ∈ Finset.range (C.time p.1 p.2), cost (M.runFrom p.2 u)
  post p _ := enc (C.post p.1 p.2)
  lo p _ j := (Finset.range (C.time p.1 p.2 + 1)).inf' Finset.nonempty_range_add_one
    fun u => blo (M.runFrom p.2 u) j
  hi p _ j := (Finset.range (C.time p.1 p.2 + 1)).sup' Finset.nonempty_range_add_one
    fun u => bhi (M.runFrom p.2 u) j
  run p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    rw [L.runFrom p.2 _ (C.cut p.1 p.2 hs hc), C.run p.1 p.2 hs hc]
  exit_mem p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    exact L.exit _ (C.exit_mem p.1 p.2 hs hc)
  cut p d' _ hp := by
    obtain ⟨rfl, hs, hc⟩ := hp
    exact L.cut p.2 _ (C.cut p.1 p.2 hs hc)
  env p d' _ hp v hv j := by
    obtain ⟨rfl, hs, hc⟩ := hp
    obtain ⟨u, hu, w, hw, he⟩ := L.locate p.2 _ (C.cut p.1 p.2 hs hc) v hv
    have hb := hbox (M.runFrom p.2 u) w hw j
    rw [he]
    have hmem : u ∈ Finset.range (C.time p.1 p.2 + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.mem_Icc] at hb ⊢
    exact ⟨(Finset.inf'_le (fun u => blo (M.runFrom p.2 u) j) hmem).trans hb.1,
      hb.2.trans (Finset.le_sup' (fun u => bhi (M.runFrom p.2 u) j) hmem)⟩

/-! The specification API: the state renaming's and the lockstep transport's data fields as
equations, without the `simp` attribute. (`Turing.Contract.mapState`'s line sits here, not after
its definition, so that the copy-text screen does not attach it to that body.) -/
attribute [simps (config := { isSimp := false }) pre time post lo hi]
  Contract.mapState Contract.lockstep

/-- **Admissible starts of a lockstep transport** (the entry-compatibility condition, MIG-0b
gate, round 1, minor 3). If the encoding sends every source configuration at `entry` to a target
configuration at `entry'`, then every admissible source start `c` gives an admissible target start
`enc c`, at the index `(i, c)`. The condition is sufficient, not necessary: the transported
contract's admissible starts are the encodings of admissible source starts that lie at
`entry'`, so compatibility on the admissible source starts alone also suffices (the proof uses
`hentry` only at `c`; MIG-0b gate, round 2, minor 3). Without any compatibility the contract
may have no admissible start: with an identity encoding and `entry' ≠ entry` it has none. -/
theorem Contract.lockstep_admissible {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (entry' : S')
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j))
    (hentry : ∀ c : Cfg k Γ S x, c.state = some entry → (enc c).state = some entry')
    (i : ι) (c : Cfg k Γ S x) (hc : c.state = some entry) (hp : C.pre i c) :
    (enc c).state = some entry' ∧ (C.lockstep L entry' blo bhi hbox).pre (i, c) (enc c) :=
  ⟨hentry c hc, rfl, hc, hp⟩

/-- **Admissible starts for a state-renaming encoding**: when the encoding renames states by `ρ`
(as alphabet reduction's does), the renamed entry `ρ entry` is compatible, so every admissible
source start `c` gives the admissible target start `enc c`. -/
theorem Contract.lockstep_admissible_map {k' : ℕ} {Γ' S S' : Type} {x : List Γ} {x' : List Γ'}
    {M : MultiTapeTM k Γ S} {N : MultiTapeTM k' Γ' S'} {enc : Cfg k Γ S x → Cfg k' Γ' S' x'}
    {cost : Cfg k Γ S x → ℕ} {entry : S} {X : Set (Option S)} {X' : Set (Option S')} {ι : Type}
    (C : Contract M entry X ι x) (L : Lockstep M N enc cost X X') (ρ : S → S')
    (hρ : ∀ c, (enc c).state = c.state.map ρ)
    (blo bhi : Cfg k Γ S x → Fin k' → ℤ)
    (hbox : ∀ c v, (v = 0 ∨ (c.state ∉ X ∧ v ≤ cost c)) → ∀ j,
      (N.runFrom (enc c) v).workTapePos j ∈ Finset.Icc (blo c j) (bhi c j))
    (i : ι) (c : Cfg k Γ S x) (hc : c.state = some entry) (hp : C.pre i c) :
    (enc c).state = some (ρ entry) ∧
      (C.lockstep L (ρ entry) blo bhi hbox).pre (i, c) (enc c) :=
  C.lockstep_admissible L (ρ entry) blo bhi hbox
    (fun c hc => by rw [hρ, hc]; rfl) i c hc hp

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Contract/Reach.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reaching an endpoint within bounds

Many rows of the construction layer are stated existentially: from a configuration satisfying a
precondition, the machine reaches a stated endpoint at some time within a bound, with no exit
earlier and every head within a radius. `Turing.ReachesWithin` names that shape once, and
`Turing.Contract.ofReaches` turns a row in that shape into a `Turing.Contract`, choosing the time,
so that existential rows compose with `Turing.Contract.seq`, `inPhase` and `branch`.

## Main definitions

* `Turing.ReachesWithin`: the endpoint is reached within `B` steps, no state of `X` earlier, every
  head within `E` cells of its start.
* `Turing.Contract.ofReaches`: the contract of a row stated with `ReachesWithin`.

## Main results

* `Turing.reachesWithin_iff`, `Turing.ReachesWithin.mono`.
* `Turing.Contract.ofReaches_time_le`, and the field equations of `Contract.ofReaches`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the framing adapted as `Turing.Contract` (design adaptation; full entry in
  `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **Reaching an endpoint within bounds.** `ReachesWithin M d X B E post`: run from `d`, the
machine `M` is at `post` at some time `t ≤ B`; at every earlier time its state is not in `X`; and
at every time up to `t` each work head is within `E` cells of where it was in `d`. -/
def ReachesWithin {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (d : Cfg k Γ S x)
    (X : Set (Option S)) (B E : ℕ) (post : Cfg k Γ S x) : Prop :=
  ∃ t ≤ B, (∀ s < t, (M.runFrom d s).state ∉ X) ∧
    (∀ s ≤ t, ∀ j : Fin k, |(M.runFrom d s).workTapePos j - d.workTapePos j| ≤ (E : ℤ)) ∧
    M.runFrom d t = post

/-- `ReachesWithin`, as an equivalence with its definition. -/
theorem reachesWithin_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (d : Cfg k Γ S x)
    (X : Set (Option S)) (B E : ℕ) (post : Cfg k Γ S x) :
    ReachesWithin M d X B E post ↔
      ∃ t ≤ B, (∀ s < t, (M.runFrom d s).state ∉ X) ∧
        (∀ s ≤ t, ∀ j : Fin k, |(M.runFrom d s).workTapePos j - d.workTapePos j| ≤ (E : ℤ)) ∧
        M.runFrom d t = post :=
  Iff.rfl

/-- Larger bounds: an endpoint reached within `B` steps and radius `E` is reached within any
`B' ≥ B` and `E' ≥ E`. -/
theorem ReachesWithin.mono {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {d : Cfg k Γ S x}
    {X : Set (Option S)} {B E B' E' : ℕ} {post : Cfg k Γ S x}
    (h : ReachesWithin M d X B E post) (hB : B ≤ B') (hE : E ≤ E') :
    ReachesWithin M d X B' E' post := by
  obtain ⟨t, ht, hcut, henv, hrun⟩ := h
  exact ⟨t, ht.trans hB, hcut, fun s hs j => (henv s hs j).trans (by exact_mod_cast hE), hrun⟩

/-- **The contract of a row stated with `ReachesWithin`.** If from the entry, under `pre`, the
machine reaches `post` within `B` steps and radius `E`, with no state of `X` earlier, and the
endpoint's state lies in `X`, then this is the contract with that precondition and endpoint, the
exits `X`, the time chosen from the row (`0` off the precondition), and the head intervals
`[pos - E, pos + E]`.

**Proof sketch.** Under the precondition the time is the chosen witness, so the run, the cut and
the envelope are the row's clauses, the envelope read through `abs_le`; the exit is `hX`. -/
noncomputable def Contract.ofReaches {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {X : Set (Option S)} {ι : Type} {x : List Γ} (pre : ι → Cfg k Γ S x → Prop)
    (B E : ι → Cfg k Γ S x → ℕ) (post : ι → Cfg k Γ S x → Cfg k Γ S x)
    (h : ∀ i d, d.state = some entry → pre i d → ReachesWithin M d X (B i d) (E i d) (post i d))
    (hX : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ X) :
    Contract M entry X ι x where
  pre := pre
  time i d := haveI := Classical.propDecidable (d.state = some entry ∧ pre i d)
    if hd : d.state = some entry ∧ pre i d then Classical.choose (h i d hd.1 hd.2) else 0
  post := post
  lo i d j := d.workTapePos j - E i d
  hi i d j := d.workTapePos j + E i d
  run i d hd hp := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)]
    exact (Classical.choose_spec (h i d hd hp)).2.2.2
  exit_mem i d hd hp := hX i d hd hp
  cut i d hd hp u hu := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)] at hu
    exact (Classical.choose_spec (h i d hd hp)).2.1 u hu
  env i d hd hp u hu j := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)] at hu
    have := (Classical.choose_spec (h i d hd hp)).2.2.1 u hu j
    rw [abs_le] at this
    exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- The contract of a row stated with `ReachesWithin` takes at most the row's bound.

**Proof sketch.** Under the precondition the time is the chosen witness, which is at most `B`. -/
theorem Contract.ofReaches_time_le {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {X : Set (Option S)} {ι : Type} {x : List Γ} (pre : ι → Cfg k Γ S x → Prop)
    (B E : ι → Cfg k Γ S x → ℕ) (post : ι → Cfg k Γ S x → Cfg k Γ S x)
    (h : ∀ i d, d.state = some entry → pre i d → ReachesWithin M d X (B i d) (E i d) (post i d))
    (hX : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ X) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : pre i d) :
    (Contract.ofReaches pre B E post h hX).time i d ≤ B i d := by
  show (haveI := Classical.propDecidable (d.state = some entry ∧ pre i d)
    if hd : d.state = some entry ∧ pre i d then Classical.choose (h i d hd.1 hd.2) else 0) ≤ B i d
  simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)]
  exact (Classical.choose_spec (h i d hd hp)).1

attribute [simps (config := { isSimp := false }) pre post lo hi] Contract.ofReaches

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Seam

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: seams, the phase host and the release adapter

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`). The
MIG-0a compositions over `Build/Seam` (`seq`, `inPhase`, `branch` and `ReturnContract.release`)
moved here from `Build/Contract.lean` as landed on 2026-10-13, with no statement changed; with
MIG-0b's round release, the joint trajectories and frames of these compositions, and their
positivity.

**Routing.** `Turing.Contract.seq` is the single-live-exit seam, `Turing.Contract.branch` the
binary case, and the phase host (`Turing.Contract.inPhase`) handles an arbitrary set of live
exits, several of which may share one continuation. A first phase that halts cannot resume
through a seam, which dispatches only at a live anchor.

## Main definitions

* `Turing.Contract.seq`: sequencing through the R2 seam `Turing.seamCompTM`, after a first
  phase with a single live exit.
* `Turing.Contract.inPhase`: a phase run inside the phase host `Turing.phaseHostTM`, with an
  arbitrary set of live exits, each redirected; `Turing.Cfg.bindState`, its redirect.
* `Turing.Contract.branch`: the two-way seam `Turing.seamCompTM₂`, after a first phase with two
  live exits.
* `Turing.ReturnContract.release`, `Turing.RoundContract.release`: returning modules and rounds
  through the release adapter `Turing.seamReleaseTM`.

## Main results

* `Turing.Contract.Traj.seq`, `Turing.Contract.Traj.inPhase`, `Turing.Contract.Traj.branch`,
  `Turing.Contract.Frames.seq`: preservation of joint trajectories and frames.
* `Turing.Contract.seq_positive`, `Turing.Contract.inPhase_positive`,
  `Turing.Contract.branch_positive`, `Turing.ReturnContract.release_positive`,
  `Turing.RoundContract.release_positive`: positivity.
* `Turing.Contract.seq_pre`, `Turing.Contract.inPhase_time`, `Turing.Contract.branch_post`
  and the rest — the specification API (user, 2026-10-16): the composites' data fields as
  equations, without the `simp` attribute.
* `Turing.ReturnContract.release_pre`, `_time`, `_post`, `_lo`, `_hi` and
  `Turing.RoundContract.release_pre` … `_hi` — the release adapters' data fields as equations,
  the same way (the specification API's gate, finding 1).

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the specification-only calls adapted as `Turing.Contract` (design adaptation; full
  entry in `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

namespace Contract

section Compose

private lemma mapState_state {S S' : Type} {x : List Γ} (f : S → S') (c : Cfg k Γ S x) :
    (c.mapState f).state = c.state.map f := rfl

/-- The composed start is the left-mapped first-phase start. -/
private lemma mapState_const_inl {S₁ S₂ : Type} {x : List Γ} {e : S₁}
    {d : Cfg k Γ (S₁ ⊕ S₂) x} (hd : d.state = some (Sum.inl e)) :
    (d.mapState fun _ => e).mapState Sum.inl = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- The seam trajectory of a contract run: the left segment up to the first exit (live
throughout), and the right segment after the dispatch, at every offset. The composite starts
at `Sum.inl entry₁`; the first phase runs from that start with its state replaced by `entry₁`.

**Proof sketch.** Re-tagging the replaced start by `Sum.inl` gives back the composite start.
`C₁`'s cut is the strict exit cut of `Turing.seamCompTM_runFrom_left`, which gives the left
segment up to `t₁`. It is live: a halt before `t₁` would persist to the endpoint, which is at
`exit₁`. The right segment is `Turing.seamCompTM_run_ofCfg` with second-phase time `v` and that
run's endpoint taken to be itself. The replaced endpoint is at `entry₂` by construction. -/
private lemma seq_traj {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} (entry₂ : S₂) {ι : Type} {x : List Γ}
    (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (i : ι) (d : Cfg k Γ (S₁ ⊕ S₂) x)
    (hd : d.state = some (Sum.inl entry₁)) (hp : C₁.pre i (d.mapState fun _ => entry₁)) :
    (∀ u ≤ C₁.time i (d.mapState fun _ => entry₁),
      (seamCompTM M₁ exit₁ M₂ entry₂).runFrom d u =
          (M₁.runFrom (d.mapState fun _ => entry₁) u).mapState Sum.inl ∧
        (M₁.runFrom (d.mapState fun _ => entry₁) u).state ≠ none) ∧
    (∀ v, (seamCompTM M₁ exit₁ M₂ entry₂).runFrom d
        (C₁.time i (d.mapState fun _ => entry₁) + 1 + v) =
      (M₂.runFrom ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)
        v).mapState Sum.inr) ∧
    ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂).state =
      some entry₂ := by
  have hd' := mapState_const_inl (S₂ := S₂) hd
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  have h1 := C₁.run i _ hd₁ hp
  have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i _ hd₁ hp)
  have hcut : ∀ t < C₁.time i (d.mapState fun _ => entry₁),
      (M₁.runFrom (d.mapState fun _ => entry₁) t).state ≠ some exit₁ :=
    fun t ht => C₁.cut i _ hd₁ hp t ht
  refine ⟨fun u hu => ⟨?_, ?_⟩, fun v => ?_, by rw [mapState_state, hx]; rfl⟩
  · have hl := seamCompTM_runFrom_left M₁ exit₁ M₂ entry₂ hcut u hu
    rwa [hd'] at hl
  · refine MultiTapeTM.runFrom_state_ne_none_of_le M₁ _ _ ?_ u hu
    rw [h1, hx]
    exact Option.some_ne_none _
  · have hr := seamCompTM_run_ofCfg M₁ exit₁ M₂ entry₂ h1 hx hcut (T₂ := v) rfl
    rwa [hd'] at hr

/-- **Sequencing through the R2 seam** (`Turing.seamCompTM_run_ofCfg`,
`Turing.seamCompTM_firstReturn_ofCfg`): run `C₁` to its single live exit `exit₁`, take one
stationary dispatch step, and run `C₂`, so the time is `t₁ + 1 + t₂`. The second phase starts
from the first's endpoint with its state replaced by `entry₂`; the endpoint and the exits are
right-tagged, and the envelopes take the hull.

This is the **single-live-exit seam**. Two live exits go through `Turing.Contract.branch`, and
an arbitrary set of live exits through the phase host (`Turing.Contract.inPhase`). A first phase
that halts cannot resume through a seam, which dispatches only at a live anchor.

**Proof sketch.** By the seam trajectory (`seq_traj`): up to `t₁` the composite is the
left-tagged first phase, live throughout, and at `t₁ + 1 + v` it is the right-tagged second
phase at `v`, from its entry. The run is `Turing.seamCompTM_run_ofCfg` with `C₂`'s run, and the
exit is `C₂`'s, right-tagged. For the cut, a time up to `t₁` carries a live left-tagged state,
which is no right-tagged exit; a later time is `t₁ + 1 + v` with `v < t₂`, and injectivity of the
right tag reduces it to `C₂`'s cut at `v`. The envelope is `C₁`'s up to `t₁` and `C₂`'s after
the dispatch (offset `0` is the dispatch step), inside the hull. -/
def seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)} {ι κ : Type} {x : List Γ}
    (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (C₂ : Contract M₂ entry₂ X₂ κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)) :
    Contract (seamCompTM M₁ exit₁ M₂ entry₂) (Sum.inl entry₁) (Option.map Sum.inr '' X₂) ι x where
  pre i d := C₁.pre i (d.mapState fun _ => entry₁)
  time i d := C₁.time i (d.mapState fun _ => entry₁) + 1 +
    C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)
  post i d :=
    (C₂.post (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)).mapState
      Sum.inr
  lo i d j := min (C₁.lo i (d.mapState fun _ => entry₁) j)
    (C₂.lo (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j)
  hi i d j := max (C₁.hi i (d.mapState fun _ => entry₁) j)
    (C₂.hi (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j)
  run i d hd hp := by
    have hd' := mapState_const_inl (S₂ := S₂) hd
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i _ hd₁ hp)
    have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
    have hr := seamCompTM_run_ofCfg M₁ exit₁ M₂ entry₂ (C₁.run i _ hd₁ hp) hx
      (fun t ht => C₁.cut i _ hd₁ hp t ht) (C₂.run _ _ hd₂ (hlink i _ hd₁ hp))
    rw [hd'] at hr
    exact hr
  exit_mem i d hd hp := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
    exact ⟨_, C₂.exit_mem _ _ hd₂ (hlink i _ hd₁ hp), rfl⟩
  cut i d hd hp u hu := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
    change u < C₁.time i (d.mapState fun _ => entry₁) + 1 +
      C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
    rintro ⟨q, hq, heq⟩
    by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
    · obtain ⟨hrun, hlive⟩ := hL u hle
      rw [hrun] at heq
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
      rw [mapState_state, hs] at heq
      cases q <;> simp at heq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
        ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
      rw [hR v] at heq
      have hq' : q = (M₂.runFrom ((C₁.post i (d.mapState fun _ => entry₁)).mapState
          fun _ => entry₂) v).state := Option.map_injective Sum.inr_injective heq
      exact C₂.cut _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) (hq' ▸ hq)
  env i d hd hp u hu j := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
    change u ≤ C₁.time i (d.mapState fun _ => entry₁) + 1 +
      C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
    by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
    · rw [(hL u hle).1]
      exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₁.env i _ hd₁ hp u hle j)
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
        ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
      rw [hR v]
      exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
        (C₂.env _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) j)

/-- Re-type a configuration's control state through a partial map: the phase host's redirect.
A halted configuration stays halted; every other field is kept. -/
def _root_.Turing.Cfg.bindState {S S' : Type} {x : List Γ} (d : Cfg k Γ S x) (f : S → Option S') :
    Cfg k Γ S' x :=
  ⟨d.state.bind f, d.inputPos, d.workTapes, d.workTapePos, d.output⟩

/-! The redirect's fields as equations, generated without the `simp` attribute (`policy.md` §1):
the state is `d.state.bind f`, and the input position, tapes, heads and output are `d`'s. -/
attribute [simps (config := { isSimp := false })] Turing.Cfg.bindState

/-- The phase-host trajectory of a contract run: the tagged prefix through the phase's exit,
the redirected endpoint one dispatch step later, and the live exit state.

**Proof sketch.** The endpoint's state lies in `X`, which excludes `none`, so it is a live exit
`s'`, which `red p` redirects (`hsome`). Before the endpoint the cut keeps every state out of
`X`, so `hred` says that none of them is redirected. `Turing.phaseHostTM_run` then gives the
prefix tagged with `p` up to the time and, one dispatch step later, the endpoint with its state
replaced by the target of `s'`, which is the endpoint's state bound through `red p`. The
other-phase clause of `hsome` is not used here. -/
private lemma inPhase_traj {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x)
    (hnone : none ∉ X) (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p)
    (i : ι) (d : Cfg k Γ (Σ i, Ph i) x) (hd : d.state = some ⟨p, s₀⟩)
    (hp : C.pre i (d.mapState fun _ => s₀)) :
    (∀ u ≤ C.time i (d.mapState fun _ => s₀),
      (phaseHostTM Mf q0 red).runFrom d u =
        ((Mf p).runFrom (d.mapState fun _ => s₀) u).mapState (Sigma.mk p)) ∧
    (phaseHostTM Mf q0 red).runFrom d (C.time i (d.mapState fun _ => s₀) + 1) =
      (C.post i (d.mapState fun _ => s₀)).bindState (red p) ∧
    ∃ s', (C.post i (d.mapState fun _ => s₀)).state = some s' ∧ some s' ∈ X := by
  have hd' : (d.mapState fun _ => s₀).mapState (Sigma.mk p) = d :=
    Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl
  have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
  have hx := C.exit_mem i _ hc hp
  obtain ⟨s', hs'⟩ : ∃ s', (C.post i (d.mapState fun _ => s₀)).state = some s' := by
    cases h : (C.post i (d.mapState fun _ => s₀)).state with
    | none => rw [h] at hx; exact absurd hx hnone
    | some s' => exact ⟨s', rfl⟩
  have hs'X : some s' ∈ X := by rw [← hs']; exact hx
  obtain ⟨q', hq', -⟩ := hsome s' hs'X
  have H := phaseHostTM_run Mf q0 red p (d.mapState fun _ => s₀) _ _ (C.run i _ hc hp) s' hs'
    q' hq' (fun u hu s hs => hred s (fun hm => C.cut i _ hc hp u hu (by rw [hs]; exact hm)))
  rw [hd'] at H
  refine ⟨H.1, ?_, s', hs', hs'X⟩
  rw [H.2]
  refine Cfg.ext ?_ rfl rfl rfl rfl
  show Option.map (fun _ => q') (C.post i (d.mapState fun _ => s₀)).state =
    (C.post i (d.mapState fun _ => s₀)).state.bind (red p)
  rw [hs']
  simp [hq']

/-- **A phase inside the phase host** (`Turing.phaseHostTM_run`). Phase `p` runs under its own
contract, whose exits are live (`hnone`) and are exactly the states of phase `p` that the host
redirects (`hred`, `hsome`), each to a state of another phase. The host's exits are the
redirect targets, the time gains one dispatch step, and the envelopes are the phase's. The
phase host thus handles an **arbitrary set of live exits**, each sent to its own target, and
several may share one continuation; `Turing.Contract.seq` and `Turing.Contract.branch` are the
one- and two-exit seams.

The other-phase condition `q.1 ≠ p` is **sufficient, not necessary**. What the cut needs is that
the run avoids every redirect target up to its endpoint; up to there the host run is tagged with
phase `p`, so it never meets a state of another phase. A same-phase target that the run avoids
up to its endpoint would also do, while a redirect back to the entry fails at time `0`; a
generalization could ask for that avoidance instead.

**Proof sketch.** By the phase-host trajectory (`inPhase_traj`): up to the phase's time the
host is the phase run tagged with `p`, and one dispatch step later it is the phase's endpoint
with its state bound through `red p`. This gives the run, and the exit is the target of the
phase's live exit. For the cut, a time up to the phase's time carries a state tagged with `p`,
or `none`; a target equal to it would lie in phase `p`, against `q.1 ≠ p`. The envelope is the
phase's up to its time; at the dispatch step the heads are those of the phase's endpoint. -/
def inPhase {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p} {X : Set (Option (Ph p))}
    {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x) (hnone : none ∉ X)
    (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p) :
    Contract (phaseHostTM Mf q0 red) ⟨p, s₀⟩ {q | ∃ s, some s ∈ X ∧ q = red p s} ι x where
  pre i d := C.pre i (d.mapState fun _ => s₀)
  time i d := C.time i (d.mapState fun _ => s₀) + 1
  post i d := (C.post i (d.mapState fun _ => s₀)).bindState (red p)
  lo i d := C.lo i (d.mapState fun _ => s₀)
  hi i d := C.hi i (d.mapState fun _ => s₀)
  run i d hd hp := (inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp).2.1
  exit_mem i d hd hp := by
    obtain ⟨-, -, s', hs', hs'X⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    refine ⟨s', hs'X, ?_⟩
    show (C.post i (d.mapState fun _ => s₀)).state.bind (red p) = red p s'
    rw [hs']
    rfl
  cut i d hd hp u hu := by
    change u < C.time i (d.mapState fun _ => s₀) + 1 at hu
    obtain ⟨hL, -, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    rw [hL u (by omega)]
    rintro ⟨s, hsX, heq⟩
    obtain ⟨q, hq, hqp⟩ := hsome s hsX
    rw [hq, mapState_state] at heq
    obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp heq
    exact hqp (by rw [← ha])
  env i d hd hp u hu j := by
    change u ≤ C.time i (d.mapState fun _ => s₀) + 1 at hu
    have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hE, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    rcases Nat.lt_or_ge u (C.time i (d.mapState fun _ => s₀) + 1) with h | h
    · rw [hL u (by omega)]
      exact C.env i _ hc hp u (by omega) j
    · obtain rfl : u = C.time i (d.mapState fun _ => s₀) + 1 := by omega
      rw [hE]
      have h' := C.env i _ hc hp _ le_rfl j
      rw [C.run i _ hc hp] at h'
      exact h'

end Compose

/-! ## The two-way branch -/

/-- The two-way composed start is the doubly left-mapped first-phase start. -/
private lemma mapState_const_inl_inl {S₀ S₁ S₂ : Type} {x : List Γ} {e : S₀}
    {d : Cfg k Γ ((S₀ ⊕ S₁) ⊕ S₂) x} (hd : d.state = some (Sum.inl (Sum.inl e))) :
    ((d.mapState fun _ => e).mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState
      (Sum.inl : S₀ ⊕ S₁ → (S₀ ⊕ S₁) ⊕ S₂) = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- The two-way seam trajectory of a contract run: the doubly left-mapped first phase up to
its exit (live throughout), then, per exit, the matching continuation at every offset.

**Proof sketch.** The two-way seam nests two seams: the inner one dispatches `e₁` to the first
continuation, and the outer one dispatches the inner machine's `Sum.inl e₂` to the second.
`C₀`'s cut excludes both exits before its time. By the inner seam's left segment
(`Turing.seamCompTM_runFrom_left`), the inner machine therefore avoids `Sum.inl e₂` before that
time, so the outer seam's left segment, rewritten by the inner one, is the doubly tagged first
phase up to its time. It is live, since a halt would persist to the endpoint, which is at an
exit. The two continuations are the two halves of `Turing.seamCompTM₂_run_ofCfg`. -/
private lemma branch_traj {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} (M₁ : MultiTapeTM k Γ S₁) (M₂ : MultiTapeTM k Γ S₂)
    {entry₀ e₁ e₂ : S₀} (entry₁ : S₁) (entry₂ : S₂) {ι : Type} {x : List Γ} (he : e₁ ≠ e₂)
    (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x) (i : ι)
    (d : Cfg k Γ ((S₀ ⊕ S₁) ⊕ S₂) x) (hd : d.state = some (Sum.inl (Sum.inl entry₀)))
    (hp : C₀.pre i (d.mapState fun _ => entry₀)) :
    (∀ u ≤ C₀.time i (d.mapState fun _ => entry₀),
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d u =
          ((M₀.runFrom (d.mapState fun _ => entry₀) u).mapState Sum.inl).mapState Sum.inl ∧
        (M₀.runFrom (d.mapState fun _ => entry₀) u).state ≠ none) ∧
    ((C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ → ∀ v,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d
          (C₀.time i (d.mapState fun _ => entry₀) + 1 + v) =
        ((M₁.runFrom ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)
          v).mapState Sum.inr).mapState Sum.inl) ∧
    ((C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ → ∀ v,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d
          (C₀.time i (d.mapState fun _ => entry₀) + 1 + v) =
        (M₂.runFrom ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)
          v).mapState Sum.inr) := by
  have hd' := mapState_const_inl_inl (S₁ := S₁) (S₂ := S₂) hd
  have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
  have h0 := C₀.run i _ hc hp
  have hx := C₀.exit_mem i _ hc hp
  have hcut₁ : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      (M₀.runFrom (d.mapState fun _ => entry₀) t).state ≠ some e₁ :=
    fun t ht h => C₀.cut i _ hc hp t ht (by rw [h]; exact Set.mem_insert _ _)
  have hcut₂ : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      (M₀.runFrom (d.mapState fun _ => entry₀) t).state ≠ some e₂ :=
    fun t ht h => C₀.cut i _ hc hp t ht (by rw [h]; exact Set.mem_insert_of_mem _ rfl)
  have hcutO : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      ((seamCompTM M₀ e₁ M₁ entry₁).runFrom ((d.mapState fun _ => entry₀).mapState Sum.inl)
        t).state ≠ some (Sum.inl e₂) := by
    intro t ht h
    rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ t ht.le] at h
    exact hcut₂ t ht (by simpa [Cfg.mapState] using h)
  have H := seamCompTM₂_run_ofCfg M₀ e₁ e₂ he M₁ entry₁ M₂ entry₂ h0
    (fun t ht => ⟨hcut₁ t ht, hcut₂ t ht⟩)
  rw [hd'] at H
  refine ⟨fun u hu => ⟨?_, ?_⟩, H.1, H.2⟩
  · have h := seamCompTM_runFrom_left (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂
      hcutO u hu
    rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ u hu, hd'] at h
    exact h
  · refine MultiTapeTM.runFrom_state_ne_none_of_le M₀ _ _ ?_ u hu
    rw [h0]
    intro h'
    rw [h'] at hx
    simp at hx

/-- **The two-way branch** (`Turing.seamCompTM₂_run_ofCfg`): the first phase ends at one of two
distinct live exits, and the seam dispatches, in one step, to the matching continuation, which
starts from the first phase's endpoint with its state replaced by its entry. Each
continuation's precondition is needed only when its exit is the one reached. The time, the
endpoint and the continuation part of the envelope hull are the selected continuation's.

This is the **binary case** of the routing: `Turing.Contract.seq` is the single-live-exit seam,
and the phase host (`Turing.Contract.inPhase`) handles an arbitrary set of live exits. Halted
endpoints of the two continuations share the untagged `none`, so a consumer that must recover
the branch from the final state needs live tagged exits or an explicit verdict.

**Proof sketch.** By the two-way trajectory (`branch_traj`), and by cases on the exit reached
(`e₁`, or else `e₂` by `exit_mem`). Up to the first phase's time the composite is the doubly
left-tagged first phase, live throughout, so it meets no exit of either continuation. At time
`t₀ + 1 + v` it is the selected continuation's run at `v`, tagged, which gives the run, the exit
and the envelope. For the cut at `v` below the continuation's time, a tagged exit of the
selected continuation is excluded by that continuation's cut, through injectivity of the tags;
an exit of the other continuation carries the other tag or is `none`, and the state is live by
`Turing.Contract.live`. -/
def branch {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁] {M₀ : MultiTapeTM k Γ S₀}
    {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂} {entry₀ e₁ e₂ : S₀} {entry₁ : S₁}
    {entry₂ : S₂} {X₁ : Set (Option S₁)} {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ}
    (he : e₁ ≠ e₂) (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x)
    (C₁ : Contract M₁ entry₁ X₁ κ₁ x) (C₂ : Contract M₂ entry₂ X₂ κ₂ x) (l₁ : ι → κ₁)
    (l₂ : ι → κ₂)
    (h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁))
    (h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)) :
    Contract (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂) (Sum.inl (Sum.inl entry₀))
      ((Option.map (Sum.inl ∘ Sum.inr) '' X₁) ∪ (Option.map Sum.inr '' X₂)) ι x where
  pre i d := C₀.pre i (d.mapState fun _ => entry₀)
  time i d :=
    C₀.time i (d.mapState fun _ => entry₀) + 1 +
      if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
        C₁.time (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)
      else C₂.time (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)
  post i d :=
    if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      ((C₁.post (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)).mapState
        Sum.inr).mapState Sum.inl
    else
      (C₂.post (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)).mapState
        Sum.inr
  lo i d j := min (C₀.lo i (d.mapState fun _ => entry₀) j)
    (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      C₁.lo (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) j
    else C₂.lo (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) j)
  hi i d j := max (C₀.hi i (d.mapState fun _ => entry₀) j)
    (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      C₁.hi (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) j
    else C₂.hi (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) j)
  run i d hd hp := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨-, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      rw [if_pos h, if_pos h, H₁ h, C₁.run _ _ hd₁ (h₁ i _ hc hp h)]
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      rw [if_neg h, if_neg h, H₂ h', C₂.run _ _ hd₂ (h₂ i _ hc hp h')]
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      rw [if_pos h]
      refine Or.inl ⟨_, C₁.exit_mem _ _ hd₁ (h₁ i _ hc hp h), ?_⟩
      rw [mapState_state, mapState_state, Option.map_map]
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      rw [if_neg h]
      exact Or.inr ⟨_, C₂.exit_mem _ _ hd₂ (h₂ i _ hc hp h'), rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
    · obtain ⟨hrun, hlive⟩ := HL u hle
      rw [hrun]
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
      rintro (⟨q, -, heq⟩ | ⟨q, -, heq⟩) <;>
        rw [mapState_state, mapState_state, hs] at heq <;> cases q <;> simp at heq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
        ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
      by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
      · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
            some entry₁ := by rw [mapState_state, h]; rfl
        rw [if_pos h] at hu
        have hv : v < C₁.time (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState
            fun _ => entry₁) := by omega
        have hcut := C₁.cut _ _ hd₁ (h₁ i _ hc hp h) v hv
        have hlive := live C₁ _ _ hd₁ (h₁ i _ hc hp h) hv
        rw [H₁ h v]
        rintro (⟨q, hq, heq⟩ | ⟨q, -, heq⟩)
        · rw [mapState_state, mapState_state, Option.map_map] at heq
          exact hcut (Option.map_injective (Sum.inl_injective.comp Sum.inr_injective) heq ▸ hq)
        · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
          rw [mapState_state, mapState_state, hs] at heq
          cases q <;> simp at heq
      · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
          rcases C₀.exit_mem i _ hc hp with h'' | h''
          · exact absurd h'' h
          · exact h''
        have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
            some entry₂ := by rw [mapState_state, h']; rfl
        rw [if_neg h] at hu
        have hv : v < C₂.time (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState
            fun _ => entry₂) := by omega
        have hcut := C₂.cut _ _ hd₂ (h₂ i _ hc hp h') v hv
        have hlive := live C₂ _ _ hd₂ (h₂ i _ hc hp h') hv
        rw [H₂ h' v]
        rintro (⟨q, -, heq⟩ | ⟨q, hq, heq⟩)
        · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
          rw [mapState_state, hs] at heq
          cases q <;> simp at heq
        · rw [mapState_state] at heq
          exact hcut (Option.map_injective Sum.inr_injective heq ▸ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
    · rw [(HL u hle).1]
      exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₀.env i _ hc hp u hle j)
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
        ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
      by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
      · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
            some entry₁ := by rw [mapState_state, h]; rfl
        rw [if_pos h] at hu
        rw [if_pos h, if_pos h, H₁ h v]
        exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
          (C₁.env _ _ hd₁ (h₁ i _ hc hp h) v (by omega) j)
      · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
          rcases C₀.exit_mem i _ hc hp with h'' | h''
          · exact absurd h'' h
          · exact h''
        have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
            some entry₂ := by rw [mapState_state, h']; rfl
        rw [if_neg h] at hu
        rw [if_neg h, if_neg h, H₂ h' v]
        exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
          (C₂.env _ _ hd₂ (h₂ i _ hc hp h') v (by omega) j)

/-! ### The specification API (user, 2026-10-16)

The data fields of the seam, phase and branch composites as equations, generated by `simps`
without the `simp` attribute, so that consumers never unfold the definitions. -/

attribute [simps (config := { isSimp := false }) pre time post lo hi] seq inPhase branch

end Contract

/-! ## The release adapter -/

/-- The release start is the anchor-mapped start, re-tagged fresh. -/
private lemma release_start {S : Type} {anchor : S} {x : List Γ} {d : Cfg k Γ (Unit ⊕ S) x}
    (hd : d.state = some (Sum.inl ())) :
    (d.mapState fun _ => anchor).mapState (fun _ => (Sum.inl () : Unit ⊕ S)) = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- **The release adapter** (`Turing.seamReleaseTM_firstReturn`): a fresh start state executes the
anchor's first step, so the returning run becomes an ordinary contract whose cut includes time
`0`, at the same time and with no dispatch step. Its single exit is the right-tagged anchor, and
the envelopes are unchanged.

**Proof sketch.** The release start is the anchor-mapped start re-tagged fresh
(`release_start`). Fed the returning contract's positivity, run, return and positive cut,
`Turing.seamReleaseTM_firstReturn` gives the run to the right-tagged endpoint at the same time,
and the cut against the right-tagged anchor at every earlier time, time `0` included since the
fresh state is left-tagged. The exit is the endpoint's state, the anchor, right-tagged. For the
envelope, the head vector at time `0` is the start's; at a positive time the release run is
the source run, right-tagged (`Turing.seamReleaseTM_runFrom_pos`), so its heads are the
source's, inside the source envelope. -/
def ReturnContract.release {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {ι : Type}
    {x : List Γ} (C : ReturnContract M anchor ι x) :
    Contract (seamReleaseTM M anchor) (Sum.inl ()) {some (Sum.inr anchor)} ι x where
  pre i d := C.pre i (d.mapState fun _ => anchor)
  time i d := C.time i (d.mapState fun _ => anchor)
  post i d := (C.post i (d.mapState fun _ => anchor)).mapState Sum.inr
  lo i d := C.lo i (d.mapState fun _ => anchor)
  hi i d := C.hi i (d.mapState fun _ => anchor)
  run i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_firstReturn M anchor hc (C.pos i _ hc hp) (C.run i _ hc hp)
      (C.exit_eq i _ hc hp) (C.cut i _ hc hp)
    rw [release_start hd] at H
    exact H.1
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    show Option.map Sum.inr (C.post i (d.mapState fun _ => anchor)).state ∈ _
    rw [C.exit_eq i _ hc hp]
    rfl
  cut i d hd hp u hu hmem := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_firstReturn M anchor hc (C.pos i _ hc hp) (C.run i _ hc hp)
      (C.exit_eq i _ hc hp) (C.cut i _ hc hp)
    rw [release_start hd] at H
    exact H.2 u hu (Set.mem_singleton_iff.mp hmem)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · have h0 := C.env i _ hc hp 0 (Nat.zero_le _) j
      rw [MultiTapeTM.runFrom_zero] at h0 ⊢
      exact h0
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H]
      exact C.env i _ hc hp u hu j

/-- **The round release** (design §16a item 2, with item 5's export): a fresh start state
executes the anchor's first step, so a round becomes an ordinary contract whose exits are the
right-tagged images of the anchor and of the escape set, at the same time and with the same
envelope. The escape set is arbitrary: it may contain `none` (a round that halts still ends
halted, since the tag keeps `none`), several states, or the anchor itself. **Only for a single
live escape distinct from the anchor**, `escape = {some e}` with `e ≠ anchor`, are the exits two
distinct live states, `some (Sum.inr anchor)` and `some (Sum.inr e)`, the shape of
`Turing.Contract.branch`'s first phase. Routing through the phase host
(`Turing.Contract.inPhase`) needs in general that `none` is not an exit and the redirect
conditions.

**Proof sketch.** At every positive time the release run is the round run, right-tagged
(`Turing.seamReleaseTM_runFrom_pos`), and the release start re-tags the anchor-mapped start. The
run and the exit are the round's, tagged. The cut at time `0` holds since the fresh state is
left-tagged; at a positive time a tagged exit would be an anchor or escape state of the round
before its end, which its cut excludes. The heads are the round's at every time. -/
def RoundContract.release {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {escape : Set (Option S)} {ι : Type} {x : List Γ} (R : RoundContract M anchor escape ι x) :
    Contract (seamReleaseTM M anchor) (Sum.inl ())
      (Option.map Sum.inr '' insert (some anchor) escape) ι x where
  pre i d := R.pre i (d.mapState fun _ => anchor)
  time i d := R.time i (d.mapState fun _ => anchor)
  post i d := (R.post i (d.mapState fun _ => anchor)).mapState Sum.inr
  lo i d := R.lo i (d.mapState fun _ => anchor)
  hi i d := R.hi i (d.mapState fun _ => anchor)
  run i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_runFrom_pos M anchor _ hc _ (R.pos i _ hc hp)
    rw [release_start hd, R.run i _ hc hp] at H
    exact H
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    exact ⟨_, R.exit_mem i _ hc hp, rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rintro ⟨q, hq, heq⟩
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · rw [MultiTapeTM.runFrom_zero, hd] at heq
      cases q <;> simp at heq
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H] at heq
      have hq' : q = (M.runFrom (d.mapState fun _ => anchor) u).state :=
        Option.map_injective Sum.inr_injective heq
      exact R.cut i _ hc hp u hpos hu (hq' ▸ Set.mem_insert_of_mem _ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · have h0 := R.env i _ hc hp 0 (Nat.zero_le _) j
      rw [MultiTapeTM.runFrom_zero] at h0 ⊢
      exact h0
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H]
      exact R.env i _ hc hp u hu j

/-! The specification API (user, 2026-10-16; its gate, finding 1): the two release adapters'
data fields as equations, generated by `simps` without the `simp` attribute, so that consumers
never unfold the definitions. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi]
  ReturnContract.release RoundContract.release

/-! ## Joint trajectories, frames and positivity of the seam compositions (MIG-0b) -/

namespace Contract

/-- **`seq` preserves joint trajectories**: the first relation through the first phase, and the
second from the dispatch on (the dispatch step is stationary, so it is the second phase's time
`0`).

**Proof sketch.** By the seam trajectory (`seq_traj`), split at the first phase's time, as in
`Turing.Contract.seq`'s envelope. -/
theorem Traj.seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} {C₁ : Contract M₁ entry₁ {some exit₁} ι x}
    {C₂ : Contract M₂ entry₂ X₂ κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)}
    {R₁ : ι → Cfg k Γ S₁ x → (Fin k → ℤ) → Prop} {R₂ : κ → Cfg k Γ S₂ x → (Fin k → ℤ) → Prop}
    (h₁ : C₁.Traj R₁) (h₂ : C₂.Traj R₂) :
    (C₁.seq C₂ link hlink).Traj fun i d p => R₁ i (d.mapState fun _ => entry₁) p ∨
      R₂ (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) p := by
  intro i d hd hp u hu
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
  change u ≤ C₁.time i (d.mapState fun _ => entry₁) + 1 +
    C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
  by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
  · rw [(hL u hle).1]
    exact Or.inl (h₁ i _ hd₁ hp u hle)
  · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
      ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
    rw [hR v]
    exact Or.inr (h₂ _ _ hd₂ (hlink i _ hd₁ hp) v (by omega))

/-- **`seq` preserves frames**: the first footprint at the first-phase start and the second at
the second-phase start. Frames ignore control states, so the seam's tags do not matter.

**Proof sketch.** The first phase frames the start against its endpoint, and the second its
start, the state-replaced first endpoint, against the second endpoint; compose
(`Turing.Cfg.SameOutside.trans`) and re-tag (`Turing.Cfg.SameOutside.mapState`). -/
theorem Frames.seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} {C₁ : Contract M₁ entry₁ {some exit₁} ι x}
    {C₂ : Contract M₂ entry₂ X₂ κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)}
    {fp₁ : ι → Cfg k Γ S₁ x → Fin k → Set ℤ} {fp₂ : κ → Cfg k Γ S₂ x → Fin k → Set ℤ}
    (h₁ : C₁.Frames fp₁) (h₂ : C₂.Frames fp₂) :
    (C₁.seq C₂ link hlink).Frames fun i d j => fp₁ i (d.mapState fun _ => entry₁) j ∪
      fp₂ (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j := by
  intro i d hd hp
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
  have f₁ : Cfg.SameOutside (fp₁ i (d.mapState fun _ => entry₁)) d
      (C₁.post i (d.mapState fun _ => entry₁)) := h₁ i _ hd₁ hp
  have f₂ := h₂ _ _ hd₂ (hlink i _ hd₁ hp)
  exact (f₁.trans fun j q hq => f₂ j q hq).mapState Sum.inr

/-- **`inPhase` preserves joint trajectories**: the phase's relation, at the state-replaced start.
The dispatch step is stationary.

**Proof sketch.** By the phase-host trajectory (`inPhase_traj`), as in
`Turing.Contract.inPhase`'s envelope: up to the phase's time the host heads are the phase's, and
at the dispatch they are the phase endpoint's. -/
theorem Traj.inPhase {I : Type} {Ph : I → Type} {Mf : (i : I) → MultiTapeTM k Γ (Ph i)}
    {q0 : Σ i, Ph i} {red : (i : I) → Ph i → Option (Σ i, Ph i)} {p : I} {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} {C : Contract (Mf p) s₀ X ι x}
    {hnone : none ∉ X} {hred : ∀ s, some s ∉ X → red p s = none}
    {hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p}
    {R : ι → Cfg k Γ (Ph p) x → (Fin k → ℤ) → Prop} (h : C.Traj R) :
    (Contract.inPhase Mf q0 red p C hnone hred hsome).Traj
      fun i d => R i (d.mapState fun _ => s₀) := by
  intro i d hd hp u hu
  change u ≤ C.time i (d.mapState fun _ => s₀) + 1 at hu
  have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
  obtain ⟨hL, hE, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
  rcases Nat.lt_or_ge u (C.time i (d.mapState fun _ => s₀) + 1) with h' | h'
  · rw [hL u (by omega)]
    exact h i _ hc hp u (by omega)
  · obtain rfl : u = C.time i (d.mapState fun _ => s₀) + 1 := by omega
    rw [hE]
    have h'' := h i _ hc hp _ le_rfl
    rw [C.run i _ hc hp] at h''
    exact h''

/-- **`branch` preserves joint trajectories**: the first phase's relation up to its time, then
the relation of the continuation that its exit selects.

**Proof sketch.** By the two-way trajectory (`branch_traj`) and by cases on the exit reached, as
in `Turing.Contract.branch`'s envelope. -/
theorem Traj.branch {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₀ e₁ e₂ : S₀} {entry₁ : S₁} {entry₂ : S₂} {X₁ : Set (Option S₁)}
    {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ} {he : e₁ ≠ e₂}
    {C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x} {C₁ : Contract M₁ entry₁ X₁ κ₁ x}
    {C₂ : Contract M₂ entry₂ X₂ κ₂ x} {l₁ : ι → κ₁} {l₂ : ι → κ₂}
    {h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁)}
    {h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)}
    {R₀ : ι → Cfg k Γ S₀ x → (Fin k → ℤ) → Prop} {R₁ : κ₁ → Cfg k Γ S₁ x → (Fin k → ℤ) → Prop}
    {R₂ : κ₂ → Cfg k Γ S₂ x → (Fin k → ℤ) → Prop}
    (t₀ : C₀.Traj R₀) (t₁ : C₁.Traj R₁) (t₂ : C₂.Traj R₂) :
    (Contract.branch he C₀ C₁ C₂ l₁ l₂ h₁ h₂).Traj fun i d p =>
      R₀ i (d.mapState fun _ => entry₀) p ∨
        (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
          R₁ (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) p
        else
          R₂ (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) p) := by
  intro i d hd hp u hu
  have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
  obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
  by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
  · rw [(HL u hle).1]
    exact Or.inl (t₀ i _ hc hp u hle)
  · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
      ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
    right
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      change _ ≤ _ + 1 + (if _ then _ else _) at hu
      rw [if_pos h] at hu
      rw [if_pos h, H₁ h v]
      exact t₁ _ _ hd₁ (h₁ i _ hc hp h) v (by omega)
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      change _ ≤ _ + 1 + (if _ then _ else _) at hu
      rw [if_neg h] at hu
      rw [if_neg h, H₂ h' v]
      exact t₂ _ _ hd₂ (h₂ i _ hc hp h') v (by omega)

/-- `seq` is positive: it takes a dispatch step. -/
theorem seq_positive {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} (C₁ : Contract M₁ entry₁ {some exit₁} ι x)
    (C₂ : Contract M₂ entry₂ X₂ κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)) :
    (C₁.seq C₂ link hlink).Positive :=
  fun _ _ _ _ => Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)

/-- `inPhase` is positive: it takes a dispatch step. -/
theorem inPhase_positive {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x)
    (hnone : none ∉ X) (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p) :
    (Contract.inPhase Mf q0 red p C hnone hred hsome).Positive :=
  fun _ _ _ _ => Nat.succ_pos _

/-- `branch` is positive: it takes a dispatch step. -/
theorem branch_positive {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₀ e₁ e₂ : S₀} {entry₁ : S₁} {entry₂ : S₂} {X₁ : Set (Option S₁)}
    {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ} (he : e₁ ≠ e₂)
    (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x) (C₁ : Contract M₁ entry₁ X₁ κ₁ x)
    (C₂ : Contract M₂ entry₂ X₂ κ₂ x) (l₁ : ι → κ₁) (l₂ : ι → κ₂)
    (h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁))
    (h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)) :
    (Contract.branch he C₀ C₁ C₂ l₁ l₂ h₁ h₂).Positive :=
  fun _ _ _ _ => Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)

end Contract

/-- The release of a returning contract is positive, since a return takes positive time. -/
theorem ReturnContract.release_positive {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {ι : Type} {x : List Γ} (C : ReturnContract M anchor ι x) : C.release.Positive :=
  fun i d hd hp => C.pos i _ (by simp [Cfg.mapState, hd]) hp

/-- The release of a round contract is positive, since a round takes positive time. -/
theorem RoundContract.release_positive {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {escape : Set (Option S)} {ι : Type} {x : List Γ} (R : RoundContract M anchor escape ι x) :
    R.release.Positive :=
  fun i d hd hp => R.pos i _ (by simp [Cfg.mapState, hd]) hp

end Turing
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/Phases.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTable
import TCSlib.Complexity.RAMSimulation.Sim.PhaseRegister
import TCSlib.Complexity.RAMSimulation.Sim.PhaseMemoryMachines
import TCSlib.Complexity.RAMSimulation.Sim.PhaseEmit
import TCSlib.Complexity.TuringMachine.Build.InputBit
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2's simulation: one phase per instruction

The simulating machine runs one phase for each instruction it executes. A phase is a machine on
the eight tapes of `WordRAM.Sim.Encodes`: from tapes encoding a configuration `c` whose current
instruction is `ins`, it reaches tapes encoding the next configuration `xstep … c`, and its exit
tells the host where the program goes next. The host (a phase host over the program's positions)
and the induction over a run are built from these phases.

Every phase is a nondeterministic machine whose two transitions agree everywhere except at the
entry of a `coin` phase, where the choice is the coin. Fixing the choice gives a deterministic
machine (`Turing.NDTM.fixChoice`), and the phase's run is stated for each fixed choice; the
deterministic simulation fixes it to `false`, so that coins read `0`.

## Main definitions

* `WordRAM.Sim.isCoin`, `WordRAM.Sim.isVerdict`, `WordRAM.Sim.jumpTarget`.

## Main results

* `WordRAM.Sim.exists_phase`: the phase of an instruction other than `accept` and `reject`.
* `WordRAM.Sim.exists_verdictPhase`: the phase of `accept` and `reject`, which writes the output
  and halts.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2: nondeterministic machines.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the word RAM (`TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`.
-/

namespace WordRAM.Sim

open Turing

/-- Whether an instruction is a `coin`. -/
def isCoin : XInstr → Bool
  | .coin _ => true
  | _ => false

/-- Whether an instruction is a `coin`, as an equation. -/
theorem isCoin_def (ins : XInstr) :
    isCoin ins = match ins with
      | .coin _ => true
      | _ => false := by
  cases ins <;> rfl

/-- Whether an instruction gives a verdict: `accept` or `reject`. -/
def isVerdict : XInstr → Bool
  | .base .accept => true
  | .base .reject => true
  | _ => false

/-- Whether an instruction gives a verdict, as an equation. -/
theorem isVerdict_def (ins : XInstr) :
    isVerdict ins = match ins with
      | .base .accept => true
      | .base .reject => true
      | _ => false := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- The position a taken jump goes to: the label of `bltz`, and `0` for any other instruction
(which never jumps). -/
def jumpTarget : XInstr → ℕ
  | .base (.bltz _ l) => l
  | _ => 0

/-- The position a taken jump goes to, as an equation. -/
theorem jumpTarget_def (ins : XInstr) :
    jumpTarget ins = match ins with
      | .base (.bltz _ l) => l
      | _ => 0 := by
  rcases ins with ins | _ | _ | _ | _ <;> try rfl

/-- **The phase of an instruction.** For `a`, an output mode `fn` and an instruction `ins` that is
not a verdict and whose addresses are below `2^(a-1)` in absolute value, there is a
nondeterministic machine `N` on eight tapes, with an entry and two exits `next` and `jump`, and a
constant `C`, such that:
* the entry is never re-entered, and the two transitions of `N` agree at every state except the
  entry, and at the entry too unless `ins` is a `coin`;
* for each choice `b`: whenever the instruction at `c.pc` of a program `P` is `ins` (and, for a
  `coin`, the coin `ρ.getD c.rd false` is `b`), and `d`, at the entry, encodes `c` over the cells
  `T` with origins `o`, then `xstep P x ρ c` is a configuration `c'`, and the machine with the
  choice fixed to `b` reaches, within `C·((|T| + 1)·(W + 1) + W² + |x| + 1)` steps and radius
  `C·((|T| + 1)·(W + 1) + log |x| + 1)`, a configuration `d'` encoding `c'` over the cells
  `T ∪ touches` with the same origins, at `next` if the program goes on to `c.pc + 1` and at
  `jump` if it jumps to `jumpTarget ins`.

[AB09, Exercise 1.9; §2.1.2]

**Proof sketch.** Choose the certified phase by cases on `ins`: `phase_oneMachine`,
`phase_binaryMachine`, the load/store/half/input machines, `phase_bltzMachine`,
`phase_emitMachine` or `phase_coinMachine`. These place the native word, keyed-memory and input
rows on the eight tapes and compose their contracts. The coin and emission continuations use
`NDTM.phaseHostND` through `Contract.inPhase`; the coin remembers its one choice at a fresh
entry. `TableOf` correctness and the address-range/layout lemmas preserve the memory encoding,
and `phaseTime`/`phaseSpace` absorb every native allowance and dispatch. Finally remove the
initial control with `PhaseFrame.ofCfg`, run the selected `PhaseMachine`, and apply its
`PhasePost` to the matching program and compatible coin stream. Reinstall the selected next or
jump control; encoding congruence preserves the tape postcondition and the frame equations give
the theorem's exact bounds. -/
theorem exists_phase (a : ℕ) (fn : Bool) (ins : XInstr) (hins : ImmBound a ins)
    (hv : isVerdict ins = false) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (N : NDTM 8 Bool S) (entry next jump : S)
      (C : ℕ), next ≠ jump ∧
      (∀ (b : Bool) (q : S) inp work, (N.tr b q inp work).state ≠ some entry) ∧
      (∀ q : S, q ≠ entry ∨ isCoin ins = false → N.tr false q = N.tr true q) ∧
      ∀ (b : Bool) {x : List Bool} {W : ℕ} (P : XProgram) (ρ : List Bool) (T : Finset ℤ)
        (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x),
        P.getD c.pc (.base .reject) = ins → (isCoin ins = true → ρ.getD c.rd false = b) →
        d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
        ∃ (c' : XCfg W) (d' : Turing.Cfg 8 Bool S x), xstep P x ρ c = .inl c' ∧
          Encodes a fn (T ∪ ins.touches c.mem) c' (Function.Embedding.refl _) o d' ∧
          ((d'.state = some next ∧ c'.pc = c.pc + 1) ∨
            (d'.state = some jump ∧ c'.pc = jumpTarget ins)) ∧
          ReachesWithin (N.fixChoice b) d {some next, some jump}
            (C * ((T.card + 1) * (W + 1) + W ^ 2 + x.length + 1))
            (C * ((T.card + 1) * (W + 1) + (Nat.bits x.length).length + 1)) d' := by
  have hImm : ∀ z ∈ immediates ins, InRange a z := (immBound_iff a ins).mp hins
  have hm : ∃ flag : Bool → List Bool → PhaseData → Bool,
      Nonempty (PhaseMachine (isCoin ins) (PhaseState a fn (fun _ _ _ => none))
        (fun b x i F => PhasePost a fn ins (jumpTarget ins) (flag b x i) b x i F) flag) := by
    cases ins with
    | base op =>
      cases op with
      | one z =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_oneMachine a fn z hz
      | add z j k =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        have hk := hImm k (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_binaryMachine a fn z j k hz hj hk .add
      | sub z j k =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        have hk := hImm k (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_binaryMachine a fn z j k hz hj hk .sub
      | mul z j k =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        have hk := hImm k (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_binaryMachine a fn z j k hz hj hk .mul
      | load z j =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_loadMachine a fn z j hz hj
      | store z j =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ _ => false, ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_storeMachine a fn z j hz hj
      | bltz z label =>
        have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
        refine ⟨fun _ _ i => PhaseTestKind.sign.bit (i.cfg.mem z), ?_⟩
        simpa only [isCoin_def, jumpTarget_def] using phase_bltzMachine a fn z label hz
      | accept =>
        have h : (true : Bool) = false := by simpa only [isVerdict_def] using hv
        cases h
      | reject =>
        have h : (true : Bool) = false := by simpa only [isVerdict_def] using hv
        cases h
    | rdIn z j =>
      have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
      have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
      refine ⟨fun _ _ _ => false, ?_⟩
      simpa only [isCoin_def, jumpTarget_def] using phase_inputMachine a fn z j hz hj
    | emit z =>
      have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
      refine ⟨fun _ _ _ => false, ?_⟩
      simpa only [isCoin_def, jumpTarget_def] using phase_emitMachine a fn z hz
    | coin z =>
      have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
      refine ⟨fun _ _ _ => false, ?_⟩
      simpa only [isCoin_def, jumpTarget_def] using phase_coinMachine a fn z hz
    | half z j =>
      have hz := hImm z (by simp only [immediates_def, List.mem_cons]; tauto)
      have hj := hImm j (by simp only [immediates_def, List.mem_cons]; tauto)
      refine ⟨fun _ _ _ => false, ?_⟩
      simpa only [isCoin_def, jumpTarget_def] using phase_halfMachine a fn z j hz hj
  obtain ⟨flag, ⟨M⟩⟩ := hm
  letI := M.finite
  letI := M.decEq
  refine ⟨M.State, M.finite, M.decEq, M.machine, M.entry, M.next, M.jump, M.constant,
    M.distinct, M.fresh, M.agree, ?_⟩
  intro b x W P ρ T c o d hf hc hd he
  let i : PhaseData := ⟨W, T, c, o⟩
  let F := PhaseFrame.ofCfg d
  have hp : PhaseState a fn (fun _ _ _ => none) x i F := by
    apply (phaseState_iff a fn _ x i F).mpr
    refine ⟨phase_frame_ofCfg_encodes fn T c o d he, ?_⟩
    intro r w h
    cases h
  obtain ⟨G, hq, hr⟩ := M.run b x i F hp
  have hcoins : ∀ z : ℤ, ins = .coin z → ρ.getD c.rd false = b := by
    intro z hz
    apply hc
    simp only [hz, isCoin_def]
  obtain ⟨c', hs, he', hpc⟩ := (phasePost_iff a fn ins (jumpTarget ins) (flag b x i) b x i G).mp
    hq P ρ hf hcoins
  let d' := G.cfg (if flag b x i then M.jump else M.next)
  refine ⟨c', d', hs, ?_, ?_, ?_⟩
  · exact (phase_encodes_congr fn _ c' c' (Function.Embedding.refl _) o (G.cfg ()) d'
      (by simp only [d', PhaseFrame.cfg_eq]) (by simp only [d', PhaseFrame.cfg_eq])
      (by simp only [d', PhaseFrame.cfg_eq]) rfl rfl).mp he'
  · by_cases hflag : flag b x i = true
    · right
      exact ⟨by simp only [d', if_pos hflag, PhaseFrame.cfg_eq],
        by simpa only [if_pos hflag] using hpc⟩
    · left
      exact ⟨by simp only [d', if_neg hflag, PhaseFrame.cfg_eq],
        by simpa only [if_neg hflag] using hpc⟩
  · have hF : F.cfg M.entry = d := PhaseFrame.cfg_ofCfg d M.entry hd
    rw [hF] at hr
    simpa only [i, phaseTime_eq, phaseSpace_eq, d'] using hr

/-- **The phase of a verdict.** For an output mode `fn` and a verdict `v`, there is a deterministic
machine on eight tapes, with an entry, and a constant `C`, such that from tapes at the entry
encoding `c`, the machine halts within `C` steps with the output `c.out` in function mode and
`[v]` in verdict mode, every head fixed. [AB09, Exercise 1.9]

**Proof sketch.** A stationary action halts after one step, emitting `v` precisely in verdict
mode. `encodes_iff` supplies the initial output. `MultiTapeTM.runFrom_one`,
`MultiTapeTM.step_of_some` and the field equations of `Action.apply` give the final state,
output and unchanged heads. There is no catalog row for this stationary optional emission
followed by a halt, so the action is supplied directly. -/
theorem exists_verdictPhase (fn v : Bool) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 8 Bool S) (entry : S)
      (C : ℕ),
      ∀ (a : ℕ) {x : List Bool} {W : ℕ} (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ)
        (d : Turing.Cfg 8 Bool S x),
        d.state = some entry → Encodes a fn T c (Function.Embedding.refl _) o d →
        ∃ t ≤ C, (M.runFrom d t).state = none ∧
          (M.runFrom d t).output = (if fn then c.out else [v]) ∧
          ∀ s ≤ t, (M.runFrom d s).workTapePos = d.workTapePos := by
  let M : MultiTapeTM 8 Bool Unit :=
    ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), if fn then none else some v, none⟩⟩
  refine ⟨Unit, inferInstance, inferInstance, M, (), 1, ?_⟩
  intro a x W T c o d hd he
  have ho := ((encodes_iff a fn T c (Function.Embedding.refl _) o d).mp he).2.2.2.2.2.2
  have hstep : M.runFrom d 1 =
      (M.tr () d.inputSymbol d.workTapeSymbols).apply d := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some (tm := M) hd]
  refine ⟨1, le_rfl, ?_, ?_, ?_⟩
  · rw [hstep, Action.apply_state]
  · rw [hstep, Action.apply_output, ho]
    cases fn <;> simp only [M, Bool.false_eq_true, ↓reduceIte, Option.toList_some,
      Option.toList_none, List.nil_append, List.append_nil]
  · intro s hs
    have hs' : s = 0 ∨ s = 1 := by omega
    rcases hs' with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero]
    · rw [hstep]
      funext j
      rw [Action.apply_workTapePos]
      simp only [M, SignType.coe_zero, add_zero]

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseAtoms.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBlock

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Atomic blocks for instruction schedules

The native rows become blocks that retain the RAM encoding and track known register words.
Their constants absorb the native allowances into the common instruction units.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_writeBlock`: a register-writing row updates its known-register specification.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A correctly sized register-writing row gives a block that updates the destination's known
word and retains the encoding and all other specified words. -/
theorem phase_writeBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (r : Fin 8) (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4)
    (values : (x : List Bool) → PhaseData → List Bool)
    {pre : ∀ {x : List Bool}, PhaseData → PhaseFrame x → Prop}
    {B E : ∀ {x : List Bool}, PhaseData → ℕ}
    (R : PhaseRow (fun _ => PhaseData) pre (fun {x} i F => F.write r (values x i)) @B @E)
    (C : ℕ) (hP : ∀ x i F, PhaseState a fn regs x i F → pre i F)
    (hw : ∀ x i, (values x i).length = if r = 1 then i.width + a else i.width)
    (hB : ∀ x i, B (x := x) i ≤ C * phaseTime i x)
    (hE : ∀ x i, E (x := x) i ≤ C * phaseSpace i x) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) r (some (values x i))))) := by
  apply PhaseBlock.ofRow R C hP _ hB hE
  intro x i F hp
  simpa only [phaseState_iff] using phase_state_write a fn regs x i F hp r hr₀ hr₁
    (values x i) (hw x i)

/-- Multiplying a native memory charge by its constant fits the common allowance whenever
that allowance dominates the footprint/word product. -/
theorem phase_memory_allowance (a C : ℕ) (i : PhaseData) (U : ℕ)
    (hU : (i.cells.card + 1) * (i.width + 1) ≤ U) :
    C * phaseMemoryCost a i ≤ (C * (a + 4)) * U := by
  calc
    _ ≤ C * ((a + 4) * ((i.cells.card + 1) * (i.width + 1))) :=
      Nat.mul_le_mul_left C (phase_memory_charge a i)
    _ ≤ C * ((a + 4) * U) := Nat.mul_le_mul_left C (Nat.mul_le_mul_left (a + 4) hU)
    _ = (C * (a + 4)) * U := by ring

/-- A fixed integer writer on a compatible selected register gives a block that records the
new exact word and retains all other known register words.

**Proof sketch.** Place `phase_intRow` on the supplied bank. Its readiness and blank scratch
come from the encoding. `phase_writeBlock` retains the invariant, and `phase_units` increases
the native linear allowances. This adapter is shared by key, one and coin word writers. -/
theorem phase_intBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : ℤ) (extra : ℕ) (σ : Fin 5 ↪ Fin 8)
    (hσ : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (σ r).val)
    (hr₀ : 1 ≤ (σ 2).val) (hr₁ : (σ 2).val ≤ 4)
    (hext : ∀ W : ℕ, W + extra = if σ 2 = 1 then W + a else W) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) (σ 2)
        (some (bvBits (BitVec.ofInt (i.width + extra) z)))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_intRow (I := fun _ => PhaseData) (fun i => i.width) z extra σ hσ
  apply phase_writeBlock a fn regs (σ 2) hr₀ hr₁ _ R C
  · intro x i F hp
    have he := ((phaseState_iff a fn regs x i F).mp hp).1
    refine ⟨?_, phase_frame_scratch fn i.cells i.cfg i.origins F he⟩
    rw [hext]
    exact phase_frame_ready fn i.cells i.cfg i.origins F he (σ 2) hr₀ hr₁
  · intro x i
    rw [bvBits_length]
    exact hext i.width
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.1
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.2.1

/-- A fixed integer address is written to the key register, retaining the encoded memory and
all other known registers, with a uniform phase constant. -/
theorem phase_keyBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool)) (z : ℤ) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 1 (some (keyBits a i.width z))))) := by
  simpa only [phaseKeyBank_apply, keyBits_def] using
    phase_intBlock a fn regs z a phaseKeyBank
      (by simp only [phaseKeyBank_apply]; decide)
      (by simp only [phaseKeyBank_apply]; decide)
      (by simp only [phaseKeyBank_apply]; decide)
      (by intro W; rw [phaseKeyBank_apply]; rfl)

/-- A fixed integer is written as a word to result register four, retaining the encoded memory
and all other known registers. -/
theorem phase_constBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool)) (z : ℤ) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 4
        (some (bvBits (BitVec.ofInt i.width z)))))) := by
  simpa only [phaseArithBank_apply, Nat.add_zero] using
    phase_intBlock a fn regs z 0 phaseArithBank
      (by simp only [phaseArithBank_apply]; decide)
      (by simp only [phaseArithBank_apply]; decide)
      (by simp only [phaseArithBank_apply]; decide)
      (by intro W; rw [phaseArithBank_apply]; rfl)

/-- With the addressed key known on tape one, lookup loads its memory word into the chosen
word register and retains the encoding and other known words.

**Proof sketch.** `phase_lookupRow` supplies the placed memory row. `PhaseState` supplies its
key, encoding, readiness and scratch. `phase_writeBlock` updates the known-register map, and
`phase_memory_allowance` absorbs the table charge into the phase units. -/
theorem phase_lookupBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : PhaseData → ℤ) (dst : Fin 3)
    (hk : ∀ x i, regs x i 1 = some (keyBits a i.width (z i)))
    (hz : ∀ i, InRange (i.width + a) (z i)) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) (phaseMemoryBank dst 2)
        (some (bvBits (i.cfg.mem (z i))))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_lookupRow a fn z dst
  have hr : (phaseMemoryBank dst 2).val = dst.val + 2 := by
    rw [phaseMemoryBank_apply]
    rfl
  have hr₀ : 1 ≤ (phaseMemoryBank dst 2).val := by omega
  have hr₁ : (phaseMemoryBank dst 2).val ≤ 4 := by have := dst.isLt; omega
  have hne : phaseMemoryBank dst 2 ≠ 1 := by
    intro h
    have hh := congrArg Fin.val h
    omega
  apply phase_writeBlock a fn regs (phaseMemoryBank dst 2) hr₀ hr₁ _ R (C * (a + 4))
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    refine ⟨he, hregs 1 _ (hk x i), ?_, hz i⟩
    simpa only [if_neg hne] using phase_frame_ready fn i.cells i.cfg i.origins F he
      (phaseMemoryBank dst 2) hr₀ hr₁
  · intro x i
    rw [bvBits_length, if_neg hne]
  · intro x i
    exact phase_memory_allowance a C i _ (phase_units i x).2.2.2.2.2.2.1
  · intro x i
    exact phase_memory_allowance a C i _ (phase_units i x).2.2.2.2.2.2.2

/-- With the address key and value word known in registers one and four, assignment updates
the encoded RAM memory and includes the destination cell in its footprint.

**Proof sketch.** Apply `phase_assignRow` under the known-register preconditions. Its endpoint
satisfies `phase_frame_assign_encodes`; `PhaseBlock.ofRow` retains that postcondition, and
`phase_memory_allowance` bounds the native table charge. -/
theorem phase_assignBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : PhaseData → ℤ) (v : (x : List Bool) → (i : PhaseData) → BitVec i.width)
    (hk : ∀ x i, regs x i 1 = some (keyBits a i.width (z i)))
    (hv : ∀ x i, regs x i 4 = some (bvBits (v x i)))
    (hz : ∀ i, InRange (i.width + a) (z i)) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (fun x i F => Encodes a fn (insert (z i) i.cells)
        { i.cfg with mem := Function.update i.cfg.mem (z i) (v x i) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_assignRow a fn z v
  apply PhaseBlock.ofRow R (C * (a + 4))
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    exact ⟨he, hregs 1 _ (hk x i), hregs 4 _ (hv x i), hz i⟩
  · intro x i F hp
    exact phase_frame_assign_encodes a fn i F ((phaseState_iff a fn regs x i F).mp hp).1
      (z i) (hz i) (v x i)
  · intro x i
    exact phase_memory_allowance a C i _ (phase_units i x).2.2.2.2.2.2.1
  · intro x i
    exact phase_memory_allowance a C i _ (phase_units i x).2.2.2.2.2.2.2

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseBlock.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Certified instruction blocks

The component rows use different native allowances and exact frame transformations. A block
retains their finite control and bounded run, with a precondition and postcondition on frames
and a single uniform phase constant. Blocks compose through the existing seam contract.

## Main definitions

* `WordRAM.Sim.PhaseBlock`: a finite deterministic block with a uniform phase allowance.
* `WordRAM.Sim.PhaseState`: the RAM encoding together with known register words.

## Main results

* `WordRAM.Sim.PhaseBlock.seq`: sequence blocks while adding their constants and one dispatch.
* `WordRAM.Sim.phase_state_write`: retain the encoding and known words after a register write.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A finite deterministic block takes a frame satisfying its precondition to a frame satisfying
its postcondition, restores all work heads and obeys a uniform instruction-phase allowance. -/
structure PhaseBlock
    (P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop) where
  State : Type
  finite : Fintype State
  decEq : DecidableEq State
  machine : MultiTapeTM 8 Bool State
  entry : State
  exit : State
  constant : ℕ
  run : ∀ (x : List Bool) (i : PhaseData) (F : PhaseFrame x), P x i F →
    ∃ G : PhaseFrame x, Q x i G ∧ G.workTapePos = F.workTapePos ∧
      ReachesWithin machine (F.cfg entry) {some exit}
        (constant * phaseTime i x) (constant * phaseSpace i x) (G.cfg exit)

/-- A row whose precondition follows from `P`, whose result satisfies `Q`, and whose allowances
fit the common phase units gives a block with the same finite machine. -/
theorem PhaseBlock.ofRow
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {pre : ∀ {x : List Bool}, PhaseData → PhaseFrame x → Prop}
    {f : ∀ {x : List Bool}, PhaseData → PhaseFrame x → PhaseFrame x}
    {B E : ∀ {x : List Bool}, PhaseData → ℕ}
    (R : PhaseRow (fun _ => PhaseData) @pre @f @B @E) (C : ℕ)
    (hP : ∀ x i F, P x i F → pre i F)
    (hQ : ∀ x i F, P x i F → Q x i (f i F))
    (hB : ∀ x i, B (x := x) i ≤ C * phaseTime i x)
    (hE : ∀ x i, E (x := x) i ≤ C * phaseSpace i x) : Nonempty (PhaseBlock P Q) := by
  refine ⟨⟨R.State, R.finite, R.decEq, R.machine, R.entry, R.exit, C, ?_⟩⟩
  intro x i F hp
  exact ⟨f i F, hQ x i F hp, R.heads i F (hP x i F hp),
    (R.run i F (hP x i F hp)).mono (hB x i) (hE x i)⟩

/-- Changing a block's precondition to a stronger one and its postcondition to a weaker one
retains its machine and allowance. -/
theorem PhaseBlock.weaken
    {P Q P' Q' : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    (R : PhaseBlock P Q) (hP : ∀ x i F, P' x i F → P x i F)
    (hQ : ∀ x i F, Q x i F → Q' x i F) : Nonempty (PhaseBlock P' Q') := by
  refine ⟨⟨R.State, R.finite, R.decEq, R.machine, R.entry, R.exit, R.constant, ?_⟩⟩
  intro x i F hp
  obtain ⟨G, hq, hh, hr⟩ := R.run x i F (hP x i F hp)
  exact ⟨G, hQ x i G hq, hh, hr⟩

/-- Two blocks compose through their seam. Their constants add, with one further unit for the
dispatch step.

**Proof sketch.** Run the first block and use its postcondition as the second block's
precondition. `phase_reaches_seq` composes the bounded runs through `Contract.seq`; the restored
intermediate heads give a common center. The phase units are positive, so their sum plus the
one dispatch step is bounded by the sum of constants plus one. -/
theorem PhaseBlock.seq
    {P Q R : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    (A : PhaseBlock P Q) (B : PhaseBlock Q R) : Nonempty (PhaseBlock P R) := by
  classical
  letI := A.finite
  letI := A.decEq
  letI := B.finite
  letI := B.decEq
  refine ⟨⟨A.State ⊕ B.State, inferInstance, inferInstance,
    seamCompTM A.machine A.exit B.machine B.entry, Sum.inl A.entry, Sum.inr B.exit,
    A.constant + B.constant + 1, ?_⟩⟩
  intro x i F hp
  obtain ⟨G, hq, hhG, hrA⟩ := A.run x i F hp
  obtain ⟨H, hr, hhH, hrB⟩ := B.run x i G hq
  refine ⟨H, hr, hhH.trans hhG, ?_⟩
  have hrun := phase_reaches_seq A.machine B.machine A.entry A.exit B.entry B.exit
    {some B.exit} F G H _ _ _ _ hrA hrB (Set.mem_singleton_iff.mpr rfl) hhG
  have ht : A.constant * phaseTime i x + 1 + B.constant * phaseTime i x ≤
      (A.constant + B.constant + 1) * phaseTime i x := by
    have hu := (phase_units i x).1
    nlinarith
  have he : A.constant * phaseSpace i x + B.constant * phaseSpace i x ≤
      (A.constant + B.constant + 1) * phaseSpace i x := by nlinarith
  simpa only [Set.image_singleton, Option.map_some] using hrun.mono ht he

/-- The encoding together with the specified known words in any registers. A `none` register
specification imposes no additional word condition. -/
def PhaseState (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) : Prop :=
  Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
    ∀ r w, regs x i r = some w → WordAt (F.cfg ()) r w

/-- A register state consists of its RAM encoding and each specified exact register word. -/
theorem phaseState_iff (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) :
    PhaseState a fn regs x i F ↔
      Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
        ∀ r w, regs x i r = some w → WordAt (F.cfg ()) r w := Iff.rfl

/-- Overwriting a correctly sized register preserves the encoding and every known word on
other registers, and records the new exact word at its destination.

**Proof sketch.** Use `phase_frame_write_encodes` for the encoding. At the written register,
`phase_frame_write_word` uses the readiness supplied by the encoding; elsewhere,
`phase_frame_write_other` preserves the prior word. `Function.update` describes these two cases. -/
theorem phase_state_write (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) (hp : PhaseState a fn regs x i F)
    (r : Fin 8) (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4) (w : List Bool)
    (hw : w.length = if r = 1 then i.width + a else i.width) :
    PhaseState a fn (fun y j => Function.update (regs y j) r (some w)) x i (F.write r w) := by
  obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
  apply (phaseState_iff a fn _ x i (F.write r w)).mpr
  refine ⟨phase_frame_write_encodes fn i.cells i.cfg i.origins F he r hr₀ hr₁ w hw, ?_⟩
  intro j v hj
  by_cases h : j = r
  · subst j
    simp only [Function.update_self, Option.some.injEq] at hj
    subst v
    exact phase_frame_write_word F r _ w (phase_frame_ready fn i.cells i.cfg i.origins F he
      r hr₀ hr₁) hw
  · exact phase_frame_write_other F r j w v h (hregs j v
      (by simpa only [Function.update_of_ne h] using hj))

/-- Moving only the input head preserves the RAM encoding and all known register words. -/
theorem phase_state_inputPos (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) (hp : PhaseState a fn regs x i F)
    (ip : Fin (x.length + 2)) : PhaseState a fn regs x i { F with inputPos := ip } := by
  obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
  apply (phaseState_iff a fn regs x i _).mpr
  refine ⟨?_, ?_⟩
  · exact (phase_encodes_congr fn i.cells i.cfg i.cfg (Function.Embedding.refl _) i.origins
      (F.cfg ()) (({ F with inputPos := ip } : PhaseFrame x).cfg ())
      (by simp only [PhaseFrame.cfg_eq]) (by simp only [PhaseFrame.cfg_eq])
      (by simp only [PhaseFrame.cfg_eq]) rfl rfl).mp he
  · intro r w hr
    exact (phase_wordAt_congr (F.cfg ()) (({ F with inputPos := ip } : PhaseFrame x).cfg ()) r w
      (by simp only [PhaseFrame.cfg_eq]) (by simp only [PhaseFrame.cfg_eq])).mp (hregs r w hr)

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseBounds.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseInput

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform allowances for instruction rows

A phase has a common time allowance for memory, multiplication and input access, and a space
allowance for memory and the binary input length. Native rows fit constant multiples of these
allowances, so sequencing adds only constants.

## Main definitions

* `WordRAM.Sim.phaseTime`, `WordRAM.Sim.phaseSpace`: time and radius units for one instruction.

## Main results

* `WordRAM.Sim.phase_memory_charge`: keyed-memory cost fits a constant times the memory unit.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim

/-- The phase time unit: represented memory, word multiplication and read-only input access. -/
def phaseTime (i : PhaseData) (x : List Bool) : ℕ :=
  (i.cells.card + 1) * (i.width + 1) + i.width ^ 2 + x.length + 1

/-- The time unit is the footprint/word product plus the squared word width and input length. -/
theorem phaseTime_eq (i : PhaseData) (x : List Bool) :
    phaseTime i x = (i.cells.card + 1) * (i.width + 1) + i.width ^ 2 + x.length + 1 := rfl

/-- The phase radius unit: represented memory and the binary read-only input length. -/
def phaseSpace (i : PhaseData) (x : List Bool) : ℕ :=
  (i.cells.card + 1) * (i.width + 1) + (Nat.bits x.length).length + 1

/-- The radius unit is the footprint/word product plus the binary input length. -/
theorem phaseSpace_eq (i : PhaseData) (x : List Bool) :
    phaseSpace i x = (i.cells.card + 1) * (i.width + 1) + (Nat.bits x.length).length + 1 := rfl

/-- The memory component of either allowance dominates one word plus one cell. -/
theorem phase_word_memory (i : PhaseData) :
    i.width + 1 ≤ (i.cells.card + 1) * (i.width + 1) := by
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right (i.width + 1)
    (Nat.le_add_left 1 i.cells.card)

/-- Native word, input and memory units fit the common positive time and radius allowances. -/
theorem phase_units (i : PhaseData) (x : List Bool) :
    1 ≤ phaseTime i x ∧ 1 ≤ phaseSpace i x ∧
    i.width + 1 ≤ phaseTime i x ∧ i.width + 1 ≤ phaseSpace i x ∧
    i.width + x.length + 1 ≤ phaseTime i x ∧
    i.width + (Nat.bits x.length).length + 1 ≤ phaseSpace i x ∧
    (i.cells.card + 1) * (i.width + 1) ≤ phaseTime i x ∧
    (i.cells.card + 1) * (i.width + 1) ≤ phaseSpace i x := by
  have hw := phase_word_memory i
  rw [phaseTime_eq, phaseSpace_eq]
  omega

/-- The actual table/key/value charge is at most `a+4` times the footprint/word product. -/
theorem phase_memory_charge (a : ℕ) (i : PhaseData) :
    phaseMemoryCost a i ≤ (a + 4) * ((i.cells.card + 1) * (i.width + 1)) := by
  have h₁ : i.width + a + i.width + 4 ≤ (a + 4) * (i.width + 1) := by nlinarith
  have h₂ : i.width + a + i.width + 2 ≤ (a + 4) * (i.width + 1) := by nlinarith
  calc
    phaseMemoryCost a i =
        i.cells.card * (i.width + a + i.width + 4) + (i.width + a + i.width + 2) := by
      rw [phaseMemoryCost_eq]
      omega
    _ ≤ i.cells.card * ((a + 4) * (i.width + 1)) + (a + 4) * (i.width + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h₁) h₂
    _ = (a + 4) * ((i.cells.card + 1) * (i.width + 1)) := by ring

/-- The native arithmetic time factor is at most three times the common time allowance. -/
theorem phase_arith_charge (op : PhaseArith) (i : PhaseData) (x : List Bool) :
    op.steps i.width ≤ 3 * phaseTime i x := by
  have hw := phase_word_memory i
  cases op <;> rw [PhaseArith.steps_eq, phaseTime_eq] <;> nlinarith

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseBranchMachines.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSemantics
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBranching

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The signed branch instruction phase

A branch fetches its operand, tests its signed value and selects the next or jump exit. No
memory or output changes; only the RAM control position changes.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_post_of_read`: connect an unchanged encoded memory/output to its RAM step.
* `WordRAM.Sim.phase_bltzMachine`: the phase for a negative-value branch.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A frame with unchanged encoded memory and output gives the semantic postcondition whenever
the matching RAM step has that memory/output and the selected program counter. -/
theorem phase_post_of_read (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ) (taken b : Bool)
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x)
    (he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()))
    (hstep : ∀ (P : XProgram) (ρ : List Bool), P.getD i.cfg.pc (.base .reject) = ins →
      (∀ k : ℤ, ins = .coin k → ρ.getD i.cfg.rd false = b) →
      ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
        c'.mem = i.cfg.mem ∧ c'.out = i.cfg.out ∧
        (if taken then c'.pc = label else c'.pc = i.cfg.pc + 1)) :
    PhasePost a fn ins label taken b x i F := by
  apply (phasePost_iff a fn ins label taken b x i F).mpr
  intro P ρ hf hc
  obtain ⟨c', hs, hm, ho, hp⟩ := hstep P ρ hf hc
  have he' := phase_encodes_mono fn i.cells (i.cells ∪ ins.touches i.cfg.mem) i.cfg
    (Function.Embedding.refl _) i.origins (F.cfg ()) he Finset.subset_union_left
  exact ⟨c', hs, (phase_encodes_congr fn _ i.cfg c' (Function.Embedding.refl _) i.origins
    (F.cfg ()) (F.cfg ()) rfl rfl rfl hm.symm ho.symm).mp he', hp⟩

/-- Fetching and testing an immediate operand gives a fresh-entry two-exit phase, retaining
the encoded memory and known fetched registers. The sign and output instructions share it. -/
theorem phase_testMachine (a : ℕ) (fn : Bool) (z : ℤ) (hz : InRange a z) (op : PhaseTestKind) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun _ => PhaseState a fn (fun _ i => Function.update
        (Function.update (fun _ => none) 1 (some (keyBits a i.width z))) 2
          (some (bvBits (i.cfg.mem z))))) (fun _ _ i => op.bit (i.cfg.mem z))) := by
  let regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i =>
    Function.update (Function.update (fun _ => none) 1 (some (keyBits a i.width z))) 2
      (some (bvBits (i.cfg.mem z)))
  obtain ⟨F⟩ := phase_fetchBlock a fn (fun _ _ _ => none) z 0 hz
  simp only [phaseMemoryBank_apply] at F
  obtain ⟨T⟩ := phase_testBlock a fn regs (fun i => i.cfg.mem z) op (by intro x i; rfl)
  obtain ⟨FT⟩ := PhaseBranch.seq F T
  exact phase_machine_ofBranch FT

/-- A branch instruction has a finite phase with a fresh entry, equal choices, and the jump
exit exactly when its operand has negative signed value.

**Proof sketch.** Fetch the operand into register two and prefix the native sign test using
`PhaseBranch.seq`. `phase_machine_ofBranch` supplies the fresh entry and maps its yes/no exits
to jump/next. The unchanged encoding transfers through `phase_post_of_read`, while `xstep_def`
and `PhaseTestKind.bit_eq` identify the selected program counter. -/
theorem phase_bltzMachine (a : ℕ) (fn : Bool) (z : ℤ) (label : ℕ) (hz : InRange a z) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.base (.bltz z label)) label
        (PhaseTestKind.sign.bit (i.cfg.mem z)) b x i F)
      (fun _ _ i => PhaseTestKind.sign.bit (i.cfg.mem z))) := by
  let regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i =>
    Function.update (Function.update (fun _ => none) 1 (some (keyBits a i.width z))) 2
      (some (bvBits (i.cfg.mem z)))
  obtain ⟨M⟩ := phase_testMachine a fn z hz .sign
  apply M.weaken (by intro x i F hp; exact hp)
  intro b x i G hp
  apply phase_post_of_read a fn (.base (.bltz z label)) label _ b x i G
    ((phaseState_iff a fn regs x i G).mp hp).1
  intro P ρ hf hc
  refine ⟨{ i.cfg with pc := if (i.cfg.mem z).toInt < 0 then label else i.cfg.pc + 1 },
    ?_, rfl, rfl, ?_⟩
  · simp only [xstep_def, hf]
  · simp only [PhaseTestKind.bit_eq, decide_eq_true_eq]
    split_ifs <;> rfl

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseBranching.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Prefixing and wrapping two-exit instruction blocks

Ordinary blocks can precede a word test. A fresh-entry seam wrapper then turns its two native
exits into the phase's next and jump exits, with the same selected branch.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.PhaseBranch.seq`: prefix a branch by an ordinary block.
* `WordRAM.Sim.phase_machine_ofBranch`: add fresh entry and deterministic choice agreement.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The selected yes/no state belongs to the two live exits. -/
theorem phase_branch_mem {S : Type} (yes no : S) (flag : Bool) :
    some (if flag then yes else no) ∈ ({some yes, some no} : Set (Option S)) := by
  cases flag
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
  · exact Set.mem_insert_iff.mpr (Or.inl rfl)

/-- An ordinary block followed by a two-exit branch composes through a seam, retaining the
branch flag and adding the constants plus one dispatch.

**Proof sketch.** Run both blocks and apply `phase_reaches_seq` to the second block's two live
exits. Its frame and flag determine the endpoint. Restored intermediate heads give the common
radius center, and the positive phase time unit absorbs the dispatch. -/
theorem PhaseBranch.seq
    {P Q R : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : List Bool → PhaseData → Bool} (A : PhaseBlock P Q) (B : PhaseBranch Q R flag) :
    Nonempty (PhaseBranch P R flag) := by
  classical
  letI := A.finite
  letI := A.decEq
  letI := B.finite
  letI := B.decEq
  refine ⟨⟨A.State ⊕ B.State, inferInstance, inferInstance,
    seamCompTM A.machine A.exit B.machine B.entry, Sum.inl A.entry,
    Sum.inr B.yes, Sum.inr B.no, ?_, A.constant + B.constant + 1, ?_⟩⟩
  · exact fun h => B.distinct (Sum.inr.inj h)
  · intro x i F hp
    obtain ⟨G, hq, hhG, hrA⟩ := A.run x i F hp
    obtain ⟨H, hr, hhH, hrB⟩ := B.run x i G hq
    refine ⟨H, hr, hhH.trans hhG, ?_⟩
    have hs := phase_reaches_seq A.machine B.machine A.entry A.exit B.entry
      (if flag x i then B.yes else B.no) {some B.yes, some B.no} F G H _ _ _ _ hrA hrB
      (phase_branch_mem B.yes B.no (flag x i)) hhG
    have ht : A.constant * phaseTime i x + 1 + B.constant * phaseTime i x ≤
        (A.constant + B.constant + 1) * phaseTime i x := by
      have hu := (phase_units i x).1
      nlinarith
    have he : A.constant * phaseSpace i x + B.constant * phaseSpace i x ≤
        (A.constant + B.constant + 1) * phaseSpace i x := by nlinarith
    simpa only [Set.image_insert_eq, Set.image_singleton, Option.map_some, apply_ite] using
      hs.mono ht he

/-- A two-exit branch gains a never-targeted entry and equal nondeterministic transitions.
The native yes exit is jump and the native no exit is next.

**Proof sketch.** Prefix the branch by the Boolean padding seam, as for a single-exit block.
`phase_seam_fresh` supplies the fresh entry without a second transition analysis. Compose the
zero-time prefix with `phase_reaches_seq`, retain its two-exit cut, and use the deterministic
embedding's fixed-choice equation. -/
theorem phase_machine_ofBranch
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : List Bool → PhaseData → Bool} (R : PhaseBranch P Q flag) :
    Nonempty (PhaseMachine false P (fun _ => Q) (fun _ => flag)) := by
  classical
  letI := R.finite
  letI := R.decEq
  let A : MultiTapeTM 8 Bool Bool :=
    ⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let M := seamCompTM A false R.machine R.entry
  refine ⟨⟨Bool ⊕ R.State, inferInstance, inferInstance, M.toNDTM,
    Sum.inl false, Sum.inr R.no, Sum.inr R.yes, R.constant + 1, ?_, ?_, ?_, ?_⟩⟩
  · exact fun h => R.distinct (Sum.inr.inj h).symm
  · intro b q inp work
    rw [MultiTapeTM.toNDTM_tr]
    exact phase_seam_fresh R.machine R.entry false q inp work
  · intro q hq
    funext inp work
    rw [MultiTapeTM.toNDTM_tr, MultiTapeTM.toNDTM_tr]
  · intro b x i F hp
    obtain ⟨G, hQ, hh, hr⟩ := R.run x i F hp
    have hs := phase_reaches_seq A R.machine false false R.entry
      (if flag x i then R.yes else R.no) {some R.yes, some R.no} F F G 0 0 _ _
      (phase_reaches_zero A (F.cfg false) {some false}) hr
      (phase_branch_mem R.yes R.no (flag x i)) rfl
    have ht : 0 + 1 + R.constant * phaseTime i x ≤ (R.constant + 1) * phaseTime i x := by
      have hu := (phase_units i x).1
      nlinarith
    have he : 0 + R.constant * phaseSpace i x ≤ (R.constant + 1) * phaseSpace i x := by
      nlinarith
    refine ⟨G, hQ, ?_⟩
    rw [phase_toNDTM_fixChoice, Set.pair_comm]
    simpa only [M, Set.image_insert_eq, Set.image_singleton, Option.map_some, apply_ite] using
      hs.mono ht he

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseCoin.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseFork

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The single-choice coin instruction phase

One stationary action at the fresh entry remembers the selected bit in finite control. The
registered host then runs the corresponding deterministic constant-word schedule and joins
both returns at next. Subsequent transitions do not inspect the choice.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_choiceMachine`: remember one choice in control while retaining the frame.
* `WordRAM.Sim.phase_encoded_heads`: two encodings with the same origins have the same heads.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- Two frames encoding configurations at the same origins have identical work-head vectors. -/
theorem phase_encoded_heads {a W : ℕ} {x : List Bool} (fn : Bool)
    (T U : Finset ℤ) (c c' : XCfg W) (o : Fin 8 → ℤ) (F G : PhaseFrame x)
    (hF : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ()))
    (hG : Encodes a fn U c' (Function.Embedding.refl _) o (G.cfg ())) :
    G.workTapePos = F.workTapePos := by
  funext j
  have hf := ((encodes_iff a fn T c (Function.Embedding.refl _) o (F.cfg ())).mp hF).1 j
  have hg := ((encodes_iff a fn U c' (Function.Embedding.refl _) o (G.cfg ())).mp hG).1 j
  simpa only [PhaseFrame.cfg_eq] using hg.trans hf.symm

/-- A stationary one-step source remembers the entry choice in one of two live states without
changing its frame. No catalog row supplies this single-choice, live-return control leaf; its
actions use the existing `FinTM.controlAction`.

**Proof sketch.** At the none-valued entry control, transition `b` silently enters `some b`;
every other control halts. Thus no transition targets the entry, and choices agree elsewhere.
The published one-step and control-action equations identify the unchanged frame after one
step. The initial state differs from both exits, and both work-head vectors are fixed. -/
theorem phase_choiceMachine
    (P : (x : List Bool) → PhaseData → PhaseFrame x → Prop) :
    Nonempty (PhaseMachine true P (fun _ => P) (fun b _ _ => b)) := by
  classical
  let N : NDTM 8 Bool (Option Bool) :=
    ⟨none, fun b q _ _ => if q = none then FinTM.controlAction 0 (some (some b))
      else FinTM.controlAction 0 none⟩
  refine ⟨⟨Option Bool, inferInstance, inferInstance, N, none, some false, some true, 1,
    ?_, ?_, ?_, ?_⟩⟩
  · intro h
    have h' := Option.some.inj h
    cases h'
  · intro b q inp work
    by_cases hq : q = none
    · simp only [N, if_pos hq, FinTM.controlAction_def]
      intro h
      exact Option.noConfusion (Option.some.inj h)
    · simp only [N, if_neg hq, FinTM.controlAction_def]
      exact fun h => Option.noConfusion h
  · intro q hq
    have hn : q ≠ none := by
      rcases hq with hq | hq
      · exact hq
      · cases hq
    simp only [N, if_neg hn]
  · intro b x i F hp
    have hstep : (N.fixChoice b).runFrom (F.cfg none) 1 = F.cfg (some b) := by
      rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some (by rw [PhaseFrame.cfg_eq])]
      simp only [NDTM.fixChoice_tr, N, ↓reduceIte]
      simp only [FinTM.controlAction_apply, moveInputPos_zero, PhaseFrame.cfg_eq]
    have hq : (if b then some true else some false) = some b := by cases b <;> rfl
    refine ⟨F, hp, ?_⟩
    rw [hq]
    apply (reachesWithin_iff _ _ _ _ _ _).mpr
    refine ⟨1, by simpa only [one_mul] using (phase_units i x).1, ?_, ?_, hstep⟩
    · intro s hs hm
      have hs' : s = 0 := by omega
      subst s
      rw [MultiTapeTM.runFrom_zero, PhaseFrame.cfg_eq] at hm
      rcases Set.mem_insert_iff.mp hm with h | h
      · exact Option.noConfusion (Option.some.inj h)
      · exact Option.noConfusion (Option.some.inj (Set.mem_singleton_iff.mp h))
    · intro s hs j
      have hs' : s = 0 ∨ s = 1 := by omega
      rcases hs' with rfl | rfl
      · rw [MultiTapeTM.runFrom_zero, sub_self, abs_zero]
        exact Int.natCast_nonneg _
      · rw [hstep, PhaseFrame.cfg_eq, PhaseFrame.cfg_eq, sub_self, abs_zero]
        exact Int.natCast_nonneg _

/-- A coin instruction has exactly one choice-sensitive entry transition, followed by a
deterministic constant-word assignment for that bit and a shared next exit. Its postcondition
also records the extended RAM's consumed coin through the matching step semantics.

**Proof sketch.** `phase_choiceMachine` remembers the fixed choice without changing the frame.
Instantiate `phase_forkMachine` with the two `phase_constantSchedule` branches. The signed
constant words zero and one equal `coinWord`; `xstep_def` and the compatible stream identify
the updated memory and consumed-coin configuration. `phase_post_of_write` transfers the
encoding, which does not store the RAM coin count. -/
theorem phase_coinMachine (a : ℕ) (fn : Bool) (z : ℤ) (hz : InRange a z) :
    Nonempty (PhaseMachine true (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.coin z) 0 false b x i F) (fun _ _ _ => false)) := by
  obtain ⟨A⟩ := phase_choiceMachine (PhaseState a fn (fun _ _ _ => none))
  apply phase_forkMachine A
  · intro value
    let k : ℤ := if value then 1 else 0
    obtain ⟨K⟩ := phase_constantSchedule a fn z k hz
    apply K.weaken
    · intro x i F hp
      obtain ⟨b, hp, hb⟩ := hp
      exact hp
    · intro x i F he b hb
      subst b
      apply phase_post_of_write a fn (.coin z) 0 value x i F z (BitVec.ofInt i.width k) he
      · simp only [XInstr.touches_def, Finset.mem_singleton]
      · intro P ρ hf hc
        have hw : coinWord i.width value = BitVec.ofInt i.width k := by
          rw [coinWord_def]
          dsimp only [k]
          cases value <;> rfl
        refine ⟨{ i.cfg with
          pc := i.cfg.pc + 1
          mem := Function.update i.cfg.mem z (coinWord i.width value)
          rd := i.cfg.rd + 1 }, ?_, ?_, rfl, rfl⟩
        · simp only [xstep_def, hf, hc z rfl]
        · rw [hw]
  · intro b x i F G hp hq
    exact phase_encoded_heads fn i.cells i.cells i.cfg i.cfg i.origins F G
      ((phaseState_iff a fn _ x i F).mp hp).1 ((phaseState_iff a fn _ x i G).mp hq).1

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseCompute.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseAtoms

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Arithmetic and input blocks

The computation blocks read the known operand words and record their result while retaining
the represented RAM memory. Arithmetic and input costs fit the common phase allowances.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_arithBlock`: addition, subtraction or multiplication into register four.
* `WordRAM.Sim.phase_sourceBlock`: a shared adapter for one-source linear word rows.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- Binary arithmetic on two known operand words records its result on register four, retaining
the RAM encoding and other known words.

**Proof sketch.** Apply `phase_arithRow` using the two known operands, encoded destination
readiness and blank scratch. `phase_writeBlock` maintains the register invariant.
`phase_arith_charge` absorbs multiplication's quadratic time; radius remains linear. -/
theorem phase_arithBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u v : (i : PhaseData) → BitVec i.width) (op : PhaseArith)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i)))
    (hv : ∀ x i, regs x i 3 = some (bvBits (v i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 4
        (some (bvBits (op.value (u i) (v i))))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_arithRow (I := fun _ => PhaseData) (fun i => i.width) u v op
  apply phase_writeBlock a fn regs 4 (by decide) (by decide) _ R (C * 3)
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    exact ⟨hregs 2 _ (hu x i), hregs 3 _ (hv x i),
      phase_frame_ready fn i.cells i.cfg i.origins F he 4 (by decide) (by decide),
      phase_frame_scratch fn i.cells i.cfg i.origins F he⟩
  · intro x i
    rw [bvBits_length, if_neg (by decide)]
  · intro x i
    calc
      _ ≤ C * (3 * phaseTime i x) := Nat.mul_le_mul_left C (phase_arith_charge op i x)
      _ = (C * 3) * phaseTime i x := by ring
  · intro x i
    exact (Nat.mul_le_mul_left C (phase_units i x).2.2.2.1).trans
      (Nat.mul_le_mul_right _ (by omega : C ≤ C * 3))

/-- A linear row reading register two and writing one compatible register gives a block that
retains the encoding and records its result. The adapter is shared by half and sign extension. -/
theorem phase_sourceBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → List Bool) (r : Fin 8) (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4)
    (values : (i : PhaseData) → List Bool) (C : ℕ)
    (R : PhaseRow (fun _ => PhaseData)
      (fun i F => WordAt (F.cfg ()) 2 (u i) ∧
        PhaseReady (if r = 1 then i.width + a else i.width) r F ∧ PhaseScratch F)
      (fun i F => F.write r (values i))
      (fun i => C * (i.width + 1)) (fun i => C * (i.width + 1)))
    (hu : ∀ x i, regs x i 2 = some (u i))
    (hw : ∀ i, (values i).length = if r = 1 then i.width + a else i.width) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) r (some (values i))))) := by
  apply phase_writeBlock a fn regs r hr₀ hr₁ _ R C
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    exact ⟨hregs 2 _ (hu x i),
      phase_frame_ready fn i.cells i.cfg i.origins F he r hr₀ hr₁,
      phase_frame_scratch fn i.cells i.cfg i.origins F he⟩
  · intro x i
    exact hw i
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.1
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.2.1

/-- Arithmetic halving of a known operand records its signed right shift on register four. -/
theorem phase_halfBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → BitVec i.width)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 4
        (some (bvBits ((u i).sshiftRight 1)))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_halfRow (I := fun _ => PhaseData) (fun i => i.width) u
  exact phase_sourceBlock a fn regs (fun i => bvBits (u i)) 4 (by decide) (by decide)
    (fun i => bvBits ((u i).sshiftRight 1)) C R hu
    (by intro i; rw [bvBits_length, if_neg (by decide)])

/-- Sign-extending a known word writes the key of its signed address on register one. -/
theorem phase_signExtendBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → BitVec i.width)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 1
        (some (keyBits a i.width (u i).toInt))))) := by
  obtain ⟨C, ⟨R⟩⟩ := phase_signExtendRow (I := fun _ => PhaseData) (fun i => i.width) u a
  simpa only [phase_keyBits_signExtend] using
    phase_sourceBlock a fn regs (fun i => bvBits (u i)) 1 (by decide) (by decide)
      (fun i => bvBits ((u i).signExtend (i.width + a))) C R hu
      (by intro i; rw [bvBits_length, if_pos rfl])

/-- Reading the input at a known signed position writes its bit word on register four, retaining
the RAM encoding and the other known registers while allowing the input head to move.

**Proof sketch.** Supply `phase_inputRow` with the known position, encoded input-length word,
ready result register and blank scratch. `phase_state_write` establishes the resulting known
word; `phase_state_inputPos` permits the native input-head endpoint. The native input time and
radius units are dominated by `phase_units`. -/
theorem phase_inputBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → BitVec i.width)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i => Function.update (regs x i) 4
        (some (bvBits (inBitWord i.width x (u i).toInt)))))) := by
  obtain ⟨C, ip, ⟨R⟩⟩ := phase_inputRow (I := fun _ => PhaseData) (fun i => i.width) u
  apply PhaseBlock.ofRow R C
  · intro x i F hp
    obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
    have hh := (encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
      i.origins (F.cfg ())).mp he
    exact ⟨hregs 2 _ (hu x i), hh.2.2.2.2.1,
      phase_frame_ready fn i.cells i.cfg i.origins F he 4 (by decide) (by decide),
      phase_frame_scratch fn i.cells i.cfg i.origins F he⟩
  · intro x i F hp
    have hw : PhaseState a fn
        (fun y j => Function.update (regs y j) 4
          (some (bvBits (inBitWord j.width y (u j).toInt)))) x i
        (F.write 4 (bvBits (inBitWord i.width x (u i).toInt))) := by
      simpa only [phaseState_iff] using phase_state_write a fn regs x i F hp 4
        (by decide) (by decide) (bvBits (inBitWord i.width x (u i).toInt))
        (by rw [bvBits_length, if_neg (by decide)])
    exact phase_state_inputPos a fn _ x i _ hw (ip i F)
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.2.2.1
  · intro x i
    exact Nat.mul_le_mul_left C (phase_units i x).2.2.2.2.2.1

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseControl.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSchedules
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Entry and exit control of instruction phases

A deterministic instruction block gains a fresh entry and two distinct exits. The entry is a
one-step seam dispatch that no transition targets; the unused jump exit is also never targeted.
The nondeterministic embedding has equal transitions under both choices.

## Main definitions

* `WordRAM.Sim.PhaseMachine`: a finite phase with fresh entry and two distinguished exits.

## Main results

* `WordRAM.Sim.phase_toNDTM_fixChoice`: fixing a deterministic embedding recovers its machine.
* `WordRAM.Sim.phase_run_avoids`: a state never targeted by a transition is avoided by a run
  that starts elsewhere.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- Fixing either choice of a deterministically embedded machine recovers the original machine,
by its published initial-state and transition equations. -/
theorem phase_toNDTM_fixChoice {S : Type} (M : MultiTapeTM 8 Bool S) (b : Bool) :
    M.toNDTM.fixChoice b = M := by
  have hq : (M.toNDTM.fixChoice b).q₀ = M.q₀ := by
    rw [NDTM.fixChoice_q₀, MultiTapeTM.toNDTM_q₀]
  have ht : (M.toNDTM.fixChoice b).tr = M.tr := by
    funext q inp work
    rw [NDTM.fixChoice_tr, MultiTapeTM.toNDTM_tr]
  calc
    _ = ⟨(M.toNDTM.fixChoice b).q₀, (M.toNDTM.fixChoice b).tr⟩ := rfl
    _ = ⟨M.q₀, M.tr⟩ := by rw [hq, ht]
    _ = M := rfl

/-- Every configuration is reached from itself in zero time and zero radius, with a vacuous
cut for any chosen exit set. -/
theorem phase_reaches_zero {S : Type} {x : List Bool} (M : MultiTapeTM 8 Bool S)
    (d : Turing.Cfg 8 Bool S x) (X : Set (Option S)) : ReachesWithin M d X 0 0 d := by
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨0, le_rfl, ?_, ?_, MultiTapeTM.runFrom_zero⟩
  · intro s hs
    omega
  · intro s hs j
    have hs' : s = 0 := by omega
    subst s
    rw [MultiTapeTM.runFrom_zero, sub_self, abs_zero]
    exact le_rfl

/-- A state that no transition targets is absent from every time of a run launched elsewhere. -/
theorem phase_run_avoids {S : Type} (M : MultiTapeTM 8 Bool S) (q : S)
    (ht : ∀ s inp work, (M.tr s inp work).state ≠ some q) {x : List Bool}
    (d : Turing.Cfg 8 Bool S x) (hd : d.state ≠ some q) (t : ℕ) :
    (M.runFrom d t).state ≠ some q := by
  cases t with
  | zero => simpa only [MultiTapeTM.runFrom_zero] using hd
  | succ t =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (M.runFrom d t).state with
    | none => rw [MultiTapeTM.step_of_halt hs, hs]; exact fun h => Option.noConfusion h
    | some s =>
      rw [MultiTapeTM.step_of_some hs, Action.apply_state]
      exact ht s _ _

/-- Adding a never-targeted exit to a bounded run's cut is valid when the start is elsewhere. -/
theorem phase_reaches_add_unused {S : Type} {x : List Bool} (M : MultiTapeTM 8 Bool S)
    (d : Turing.Cfg 8 Bool S x) (next jump : S) (B E : ℕ) (post : Turing.Cfg 8 Bool S x)
    (h : ReachesWithin M d {some next} B E post)
    (ht : ∀ q inp work, (M.tr q inp work).state ≠ some jump) (hd : d.state ≠ some jump) :
    ReachesWithin M d {some next, some jump} B E post := by
  obtain ⟨t, hb, hc, he, hr⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t, hb, ?_, he, hr⟩
  intro s hs hm
  rcases (Set.mem_insert_iff.mp hm) with hn | hj
  · exact hc s hs (Set.mem_singleton_iff.mpr hn)
  · exact phase_run_avoids M jump ht d hd s (Set.mem_singleton_iff.mp hj)

/-- A finite instruction phase has a never-targeted entry, choice agreement except possibly at
that entry, distinct next/jump exits and bounded fixed-choice runs. Its postcondition and jump
flag may depend on the fixed choice. -/
structure PhaseMachine (coin : Bool)
    (P : (x : List Bool) → PhaseData → PhaseFrame x → Prop)
    (Q : Bool → (x : List Bool) → PhaseData → PhaseFrame x → Prop)
    (takeJump : Bool → List Bool → PhaseData → Bool) where
  State : Type
  finite : Fintype State
  decEq : DecidableEq State
  machine : NDTM 8 Bool State
  entry : State
  next : State
  jump : State
  constant : ℕ
  distinct : next ≠ jump
  fresh : ∀ b q inp work, (machine.tr b q inp work).state ≠ some entry
  agree : ∀ q, q ≠ entry ∨ coin = false → machine.tr false q = machine.tr true q
  run : ∀ b x i F, P x i F → ∃ G : PhaseFrame x, Q b x i G ∧
    ReachesWithin (machine.fixChoice b) (F.cfg entry) {some next, some jump}
      (constant * phaseTime i x) (constant * phaseSpace i x)
      (G.cfg (if takeJump b x i then jump else next))

/-- Strengthening a phase's precondition and weakening its choice-dependent postcondition
retains its finite machine, entry/exit properties and bounds. -/
theorem PhaseMachine.weaken {coin : Bool}
    {P P' : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {Q Q' : Bool → (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : Bool → List Bool → PhaseData → Bool} (M : PhaseMachine coin P Q flag)
    (hP : ∀ x i F, P' x i F → P x i F)
    (hQ : ∀ b x i F, Q b x i F → Q' b x i F) :
    Nonempty (PhaseMachine coin P' Q' flag) := by
  refine ⟨⟨M.State, M.finite, M.decEq, M.machine, M.entry, M.next, M.jump, M.constant,
    M.distinct, M.fresh, M.agree, ?_⟩⟩
  intro b x i F hp
  obtain ⟨G, hq, hr⟩ := M.run b x i F (hP x i F hp)
  exact ⟨G, hQ b x i G hq, hr⟩

/-- The Boolean halted padding leaf of a seam has no transitions back to either of its left
states: the false state dispatches right and the true state halts. This is shared by the
single-exit and branch phase wrappers. -/
theorem phase_seam_fresh {S : Type} (R : MultiTapeTM 8 Bool S) (entry : S) (v : Bool) :
    ∀ q inp work,
      ((seamCompTM (⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩ :
        MultiTapeTM 8 Bool Bool) false R entry).tr q inp work).state ≠ some (Sum.inl v) := by
  intro q inp work
  cases q with
  | inl q =>
    rw [seamCompTM_tr_inl]
    by_cases hq : q = false
    · rw [if_pos hq]
      intro h
      exact Sum.noConfusion (Option.some.inj h)
    · rw [if_neg hq]
      simp only [Option.map_none]
      exact fun h => Option.noConfusion h
  | inr q =>
    rw [seamCompTM_tr_inr, Action.mapState_state]
    cases hs : (R.tr q inp work).state with
    | none =>
      simp only [Option.map_none]
      exact fun h => Option.noConfusion h
    | some s =>
      simp only [Option.map_some, ne_eq, Option.some.injEq]
      exact Sum.inr_ne_inl

/-- A deterministic single-exit instruction block gains a fresh entry, an unused jump exit,
and equal nondeterministic transitions under both choices.

**Proof sketch.** Use `seamCompTM` to dispatch immediately from the false state of a halted
Boolean leaf into the block; its true state is the unused jump exit. The leaf needs no
computation, and the seam supplies its dispatch. The seam transition equations prove that no
transition targets either left state. `phase_reaches_seq` composes a zero-time prefix contract
with the block, and `phase_reaches_add_unused` supplies the two-exit cut. Embed deterministically
and use `phase_toNDTM_fixChoice` for each slice. -/
theorem phase_machine_ofBlock
    {P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop} (R : PhaseBlock P Q) :
    Nonempty (PhaseMachine false P (fun _ => Q) (fun _ _ _ => false)) := by
  classical
  letI := R.finite
  letI := R.decEq
  let A : MultiTapeTM 8 Bool Bool :=
    ⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let M := seamCompTM A false R.machine R.entry
  have fresh (v : Bool) : ∀ q inp work, (M.tr q inp work).state ≠ some (Sum.inl v) :=
    phase_seam_fresh R.machine R.entry v
  refine ⟨⟨Bool ⊕ R.State, inferInstance, inferInstance, M.toNDTM,
    Sum.inl false, Sum.inr R.exit, Sum.inl true, R.constant + 1, ?_, ?_, ?_, ?_⟩⟩
  · exact Sum.inr_ne_inl
  · intro b q inp work
    rw [MultiTapeTM.toNDTM_tr]
    exact fresh false q inp work
  · intro q hq
    funext inp work
    rw [MultiTapeTM.toNDTM_tr, MultiTapeTM.toNDTM_tr]
  · intro b x i F hp
    obtain ⟨G, hQ, hh, hr⟩ := R.run x i F hp
    have hzero := phase_reaches_zero A (F.cfg false) {some false}
    have hs := phase_reaches_seq A R.machine false false R.entry R.exit {some R.exit}
      F F G 0 0 _ _ hzero hr (Set.mem_singleton_iff.mpr rfl) rfl
    have ht : 0 + 1 + R.constant * phaseTime i x ≤ (R.constant + 1) * phaseTime i x := by
      have hu := (phase_units i x).1
      nlinarith
    have he : 0 + R.constant * phaseSpace i x ≤ (R.constant + 1) * phaseSpace i x := by
      nlinarith
    have hs' : ReachesWithin M (F.cfg (Sum.inl false)) {some (Sum.inr R.exit)}
        ((R.constant + 1) * phaseTime i x) ((R.constant + 1) * phaseSpace i x)
        (G.cfg (Sum.inr R.exit)) := by
      simpa only [M, Set.image_singleton, Option.map_some] using hs.mono ht he
    refine ⟨G, hQ, ?_⟩
    rw [phase_toNDTM_fixChoice]
    apply phase_reaches_add_unused M _ _ _ _ _ _ hs' (fresh true)
    rw [PhaseFrame.cfg_eq]
    intro h
    have h' := Sum.inl.inj (Option.some.inj h)
    cases h'

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseCore.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseLayout
import TCSlib.Complexity.TuringMachine.Build.Contract.Seam
import TCSlib.Complexity.TuringMachine.Build.Contract.Reach
import TCSlib.Complexity.TuringMachine.CfgFacts

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State-independent frames for composing instruction rows

The instruction rows share eight tapes while their finite control types differ. A `PhaseFrame`
records the input head, work tapes, work heads and output, leaving control to the row that runs
on it. `PhaseRow` packages a finite row's bounded contract on these frames.

## Main definitions

* `WordRAM.Sim.PhaseFrame`: the state-independent part of an eight-tape configuration.
* `WordRAM.Sim.PhaseFrame.cfg`, `WordRAM.Sim.PhaseFrame.ofCfg`: install and remove control.
* `WordRAM.Sim.PhaseRow`: a finite row with a precondition and prescribed frame transformation.

## Main results

* `WordRAM.Sim.PhaseFrame.cfg_ofCfg`: reconstruction at a live state.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The input head, eight work tapes and heads, and output, independently of finite control. -/
structure PhaseFrame (x : List Bool) where
  inputPos : Fin (x.length + 2)
  workTapes : Fin 8 → ℤ → Option Bool
  workTapePos : Fin 8 → ℤ
  output : List Bool

/-- Removing control from a configuration retains its four tape and head fields. -/
def PhaseFrame.ofCfg {S : Type} {x : List Bool} (d : Turing.Cfg 8 Bool S x) : PhaseFrame x :=
  ⟨d.inputPos, d.workTapes, d.workTapePos, d.output⟩

attribute [simps (config := { isSimp := false }) inputPos workTapes workTapePos output] PhaseFrame.ofCfg

/-- Removing control retains the input head, work tapes and heads, and output, as an equation. -/
theorem PhaseFrame.ofCfg_eq {S : Type} {x : List Bool} (d : Turing.Cfg 8 Bool S x) :
    PhaseFrame.ofCfg d = ⟨d.inputPos, d.workTapes, d.workTapePos, d.output⟩ := rfl

/-- Installing control at `q` gives a live configuration with exactly the frame's tapes and heads. -/
def PhaseFrame.cfg {S : Type} {x : List Bool} (q : S) (F : PhaseFrame x) : Turing.Cfg 8 Bool S x :=
  ⟨some q, F.inputPos, F.workTapes, F.workTapePos, F.output⟩

attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output] PhaseFrame.cfg

/-- Installing control preserves all four frame fields and sets the live state to `q`. -/
theorem PhaseFrame.cfg_eq {S : Type} {x : List Bool} (q : S) (F : PhaseFrame x) :
    F.cfg q = ⟨some q, F.inputPos, F.workTapes, F.workTapePos, F.output⟩ := rfl

/-- Removing and reinstalling a configuration's live state reconstructs the configuration. -/
theorem PhaseFrame.cfg_ofCfg {S : Type} {x : List Bool} (d : Turing.Cfg 8 Bool S x) (q : S)
    (hd : d.state = some q) : (PhaseFrame.ofCfg d).cfg q = d :=
  Cfg.ext hd.symm rfl rfl rfl rfl

/-- Removing control after installing it recovers the frame. -/
theorem PhaseFrame.ofCfg_cfg {S : Type} {x : List Bool} (q : S) (F : PhaseFrame x) :
    PhaseFrame.ofCfg (F.cfg q) = F := rfl

/-- Renaming the control of a frame configuration only renames its installed live state. -/
theorem PhaseFrame.cfg_mapState {S S' : Type} {x : List Bool} (q : S) (F : PhaseFrame x)
    (f : S → S') : (F.cfg q).mapState f = F.cfg (f q) :=
  Cfg.mapState_eq_of_fields (F.cfg q) f (F.cfg (f q)) rfl rfl rfl rfl rfl

/-- A finite eight-tape row transforms a frame as prescribed, within uniform time and radius
bounds, and restores every work head. The index supplies word sizes and the semantic data read
by the row; the finite machine is uniform in that index and in the input. -/
structure PhaseRow (I : List Bool → Type)
    (pre : ∀ {x : List Bool}, I x → PhaseFrame x → Prop)
    (post : ∀ {x : List Bool}, I x → PhaseFrame x → PhaseFrame x)
    (B E : ∀ {x : List Bool}, I x → ℕ) where
  State : Type
  finite : Fintype State
  decEq : DecidableEq State
  machine : MultiTapeTM 8 Bool State
  entry : State
  exit : State
  heads : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), pre i F →
    (post i F).workTapePos = F.workTapePos
  run : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), pre i F →
    ReachesWithin machine (F.cfg entry) {some exit} (B i) (E i) ((post i F).cfg exit)

/-- A single-exit frame run followed by a frame run with any live exit set composes through
the seam. One dispatch step is added, and restored intermediate heads keep a common center for
the two radius bounds.

**Proof sketch.** Turn the two runs into singleton-precondition contracts with
`Contract.ofReaches`. `Contract.seq` supplies their seam run, cut and envelope, and
`PhaseFrame.cfg_mapState` identifies the state transports. The selected times are bounded by
`Contract.ofReaches_time_le`. Since the intermediate heads are restored, the hull of the two
head intervals lies within the sum of the radii about the original heads. -/
theorem phase_reaches_seq {S₁ S₂ : Type} [DecidableEq S₁] {x : List Bool}
    (M₁ : MultiTapeTM 8 Bool S₁) (M₂ : MultiTapeTM 8 Bool S₂)
    (entry₁ exit₁ : S₁) (entry₂ q₂ : S₂) (X₂ : Set (Option S₂))
    (F F₁ F₂ : PhaseFrame x) (B₁ E₁ B₂ E₂ : ℕ)
    (hr₁ : ReachesWithin M₁ (F.cfg entry₁) {some exit₁} B₁ E₁ (F₁.cfg exit₁))
    (hr₂ : ReachesWithin M₂ (F₁.cfg entry₂) X₂ B₂ E₂ (F₂.cfg q₂))
    (hq₂ : some q₂ ∈ X₂) (hh : F₁.workTapePos = F.workTapePos) :
    ReachesWithin (seamCompTM M₁ exit₁ M₂ entry₂) (F.cfg (Sum.inl entry₁))
      (Option.map Sum.inr '' X₂) (B₁ + 1 + B₂) (E₁ + E₂) (F₂.cfg (Sum.inr q₂)) := by
  classical
  let C₁ := Contract.ofReaches (M := M₁) (entry := entry₁) (X := {some exit₁})
    (fun (_ : Unit) d => d = F.cfg entry₁) (fun _ _ => B₁) (fun _ _ => E₁)
    (fun _ _ => F₁.cfg exit₁)
    (by intro u d hd he; subst d; exact hr₁)
    (by intro u d hd he; exact Set.mem_singleton_iff.mpr rfl)
  let C₂ := Contract.ofReaches (M := M₂) (entry := entry₂) (X := X₂)
    (fun (_ : Unit) d => d = F₁.cfg entry₂) (fun _ _ => B₂) (fun _ _ => E₂)
    (fun _ _ => F₂.cfg q₂)
    (by intro u d hd he; subst d; exact hr₂)
    (by intro u d hd he; exact hq₂)
  have link : ∀ (u : Unit) d, d.state = some entry₁ → C₁.pre u d →
      C₂.pre () ((C₁.post u d).mapState fun _ => entry₂) := by
    intro u d hd he
    simp only [C₁, C₂, Contract.ofReaches_pre, Contract.ofReaches_post,
      PhaseFrame.cfg_mapState]
  let C := Contract.seq C₁ C₂ (fun _ => ()) link
  have hpre : C.pre () (F.cfg (Sum.inl entry₁)) := by
    simp only [C, Contract.seq_pre, C₁, Contract.ofReaches_pre, PhaseFrame.cfg_mapState]
  have hpost : C.post () (F.cfg (Sum.inl entry₁)) = F₂.cfg (Sum.inr q₂) := by
    simp only [C, Contract.seq_post, C₁, C₂, Contract.ofReaches_post,
      PhaseFrame.cfg_mapState]
  have ht₁ : C₁.time () (F.cfg entry₁) ≤ B₁ := by
    apply Contract.ofReaches_time_le
    · rfl
    · rfl
  have ht₂ : C₂.time () (F₁.cfg entry₂) ≤ B₂ := by
    apply Contract.ofReaches_time_le
    · rfl
    · rfl
  have htime : C.time () (F.cfg (Sum.inl entry₁)) ≤ B₁ + 1 + B₂ := by
    simpa only [C, Contract.seq_time, C₁, Contract.ofReaches_post,
      PhaseFrame.cfg_mapState] using Nat.add_le_add (Nat.add_le_add_right ht₁ 1) ht₂
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨C.time () (F.cfg (Sum.inl entry₁)), htime, ?_, ?_, ?_⟩
  · exact C.cut () (F.cfg (Sum.inl entry₁)) rfl hpre
  · intro u hu j
    have he := C.env () (F.cfg (Sum.inl entry₁)) rfl hpre u hu j
    rw [Finset.mem_Icc] at he
    simp only [C, Contract.seq_lo, Contract.seq_hi, C₁, C₂,
      Contract.ofReaches_lo, Contract.ofReaches_hi, Contract.ofReaches_post,
      Cfg.mapState_workTapePos, PhaseFrame.cfg_eq, hh] at he
    rw [PhaseFrame.cfg_eq, abs_le]
    dsimp only at he ⊢
    omega
  · rw [← hpost]
    exact C.run () (F.cfg (Sum.inl entry₁)) rfl hpre

/-- Finite rows compose sequentially with the second precondition tested on the first result,
adding one dispatch step and their radius allowances.

**Proof sketch.** Use `phase_reaches_seq` for the bounded seam run. Both rows restore the work
heads, so their frame transformations compose with the same property. -/
theorem PhaseRow.seq {I : List Bool → Type}
    {P Q : ∀ {x : List Bool}, I x → PhaseFrame x → Prop}
    {f g : ∀ {x : List Bool}, I x → PhaseFrame x → PhaseFrame x}
    {B₁ E₁ B₂ E₂ : ∀ {x : List Bool}, I x → ℕ}
    (R₁ : PhaseRow I P f B₁ E₁) (R₂ : PhaseRow I Q g B₂ E₂) :
    Nonempty (PhaseRow I (fun i F => P i F ∧ Q i (f i F)) (fun i F => g i (f i F))
      (fun i => B₁ i + 1 + B₂ i) (fun i => E₁ i + E₂ i)) := by
  classical
  letI := R₁.finite
  letI := R₁.decEq
  letI := R₂.finite
  letI := R₂.decEq
  refine ⟨⟨R₁.State ⊕ R₂.State, inferInstance, inferInstance,
    seamCompTM R₁.machine R₁.exit R₂.machine R₂.entry, Sum.inl R₁.entry, Sum.inr R₂.exit,
    ?_, ?_⟩⟩
  · intro x i F hp
    rw [R₂.heads i (f i F) hp.2, R₁.heads i F hp.1]
  · intro x i F hp
    simpa only [Set.image_singleton, Option.map_some] using
      phase_reaches_seq R₁.machine R₂.machine R₁.entry R₁.exit R₂.entry R₂.exit
        {some R₂.exit} F (f i F) (g i (f i F)) (B₁ i) (E₁ i) (B₂ i) (E₂ i)
        (R₁.run i F hp.1) (R₂.run i (f i F) hp.2) (Set.mem_singleton_iff.mpr rfl)
        (R₁.heads i F hp.1)

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseEmit.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCoin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Optional output in a live instruction phase

The emit instruction tests its operand and, in function mode, appends the selected bit. A
stationary optional-emission leaf keeps all tapes and heads and returns at a live exit.

## Main definitions

* `WordRAM.Sim.PhaseFrame.emit`: append one bit precisely in function mode.

## Main results

* `WordRAM.Sim.phase_emitAction_apply`: the exact frame of a stationary optional emission.
* `WordRAM.Sim.phase_emitBlock`: a live-return optional-emission block.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- Append the selected bit in function mode, leaving all input/work tapes and heads fixed. -/
def PhaseFrame.emit {x : List Bool} (fn bit : Bool) (F : PhaseFrame x) : PhaseFrame x :=
  { F with output := F.output ++ if fn then [bit] else [] }

attribute [simps (config := { isSimp := false }) inputPos workTapes workTapePos output] PhaseFrame.emit

/-- Optional emission changes only the frame's output by the conditional singleton append. -/
theorem PhaseFrame.emit_eq {x : List Bool} (fn bit : Bool) (F : PhaseFrame x) :
    F.emit fn bit = { F with output := F.output ++ if fn then [bit] else [] } := rfl

/-- A stationary, non-writing action with optional emission installs its live or halted control
and appends just that optional output, leaving all other frame fields unchanged. -/
theorem phase_emitAction_apply {S : Type} {x : List Bool} (d : Turing.Cfg 8 Bool S x)
    (q : Option S) (bit : Option Bool) :
    (⟨0, fun _ => (none, 0), bit, q⟩ : Action 8 Bool S).apply d =
      { d with state := q, output := d.output ++ bit.toList } := by
  apply Cfg.ext
  · rw [Action.apply_state]
  · simp only [Action.apply_inputPos, moveInputPos_zero]
  · funext j
    simp only [Action.apply_workTapes, Option.getD_none, Cfg.workTapeSymbols_eq,
      Function.update_eq_self]
  · funext j
    simp only [Action.apply_workTapePos, SignType.coe_zero, add_zero]
  · rw [Action.apply_output]

/-- One stationary optional emission is a live-return block. There is no native catalog row
with this optional-output and live-return frame contract, so its one action is supplied here.

**Proof sketch.** The Boolean entry advances to the Boolean exit in one step.
`phase_emitAction_apply` gives its exact output and unchanged frame; its initial state differs
from the exit and every work head stays fixed. `PhaseBlock.ofRow` absorbs its one step into the
positive phase unit. -/
theorem phase_emitBlock (fn bit : Bool)
    (P : (x : List Bool) → PhaseData → PhaseFrame x → Prop) :
    Nonempty (PhaseBlock P (fun x i G => ∃ F, P x i F ∧ G = F.emit fn bit)) := by
  let M : MultiTapeTM 8 Bool Bool :=
    ⟨false, fun _ _ _ => ⟨0, fun _ => (none, 0), if fn then some bit else none, some true⟩⟩
  have hstep {x : List Bool} (F : PhaseFrame x) :
      M.runFrom (F.cfg false) 1 = (F.emit fn bit).cfg true := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some (by rw [PhaseFrame.cfg_eq])]
    change (⟨0, fun _ => (none, 0), if fn then some bit else none, some true⟩ :
      Action 8 Bool Bool).apply (F.cfg false) = _
    rw [phase_emitAction_apply]
    cases fn <;> simp only [PhaseFrame.emit_eq, PhaseFrame.cfg_eq, Bool.false_eq_true,
      ↓reduceIte, Option.toList_none, Option.toList_some]
  let row : PhaseRow (fun _ => PhaseData) (fun {x} i F => P x i F)
      (fun _ F => F.emit fn bit) (fun _ => 1) (fun _ => 0) :=
    ⟨Bool, inferInstance, inferInstance, M, false, true,
      (by intro x i F hp; rw [PhaseFrame.emit_eq]), by
        intro x i F hp
        apply (reachesWithin_iff _ _ _ _ _ _).mpr
        refine ⟨1, le_rfl, ?_, ?_, hstep F⟩
        · intro s hs hm
          have hs' : s = 0 := by omega
          subst s
          rw [MultiTapeTM.runFrom_zero, PhaseFrame.cfg_eq] at hm
          have h : (false : Bool) = true := Option.some.inj (Set.mem_singleton_iff.mp hm)
          cases h
        · intro s hs j
          have hs' : s = 0 ∨ s = 1 := by omega
          rcases hs' with rfl | rfl
          · rw [MultiTapeTM.runFrom_zero, sub_self, abs_zero]
            exact le_rfl
          · rw [hstep, PhaseFrame.cfg_eq, PhaseFrame.cfg_eq, PhaseFrame.emit_eq,
              sub_self, abs_zero]
            exact le_rfl⟩
  apply PhaseBlock.ofRow row 1 (by intro x i F hp; exact hp)
  · intro x i F hp
    exact ⟨F, hp, rfl⟩
  · intro x i
    simpa only [one_mul] using (phase_units i x).1
  · intro x i
    exact Nat.zero_le _

/-- A frame emission preserves the encoding and appends its bit to the RAM output, including
verdict mode where the physical output remains empty.

**Proof sketch.** Read the encoding and its tape-layout predicates through their published
readers. The first six clauses are unchanged because all work tapes and heads are fixed.
The output clause follows from the original output equation by cases on function mode. -/
theorem phase_frame_emit_encodes {a W : ℕ} {x : List Bool} (fn bit : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (F : PhaseFrame x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ())) :
    Encodes a fn T { c with out := c.out ++ [bit] } (Function.Embedding.refl _) o
      ((F.emit fn bit).cfg ()) := by
  simp only [encodes_iff, keyTableAt_iff, tableAt_iff, wordAt_iff,
    PhaseFrame.emit_eq, PhaseFrame.cfg_eq] at he ⊢
  obtain ⟨hpos, htable, hkey, hregs, hlen, hscratch, hout⟩ := he
  refine ⟨hpos, htable, hkey, hregs, hlen, hscratch, ?_⟩
  rw [hout]
  cases fn <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil]

/-- The emit instruction has a finite phase with equal choices and a shared next exit. It
appends its operand's nonzero bit in function mode and retains empty physical output in
verdict mode, while encoding the exact extended RAM step in both modes.

**Proof sketch.** Use the shared `phase_testMachine` with the nonzero test. Each branch of
`phase_forkMachine` runs `phase_emitBlock` for its selected bit; both return to the common next
exit. The branch flag identifies that bit with the RAM's nonzero bit, and
`phase_frame_emit_encodes` maintains the encoding in either output mode. `xstep_def` supplies
the next RAM configuration; enlarge its footprint and ignore its control in the encoding. -/
theorem phase_emitMachine (a : ℕ) (fn : Bool) (z : ℤ) (hz : InRange a z) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.emit z) 0 false b x i F) (fun _ _ _ => false)) := by
  let regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i =>
    Function.update (Function.update (fun _ => none) 1 (some (keyBits a i.width z))) 2
      (some (bvBits (i.cfg.mem z)))
  obtain ⟨A⟩ := phase_testMachine a fn z hz .nonzero
  apply phase_forkMachine A
  · intro value
    obtain ⟨E⟩ := phase_emitBlock fn value (fun x i F => ∃ b : Bool,
      PhaseState a fn regs x i F ∧ PhaseTestKind.nonzero.bit (i.cfg.mem z) = value)
    apply E.weaken (by intro x i F hp; exact hp)
    intro x i G he b hb
    obtain ⟨F, ⟨b₀, hp, hflag⟩, rfl⟩ := he
    have hv : decide (i.cfg.mem z ≠ 0) = value := by
      simpa only [PhaseTestKind.bit_eq] using hflag
    have he' := phase_frame_emit_encodes fn value i.cells i.cfg i.origins F
      ((phaseState_iff a fn regs x i F).mp hp).1
    have he'' := phase_encodes_mono fn i.cells (i.cells ∪ (XInstr.emit z).touches i.cfg.mem)
      { i.cfg with out := i.cfg.out ++ [value] } (Function.Embedding.refl _) i.origins
      ((F.emit fn value).cfg ()) he' Finset.subset_union_left
    apply (phasePost_iff a fn (.emit z) 0 false b x i (F.emit fn value)).mpr
    intro P ρ hf hc
    let c' : XCfg i.width := { i.cfg with
      pc := i.cfg.pc + 1
      out := i.cfg.out ++ [value] }
    refine ⟨c', ?_, ?_, rfl⟩
    · simp only [c', xstep_def, hf, hv]
    · exact (phase_encodes_congr fn _ { i.cfg with out := i.cfg.out ++ [value] } c'
        (Function.Embedding.refl _) i.origins ((F.emit fn value).cfg ())
        ((F.emit fn value).cfg ()) rfl rfl rfl rfl rfl).mp he''
  · intro b x i F G hp hq
    exact phase_encoded_heads fn i.cells i.cells i.cfg i.cfg i.origins F G
      ((phaseState_iff a fn _ x i F).mp hp).1 ((phaseState_iff a fn regs x i G).mp hq).1

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseFork.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseHost
import TCSlib.Complexity.TuringMachine.Build.NDHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Returning from two instruction continuations

The registered nondeterministic phase host runs a source phase, dispatches its selected live
exit to one of two deterministic continuation blocks, and joins their returns at one next exit.
No transition returns to the source entry. This control arrangement is shared by the coin and
output instruction phases.

## Main definitions

* `WordRAM.Sim.PhaseForkNode`: source, Boolean continuation and common return phases.

## Main results

* `WordRAM.Sim.phase_forkMachine`: compose a finite two-exit source with its continuations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- The three kinds of tagged phase in a two-continuation instruction: its source, a selected
Boolean continuation and the shared return phase. -/
inductive PhaseForkNode where
  | source
  | branch (value : Bool)
  | done
  deriving DecidableEq, Fintype

/-- A source phase and two deterministic continuations join at a common next exit. Only the
source entry can have choice-dependent transitions, and only if its own coin flag permits it.

**Proof sketch.** Instantiate `NDTM.phaseHostND` on the source, two continuation blocks and a
halted Boolean return leaf. Redirect the source's next/jump exits to their continuation entries
and both continuation exits to the same return state. The host transition reader transfers
freshness and choice agreement by phase tags. For a fixed slice,
`phase_reaches_inPhase` places the source and selected continuation through `Contract.inPhase`;
`phase_reaches_trans` concatenates their runs. The two dispatches are absorbed into the sum of
the source and both continuation constants plus two. -/
theorem phase_forkMachine {coin : Bool}
    {P : (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {Q R : Bool → (x : List Bool) → PhaseData → PhaseFrame x → Prop}
    {flag : Bool → List Bool → PhaseData → Bool} (A : PhaseMachine coin P Q flag)
    (banks : ∀ value : Bool, Nonempty (PhaseBlock
      (fun x i F => ∃ b : Bool, Q b x i F ∧ flag b x i = value)
      (fun x i F => ∀ b : Bool, flag b x i = value → R b x i F)))
    (heads : ∀ b x i F G, P x i F → Q b x i G → G.workTapePos = F.workTapePos) :
    Nonempty (PhaseMachine coin P R (fun _ _ _ => false)) := by
  classical
  let B := fun value => Classical.choice (banks value)
  let Ph : PhaseForkNode → Type
    | .source => A.State
    | .branch value => (B value).State
    | .done => Bool
  letI : ∀ p, Fintype (Ph p) := fun p => match p with
    | .source => A.finite
    | .branch value => (B value).finite
    | .done => inferInstance
  letI : ∀ p, DecidableEq (Ph p) := fun p => match p with
    | .source => A.decEq
    | .branch value => (B value).decEq
    | .done => inferInstance
  let Nf : (p : PhaseForkNode) → NDTM 8 Bool (Ph p)
    | .source => A.machine
    | .branch value => (B value).machine.toNDTM
    | .done => ⟨false, fun _ _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let red : (p : PhaseForkNode) → Ph p → Option (Σ p, Ph p)
    | .source, q =>
      if q = A.jump then some ⟨.branch true, (B true).entry⟩
      else if q = A.next then some ⟨.branch false, (B false).entry⟩ else none
    | .branch value, q => if q = (B value).exit then some ⟨.done, false⟩ else none
    | .done, _ => none
  let q₀ : Σ p, Ph p := ⟨.source, A.entry⟩
  let N := NDTM.phaseHostND Nf q₀ red
  let Mf := fun b p => (Nf p).fixChoice b
  let Y : Set (Option (Σ p, Ph p)) := {some ⟨.done, false⟩, some ⟨.done, true⟩}
  have ynone : none ∉ Y := by
    intro h
    rcases Set.mem_insert_iff.mp h with h | h
    · exact Option.noConfusion h
    · exact Option.noConfusion (Set.mem_singleton_iff.mp h)
  have ytag (p : PhaseForkNode) (hp : p ≠ .done) :
      ∀ r, some r ∈ Y → r.1 ≠ p := by
    intro r hr
    simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq] at hr
    rcases hr with rfl | rfl <;> exact fun h => hp h.symm
  have redtag : ∀ p q target, red p q = some target → target.1 ≠ .source := by
    intro p q target h
    cases p <;> simp only [red] at h <;> (try split_ifs at h) <;>
      cases h <;> intro hf <;> cases hf
  have source_red : ∀ q, some q ∉ ({some A.next, some A.jump} : Set (Option A.State)) →
      red .source q = none := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq, not_or] at hq
    simp only [red, if_neg hq.2, if_neg hq.1]
  have source_some : ∀ q, some q ∈ ({some A.next, some A.jump} : Set (Option A.State)) →
      ∃ target, red .source q = some target ∧ target.1 ≠ .source := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq] at hq
    rcases hq with rfl | rfl
    · refine ⟨⟨.branch false, (B false).entry⟩, ?_, by intro h; cases h⟩
      simp only [red, A.distinct, ↓reduceIte]
    · refine ⟨⟨.branch true, (B true).entry⟩, ?_, by intro h; cases h⟩
      simp only [red, ↓reduceIte]
  have source_target (value : Bool) :
      red .source (if value then A.jump else A.next) = some ⟨.branch value, (B value).entry⟩ := by
    cases value <;> simp only [Bool.false_eq_true, red, A.distinct, ↓reduceIte]
  have source_none : none ∉ ({some A.next, some A.jump} : Set (Option A.State)) := by
    intro h
    rcases Set.mem_insert_iff.mp h with h | h
    · exact Option.noConfusion h
    · exact Option.noConfusion (Set.mem_singleton_iff.mp h)
  refine ⟨⟨(Σ p, Ph p), inferInstance, inferInstance, N, q₀,
    ⟨.done, false⟩, ⟨.done, true⟩,
    A.constant + (B false).constant + (B true).constant + 2, ?_, ?_, ?_, ?_⟩⟩
  · intro h
    have h' := sigma_mk_injective h
    cases h'
  · intro b q inp work
    rcases q with ⟨p, q⟩
    simp only [N, NDTM.phaseHostND_tr]
    cases hred : red p q with
    | some target =>
      intro h
      exact redtag p q target hred (congrArg Sigma.fst (Option.some.inj h))
    | none =>
      simp only [Action.mapState_state]
      cases p with
      | source =>
        intro h
        obtain ⟨s, hs, hq⟩ := Option.map_eq_some_iff.mp h
        have he : s = A.entry := sigma_mk_injective hq
        exact A.fresh b q inp work (hs.trans (congrArg some he))
      | branch value =>
        intro h
        obtain ⟨s, hs, hq⟩ := Option.map_eq_some_iff.mp h
        have bad := congrArg Sigma.fst hq
        cases bad
      | done =>
        intro h
        obtain ⟨s, hs, hq⟩ := Option.map_eq_some_iff.mp h
        have bad := congrArg Sigma.fst hq
        cases bad
  · intro q hq
    rcases q with ⟨p, q⟩
    funext inp work
    simp only [N, NDTM.phaseHostND_tr]
    cases hred : red p q with
    | some target => rfl
    | none =>
      cases p with
      | source =>
        have ha : q ≠ A.entry ∨ coin = false := by
          rcases hq with hq | hc
          · left
            intro h
            apply hq
            subst q
            rfl
          · exact Or.inr hc
        exact congrArg (fun a : Action 8 Bool A.State =>
          a.mapState (fun s => (⟨.source, s⟩ : Σ p, Ph p)))
          (congrFun (congrFun (A.agree q ha) inp) work)
      | branch value => simp only [Nf, MultiTapeTM.toNDTM_tr]
      | done => rfl
  · intro b x i F hp
    obtain ⟨G, hq, hrA⟩ := A.run b x i F hp
    let value := flag b x i
    obtain ⟨H, hr, hh, hrB⟩ := (B value).run x i G ⟨b, hq, rfl⟩
    have hs := phase_reaches_inPhase (Mf b) q₀ red .source A.entry
      (if flag b x i then A.jump else A.next) {some A.next, some A.jump} F G
      (A.constant * phaseTime i x) (A.constant * phaseSpace i x) hrA
      (by simpa only [Set.pair_comm] using phase_branch_mem A.jump A.next (flag b x i))
      source_none source_red source_some ⟨.branch value, (B value).entry⟩
      (source_target value) Y ynone (ytag .source (by decide))
    have hb : ReachesWithin (Mf b (.branch value)) (G.cfg (B value).entry)
        {some (B value).exit} ((B value).constant * phaseTime i x)
        ((B value).constant * phaseSpace i x) (H.cfg (B value).exit) := by
      simpa only [Mf, Nf, phase_toNDTM_fixChoice] using hrB
    have ht := phase_reaches_inPhase (Mf b) q₀ red (.branch value) (B value).entry
      (B value).exit {some (B value).exit} G H ((B value).constant * phaseTime i x)
      ((B value).constant * phaseSpace i x) hb (Set.mem_singleton_iff.mpr rfl)
      (by intro h; exact Option.noConfusion (Set.mem_singleton_iff.mp h))
      (by
        intro q hq
        simp only [Set.mem_singleton_iff, Option.some.injEq] at hq
        simp only [red, if_neg hq])
      (by
        intro q hq
        have he : q = (B value).exit := Option.some.inj (Set.mem_singleton_iff.mp hq)
        subst q
        exact ⟨⟨.done, false⟩, by simp only [red, ↓reduceIte], by intro h; cases h⟩)
      ⟨.done, false⟩ (by simp only [red, ↓reduceIte]) Y ynone
      (ytag (.branch value) (by intro h; cases h))
    have hrun := phase_reaches_trans (phaseHostTM (Mf b) q₀ red) q₀
      ⟨.branch value, (B value).entry⟩ ⟨.done, false⟩ Y F G H _ _ _ _ hs ht
      (heads b x i F G hp hq)
    have hc : (B value).constant ≤ (B false).constant + (B true).constant := by
      cases value <;> omega
    have htime : (A.constant * phaseTime i x + 1) + ((B value).constant * phaseTime i x + 1) ≤
        (A.constant + (B false).constant + (B true).constant + 2) * phaseTime i x := by
      have hu := (phase_units i x).1
      have hm := Nat.mul_le_mul_right (phaseTime i x) hc
      nlinarith
    have hspace : A.constant * phaseSpace i x + (B value).constant * phaseSpace i x ≤
        (A.constant + (B false).constant + (B true).constant + 2) * phaseSpace i x := by
      have hm := Nat.mul_le_mul_right (phaseSpace i x) hc
      nlinarith
    refine ⟨H, hr b rfl, ?_⟩
    simpa only [N, NDTM.phaseHostND_fixChoice, Mf, Y] using hrun.mono htime hspace

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseHost.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseBranchMachines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Frame contracts inside the registered phase host

A native frame contract runs inside a tagged phase until its live exit, then dispatches to its
redirect target. Every host exit set confined to other phases is avoided before that endpoint.
The bounded-run composition lemma also concatenates two contracts of the same host.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_reaches_inPhase`: place a bounded frame contract in the phase host.
* `WordRAM.Sim.phase_reaches_trans`: concatenate bounded runs of the same machine.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- Binding a frame's live control to one live target installs that target without changing
any frame fields. -/
theorem phase_frame_bindState {S H : Type} {x : List Bool} (F : PhaseFrame x)
    (q : S) (r : H) (f : S → Option H) (hf : f q = some r) :
    (F.cfg q).bindState f = F.cfg r := by
  apply Cfg.ext
  · simpa only [Cfg.bindState_state, PhaseFrame.cfg_eq] using hf
  · simp only [Cfg.bindState_inputPos, PhaseFrame.cfg_eq]
  · funext j z
    simp only [Cfg.bindState_workTapes, PhaseFrame.cfg_eq]
  · funext j
    simp only [Cfg.bindState_workTapePos, PhaseFrame.cfg_eq]
  · simp only [Cfg.bindState_output, PhaseFrame.cfg_eq]

/-- A native bounded run dispatches once inside the phase host, retaining its radius and
avoiding any host exit set consisting entirely of live states in other phases.

**Proof sketch.** Turn the native row into `Contract.ofReaches` and place it with
`Contract.inPhase`. Its published time, post and envelope equations give the endpoint and
bounds. For the possibly larger host cut, `phaseHostTM_run_le` tags the native prefix by its
source phase; it cannot meet an exit tagged by another phase. -/
theorem phase_reaches_inPhase {I : Type} {Ph : I → Type} {x : List Bool}
    (Mf : (p : I) → MultiTapeTM 8 Bool (Ph p)) (q₀ : Σ p, Ph p)
    (red : (p : I) → Ph p → Option (Σ p, Ph p)) (p : I) (entry exit : Ph p)
    (X : Set (Option (Ph p))) (F G : PhaseFrame x) (B E : ℕ)
    (hr : ReachesWithin (Mf p) (F.cfg entry) X B E (G.cfg exit))
    (hx : some exit ∈ X) (hnone : none ∉ X)
    (hred : ∀ q, some q ∉ X → red p q = none)
    (hsome : ∀ q, some q ∈ X → ∃ r, red p q = some r ∧ r.1 ≠ p)
    (target : Σ p, Ph p) (htarget : red p exit = some target)
    (Y : Set (Option (Σ p, Ph p))) (hYnone : none ∉ Y)
    (hYtag : ∀ r, some r ∈ Y → r.1 ≠ p) :
    ReachesWithin (phaseHostTM Mf q₀ red) (F.cfg ⟨p, entry⟩) Y (B + 1) E
      (G.cfg target) := by
  classical
  let C := Contract.ofReaches (M := Mf p) (entry := entry) (X := X)
    (fun (_ : Unit) d => d = F.cfg entry) (fun _ _ => B) (fun _ _ => E)
    (fun _ _ => G.cfg exit)
    (by intro u d hd he; subst d; exact hr)
    (by intro u d hd he; simpa only [PhaseFrame.cfg_eq] using hx)
  let H := Contract.inPhase Mf q₀ red p C hnone hred hsome
  have hpre : H.pre () (F.cfg ⟨p, entry⟩) := by
    simp only [H, Contract.inPhase_pre, C, Contract.ofReaches_pre, PhaseFrame.cfg_mapState]
  have hpost : H.post () (F.cfg ⟨p, entry⟩) = G.cfg target := by
    simp only [H, Contract.inPhase_post, C, Contract.ofReaches_post, PhaseFrame.cfg_mapState]
    exact phase_frame_bindState G exit target (red p) htarget
  have hF : (F.cfg entry).state = some entry := by simp only [PhaseFrame.cfg_eq]
  have hH : (F.cfg (⟨p, entry⟩ : Σ p, Ph p)).state = some ⟨p, entry⟩ := by
    simp only [PhaseFrame.cfg_eq]
  have hpC : C.pre () (F.cfg entry) := by simp only [C, Contract.ofReaches_pre]
  have ht : C.time () (F.cfg entry) ≤ B := by
    apply Contract.ofReaches_time_le
    · exact hF
    · rfl
  have htime : H.time () (F.cfg ⟨p, entry⟩) = C.time () (F.cfg entry) + 1 := by
    simp only [H, Contract.inPhase_time, PhaseFrame.cfg_mapState]
  have hguard : ∀ u < C.time () (F.cfg entry), ∀ q,
      ((Mf p).runFrom (F.cfg entry) u).state = some q → red p q = none := by
    intro u hu q hq
    apply hred q
    intro hm
    exact C.cut () (F.cfg entry) hF hpC u hu (by rw [hq]; exact hm)
  have hprefix := phaseHostTM_run_le Mf q₀ red p (F.cfg entry)
    (C.time () (F.cfg entry)) hguard
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨H.time () (F.cfg ⟨p, entry⟩), by rw [htime]; omega, ?_, ?_, ?_⟩
  · intro u hu hm
    rw [htime] at hu
    have hpref := hprefix u (by omega)
    rw [PhaseFrame.cfg_mapState] at hpref
    rw [hpref, Cfg.mapState_state] at hm
    cases hs : ((Mf p).runFrom (F.cfg entry) u).state with
    | none => exact hYnone (by simpa only [hs, Option.map_none] using hm)
    | some q =>
      exact hYtag ⟨p, q⟩ (by simpa only [hs, Option.map_some] using hm) rfl
  · intro u hu j
    have he := H.env () (F.cfg ⟨p, entry⟩) hH hpre u hu j
    rw [Finset.mem_Icc] at he
    simp only [H, Contract.inPhase_lo, Contract.inPhase_hi, C, Contract.ofReaches_lo,
      Contract.ofReaches_hi, Cfg.mapState_workTapePos, PhaseFrame.cfg_eq] at he
    rw [PhaseFrame.cfg_eq, abs_le]
    dsimp only at he ⊢
    omega
  · rw [← hpost]
    exact H.run () (F.cfg ⟨p, entry⟩) hH hpre

/-- Two bounded runs of the same machine concatenate without a dispatch step when their frame
endpoints agree. Restored intermediate heads give the sum of their radius allowances.

**Proof sketch.** Split a prefix time before or after the first witness. `runFrom_add` reduces
the latter part to the second run, giving its cut and endpoint. Restoration of the
intermediate heads identifies the two radius centers, and each allowance fits their sum. -/
theorem phase_reaches_trans {S : Type} {x : List Bool} (M : MultiTapeTM 8 Bool S)
    (q₀ q₁ q₂ : S) (X : Set (Option S)) (F G H : PhaseFrame x) (B₁ E₁ B₂ E₂ : ℕ)
    (h₁ : ReachesWithin M (F.cfg q₀) X B₁ E₁ (G.cfg q₁))
    (h₂ : ReachesWithin M (G.cfg q₁) X B₂ E₂ (H.cfg q₂))
    (hh : G.workTapePos = F.workTapePos) :
    ReachesWithin M (F.cfg q₀) X (B₁ + B₂) (E₁ + E₂) (H.cfg q₂) := by
  obtain ⟨t₁, ht₁, hc₁, he₁, hr₁⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h₁
  obtain ⟨t₂, ht₂, hc₂, he₂, hr₂⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h₂
  have tail (u : ℕ) : M.runFrom (F.cfg q₀) (t₁ + u) = M.runFrom (G.cfg q₁) u := by
    rw [MultiTapeTM.runFrom_add, hr₁]
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t₁ + t₂, by omega, ?_, ?_, by rw [tail, hr₂]⟩
  · intro u hu
    by_cases h : u < t₁
    · exact hc₁ u h
    · have hu' : u = t₁ + (u - t₁) := by omega
      rw [hu', tail]
      exact hc₂ (u - t₁) (by omega)
  · intro u hu j
    by_cases h : u ≤ t₁
    · exact (he₁ u h j).trans (by exact_mod_cast Nat.le_add_right E₁ E₂)
    · have hu' : u = t₁ + (u - t₁) := by omega
      rw [hu', tail]
      have he := he₂ (u - t₁) (by omega) j
      simp only [PhaseFrame.cfg_eq, hh] at he ⊢
      exact he.trans (by exact_mod_cast Nat.le_add_left E₂ E₁)

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseInput.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseMemory

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Input-bit rows of an instruction phase

The input row reads a position from word register two, uses the input-length word on tape five,
and writes the resulting bit word to register four. Its input-head endpoint may vary, while all
work heads return to their origins.

## Main definitions

* `WordRAM.Sim.phaseInputBank`: the position, length, result and scratch tape bank.

## Main results

* `WordRAM.Sim.phase_inputRow`: place the native input-bit row on eight tapes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The input-bit bank reads the position on tape two and length on tape five, writes tape four,
and uses scratch tapes six and seven. -/
def phaseInputBank : Fin 5 ↪ Fin 8 := ⟨![2, 5, 4, 6, 7], by decide⟩

/-- The input bank sends its five source indices to `2, 5, 4, 6, 7`, respectively. -/
theorem phaseInputBank_apply (r : Fin 5) : phaseInputBank r = ![2, 5, 4, 6, 7] r := rfl

/-- The input-bit row writes the bit word to register four, with linear input-length time and
logarithmic input-length radius. Its existential input-head function records the native row's
unconstrained final input-head location.

**Proof sketch.** Choose `exists_inputBitTM`. Register readiness supplies the old destination
word, and the selection lemmas supply the position, input-length and scratch layouts. Choose
its final input position under the precondition, with the original position as a total default.
`phase_nativeRow` and `phase_embed_wordWrite` place the exact native endpoint. -/
theorem phase_inputRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u : ∀ {x : List Bool} (i : I x), BitVec (width i)) :
    ∃ (C : ℕ) (ip : ∀ {x : List Bool}, I x → PhaseFrame x → Fin (x.length + 2)),
      Nonempty (PhaseRow I
        (fun {x} i F => WordAt (F.cfg ()) 2 (bvBits (u i)) ∧
          WordAt (F.cfg ()) 5 (Nat.bits x.length) ∧ PhaseReady (width i) 4 F ∧ PhaseScratch F)
        (fun {x} i F => { F.write 4 (bvBits (inBitWord (width i) x (u i).toInt)) with
          inputPos := ip i F })
        (fun {x} i => C * (width i + x.length + 1))
        (fun {x} i => C * (width i + (Nat.bits x.length).length + 1))) := by
  classical
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := exists_inputBitTM
  letI := hfin
  letI := hdec
  let pre : ∀ {x : List Bool}, I x → PhaseFrame x → Prop := fun {x} i F =>
    WordAt (F.cfg ()) 2 (bvBits (u i)) ∧ WordAt (F.cfg ()) 5 (Nat.bits x.length) ∧
      PhaseReady (width i) 4 F ∧ PhaseScratch F
  have hn : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), pre i F →
      ∃ ip : Fin (x.length + 2),
        ReachesWithin M ((F.cfg entry).select phaseInputBank) {some exit}
          (C * (width i + x.length + 1)) (C * (width i + (Nat.bits x.length).length + 1))
          { ((F.cfg entry).select phaseInputBank) with
            state := some exit
            inputPos := ip
            workTapes := wordWrite ((F.cfg entry).select phaseInputBank) 2
              (bvBits (inBitWord (width i) x (u i).toInt)) } := by
    intro x i F hp
    obtain ⟨w, hw, hwlen⟩ := (phaseReady_iff (width i) 4 F).mp hp.2.2.1
    obtain ⟨ip, hr⟩ := hM (u i) w ((F.cfg entry).select phaseInputBank)
      (by simp only [Cfg.select_eq, PhaseFrame.cfg_eq])
      ((phase_wordAt_select phaseInputBank (F.cfg entry) 0 _).mpr
        ((phase_wordAt_frame F entry 2 _).mpr hp.1))
      ((phase_wordAt_select phaseInputBank (F.cfg entry) 1 _).mpr
        ((phase_wordAt_frame F entry 5 _).mpr hp.2.1))
      ((phase_wordAt_select phaseInputBank (F.cfg entry) 2 w).mpr
        ((phase_wordAt_frame F entry 4 w).mpr hw))
      hwlen (phase_scratch_select phaseInputBank F entry (by decide) hp.2.2.2)
    exact ⟨ip, by simpa only [inBitWord_def] using hr⟩
  let ip : ∀ {x : List Bool}, I x → PhaseFrame x → Fin (x.length + 2) :=
    fun i F => if hp : pre i F then Classical.choose (hn i F hp) else F.inputPos
  refine ⟨C, ip, ?_⟩
  apply phase_nativeRow (I := I) pre _ _ _ S M entry exit phaseInputBank
    (fun {x} i F => { ((F.cfg entry).select phaseInputBank) with
      state := some exit
      inputPos := ip i F
      workTapes := wordWrite ((F.cfg entry).select phaseInputBank) 2
        (bvBits (inBitWord (width i) x (u i).toInt)) })
  · intro x i F hp
    simpa only [ip, dif_pos hp] using Classical.choose_spec (hn i F hp)
  · intro x i F hp
    simpa only [PhaseFrame.write_eq, PhaseFrame.cfg_eq, Cfg.select_eq,
      phase_wordWrite_as_update, phaseInputBank_apply] using
      phase_embed_wordWrite phaseInputBank (F.cfg entry) (some exit) (ip i F) 2
        (bvBits (inBitWord (width i) x (u i).toInt))
  · intro x i F hp
    simp only [PhaseFrame.write_eq]

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseInvariant.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Preservation of the RAM encoding by instruction rows

Register writes preserve the represented memory, and a keyed assignment updates exactly one
cell. The invariant includes the word registers, input-length word, blank scratch tapes and
mode-dependent output, so these preservation facts can be used between every pair of rows.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_encodes_mono`: enlarge the allowed footprint without changing tape data.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- Enlarging the allowed memory footprint preserves the encoded configuration. -/
theorem phase_encodes_mono {K a W : ℕ} {S : Type} {x : List Bool} (fn : Bool)
    (T U : Finset ℤ) (c : XCfg W) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ)
    (d : Turing.Cfg K Bool S x) (he : Encodes a fn T c σ o d) (hTU : T ⊆ U) :
    Encodes a fn U c σ o d := by
  obtain ⟨h₀, ⟨es, h₁, h₂⟩, h₃, h₄, h₅, h₆, h₇⟩ := (encodes_iff a fn T c σ o d).mp he
  exact (encodes_iff a fn U c σ o d).mpr
    ⟨h₀, ⟨es, h₁, tableOf_mono h₂ hTU⟩, h₃, h₄, h₅, h₆, h₇⟩

/-- Writing a word of the prescribed width into any of the four registers preserves the
encoded RAM configuration.

**Proof sketch.** Read the seven clauses of `encodes_iff`. The written register has its new
word by `phase_wordAt_write`; every other tape is unchanged by `phase_wordWrite_as_update`
and `Function.update_of_ne`. The represented table and blank scratch tapes are therefore
preserved, as are all heads and the output. -/
theorem phase_encodes_wordWrite {a W : ℕ} {S : Type} {x : List Bool} (fn : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o d) (r : Fin 8)
    (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4) (w : List Bool)
    (hw : w.length = if r = 1 then W + a else W) :
    Encodes a fn T c (Function.Embedding.refl _) o
      { d with workTapes := wordWrite d r w } := by
  obtain ⟨hpos, ⟨es, htable, hmem⟩, hkey, hregs, hlen, hscratch, hout⟩ :=
    (encodes_iff a fn T c (Function.Embedding.refl _) o d).mp he
  have same (j : Fin 8) (hj : j ≠ r) : wordWrite d r w j = d.workTapes j := by
    rw [phase_wordWrite_as_update, Function.update_of_ne hj]
  have keep {j : Fin 8} {v : List Bool} (hj : j ≠ r) (hv : WordAt d j v) :
      WordAt { d with workTapes := wordWrite d r w } j v := by
    exact (phase_wordAt_congr d { d with workTapes := wordWrite d r w } j v
      (same j hj).symm rfl).mp hv
  apply (encodes_iff a fn T c (Function.Embedding.refl _) o _).mpr
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, hout⟩
  · refine ⟨es, ?_, hmem⟩
    exact (phase_keyTableAt_congr d _ 0 (o 0) es
      (same 0 (by intro h; have := congrArg Fin.val h; omega)).symm).mp htable
  · by_cases hr : r = 1
    · subst r
      rw [if_pos rfl] at hw
      obtain ⟨v, hv, hvlen⟩ := hkey
      exact ⟨w, phase_wordAt_write d 1 v w hv (hw.trans hvlen.symm), hw⟩
    · obtain ⟨v, hv, hvlen⟩ := hkey
      exact ⟨v, keep (Ne.symm hr) hv, hvlen⟩
  · intro j hj₀ hj₁
    by_cases hj : j = r
    · subst j
      have hr : r ≠ 1 := by intro h; have := congrArg Fin.val h; omega
      rw [if_neg hr] at hw
      obtain ⟨v, hv, hvlen⟩ := hregs r hj₀ hj₁
      exact ⟨w, phase_wordAt_write d r v w hv (hw.trans hvlen.symm), hw⟩
    · obtain ⟨v, hv, hvlen⟩ := hregs j hj₀ hj₁
      exact ⟨v, keep hj hv, hvlen⟩
  · exact keep (j := 5) (by intro h; have := congrArg Fin.val h; omega) hlen
  · intro j hj q
    change wordWrite d r w j q = none
    rw [same j (by intro h; have := congrArg Fin.val h; omega)]
    exact hscratch j hj q

/-- A keyed assignment to an in-range cell preserves the full encoding, updates that cell's
memory word, and adds the cell to the allowed footprint.

**Proof sketch.** `phase_keyTableAt_write` and `phase_keyAssign_layout_mono` establish the new
physical table; `tableOf_keyAssign` establishes its memory meaning. All other tapes are framed
by `phase_keyTableWrite_as_update` and `Function.update_of_ne`, so their words and scratch
blankness are preserved. Heads and output do not change. -/
theorem phase_encodes_keyAssign {a W : ℕ} {S : Type} {x : List Bool} (fn : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o d)
    (es : List (List Bool × List Bool)) (htable : KeyTableAt d 0 (o 0) es)
    (hmem : TableOf a W T c.mem es) (z : ℤ) (hz : InRange (W + a) z) (v : BitVec W) :
    Encodes a fn (insert z T) { c with mem := Function.update c.mem z v }
      (Function.Embedding.refl _) o
      { d with workTapes := keyTableWrite d 0 (o 0) (keyAssign es (keyBits a W z) (bvBits v)) } := by
  obtain ⟨hpos, _, hkey, hregs, hlen, hscratch, hout⟩ :=
    (encodes_iff a fn T c (Function.Embedding.refl _) o d).mp he
  let es' := keyAssign es (keyBits a W z) (bvBits v)
  let d' := { d with workTapes := keyTableWrite d 0 (o 0) es' }
  have same (j : Fin 8) (hj : j ≠ 0) : keyTableWrite d 0 (o 0) es' j = d.workTapes j := by
    rw [phase_keyTableWrite_as_update, Function.update_of_ne hj]
  have keep {j : Fin 8} {w : List Bool} (hj : j ≠ 0) (hw : WordAt d j w) :
      WordAt d' j w :=
    (phase_wordAt_congr d d' j w (same j hj).symm rfl).mp hw
  apply (encodes_iff a fn (insert z T) { c with mem := Function.update c.mem z v }
    (Function.Embedding.refl _) o d').mpr
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, hout⟩
  · exact ⟨es', phase_keyTableAt_write d 0 (o 0) es es' htable
      (phase_keyAssign_layout_mono hmem hz v), tableOf_keyAssign hmem hz v⟩
  · obtain ⟨w, hw, hwidth⟩ := hkey
    exact ⟨w, keep (j := 1) (by decide) hw, hwidth⟩
  · intro j hj₀ hj₁
    obtain ⟨w, hw, hwidth⟩ := hregs j hj₀ hj₁
    exact ⟨w, keep (j := j) (by intro h; have := congrArg Fin.val h; omega) hw, hwidth⟩
  · exact keep (j := 5) (by decide) hlen
  · intro j hj q
    change keyTableWrite d 0 (o 0) es' j q = none
    rw [same j (by intro h; have := congrArg Fin.val h; omega)]
    exact hscratch j hj q

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseLayout.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseTable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Address ranges and tape layouts of instruction phases

The memory-table invariant is used at the width of the keys. These lemmas extend the immediate
and computed address ranges to that width and bound the physical layout of a represented table.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_inRange_mono`: increasing the width preserves the signed range.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A cell in the signed range of a width is in the signed range of every larger width. -/
theorem phase_inRange_mono {m n : ℕ} {z : ℤ} (hmn : m ≤ n) (hz : InRange m z) :
    InRange n z := by
  have hp : (2 : ℤ) ^ m ≤ 2 ^ n := pow_le_pow_right₀ (by omega) hmn
  obtain ⟨hl, hu⟩ := (inRange_iff m z).mp hz
  exact (inRange_iff n z).mpr ⟨by linarith, by linarith⟩

/-- The signed value of a word lies in the signed range of its width, including width zero. -/
theorem phase_toInt_inRange {W : ℕ} (u : BitVec W) : InRange W u.toInt := by
  exact (inRange_iff W u.toInt).mpr ⟨BitVec.le_two_mul_toInt, BitVec.two_mul_toInt_lt⟩

/-- A program immediate satisfying `ImmBound` lies in the range of the extended key width. -/
theorem phase_immediate_inRange {a W : ℕ} {ins : XInstr} (h : ImmBound a ins) {z : ℤ}
    (hz : z ∈ immediates ins) : InRange (W + a) z := by
  exact phase_inRange_mono (by omega) ((immBound_iff a ins).mp h z hz)

/-- A computed address, the signed value of a word, fits the extended key width. -/
theorem phase_computed_inRange {W : ℕ} (a : ℕ) (u : BitVec W) :
    InRange (W + a) u.toInt := by
  exact phase_inRange_mono (by omega) (phase_toInt_inRange u)

/-- Sign-extending a word writes exactly the key of its signed address. -/
theorem phase_keyBits_signExtend {W : ℕ} (a : ℕ) (u : BitVec W) :
    keyBits a W u.toInt = bvBits (u.signExtend (W + a)) := by
  rw [keyBits_def]
  apply congrArg bvBits
  apply BitVec.toInt_inj.mp
  rw [toInt_wd (phase_computed_inRange a u), BitVec.toInt_signExtend_of_le (by omega)]

/-- A keyed table with key width `K` and value width `V` occupies one header cell and
`K + V + 4` cells per entry, including markers and separators.

**Proof sketch.** Apply `joinFields_length` to the nonempty header-and-fields list read through
`tableFields_eq`. `keyFields_def` gives two marked fields per entry. The sum of their lengths
is `|es| * (K + V + 2)`, and there are `2 * |es|` separators after the header. -/
theorem phase_keyTableLength (es : List (List Bool × List Bool)) (K V : ℕ)
    (hw : ∀ e ∈ es, e.1.length = K ∧ e.2.length = V) :
    keyTableLength es = 1 + es.length * (K + V + 4) := by
  have hlen : (keyFields es).flatten.length = 2 * es.length := by
    simp only [keyFields_def, List.length_flatten, List.map_map, Function.comp_def,
      List.length_cons, List.length_nil, List.map_const', List.sum_replicate_nat]
    omega
  have hsum : ((keyFields es).flatten.map List.length).sum = es.length * (K + V + 2) := by
    simp only [keyFields_def, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, Nat.add_zero]
    calc
      _ = (es.map (fun _ => K + V + 2)).sum := by
        congr 1
        apply List.map_congr_left
        intro e he
        rw [(hw e he).1, (hw e he).2]
        omega
      _ = es.length * (K + V + 2) := by rw [List.map_const', List.sum_replicate_nat]
  have hne : tableFields [true] (keyFields es) ≠ [] := by
    rw [tableFields_eq]
    exact List.cons_ne_nil _ _
  rw [keyTableLength_def, joinFields_length _ hne, tableFields_eq]
  simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_nil,
    hlen, hsum]
  have h : 1 + es.length * (K + V + 2) + (2 * es.length + 1) - 1 =
      1 + es.length * (K + V + 2) + 2 * es.length := by omega
  rw [h]
  ring

/-- The physical layout of a represented memory is bounded by its allowed cell count. -/
theorem phase_tableOf_layout_bound {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) :
    keyTableLength es ≤ 1 + T.card * (W + a + W + 4) := by
  rw [phase_keyTableLength es (W + a) W (tableOf_widths h)]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (tableOf_length_le h)) 1

/-- Key assignment never decreases the number of entries: it replaces values or appends. -/
theorem phase_keyAssign_length_le (es : List (List Bool × List Bool)) (k v : List Bool) :
    es.length ≤ (keyAssign es k v).length := by
  rw [keyAssign_def]
  split_ifs <;> simp only [List.length_map, List.length_append, List.length_cons,
    List.length_nil] <;> omega

/-- Assigning a word to an in-range memory cell never shrinks the physical table layout. -/
theorem phase_keyAssign_layout_mono {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) {z : ℤ}
    (hz : InRange (W + a) z) (v : BitVec W) :
    keyTableLength es ≤ keyTableLength (keyAssign es (keyBits a W z) (bvBits v)) := by
  rw [phase_keyTableLength es (W + a) W (tableOf_widths h),
    phase_keyTableLength _ (W + a) W (tableOf_widths (tableOf_keyAssign h hz v))]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (phase_keyAssign_length_le es _ _)) 1

/-- Replacing a keyed table by a layout at least as long preserves its tape representation,
including the blank right tail.

**Proof sketch.** Read `KeyTableAt` through `keyTableAt_iff` and `tableAt_iff`. Inside the new
layout `keyTableWrite_apply` supplies its cells. Left of the origin it preserves the two old
blank sentinels; from the new end onward it preserves the old blank tail. The nonshrinking
length premise places the latter region beyond the old end. -/
theorem phase_keyTableAt_write {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (r : Fin K) (o : ℤ)
    (es es' : List (List Bool × List Bool)) (ht : KeyTableAt d r o es)
    (hlen : keyTableLength es ≤ keyTableLength es') :
    KeyTableAt { d with workTapes := keyTableWrite d r o es' } r o es' := by
  obtain ⟨ht, hb⟩ := (keyTableAt_iff d r o es).mp ht
  have ht' := (tableAt_iff d r o [true] (keyFields es)).mp ht
  have hc : (keyTableLength es : ℤ) ≤ (keyTableLength es' : ℤ) := by exact_mod_cast hlen
  apply (keyTableAt_iff _ r o es').mpr
  constructor
  · apply (tableAt_iff _ r o [true] (keyFields es')).mpr
    intro p hp hp'
    rw [← keyTableLength_def] at hp'
    change keyTableWrite d r o es' r (o + p) = fieldsTape (tableFields [true] (keyFields es')) p
    by_cases h0 : 0 ≤ p
    · by_cases hL : p < (keyTableLength es' : ℤ)
      · rw [keyTableWrite_apply, if_pos ⟨rfl, by omega, by omega⟩, add_sub_cancel_left]
      · rw [keyTableWrite_apply, if_neg (by omega), hb _ (by omega),
          fieldsTape_of_length_le _ (by rw [← keyTableLength_def]; omega)]
    · rw [keyTableWrite_apply, if_neg (by omega),
        ht' p hp (by rw [← keyTableLength_def]; omega), fieldsTape_of_neg _ (by omega),
        fieldsTape_of_neg _ (by omega)]
  · intro q hq
    change keyTableWrite d r o es' r q = none
    rw [keyTableWrite_apply, if_neg (by omega)]
    exact hb q (by omega)

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseMemory.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseRegister

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Memory rows of an instruction phase

Keyed lookup and assignment run on memory tape zero, key tape one and one of the three word
registers. The encoding supplies their physical table, uniform widths and blank scratch.

## Main definitions

* `WordRAM.Sim.PhaseData`: word width, memory footprint, RAM configuration and tape origins.
* `WordRAM.Sim.phaseMemoryEntries`: a represented table chosen from an encoded frame.
* `WordRAM.Sim.phaseMemoryCost`: a footprint bound for one keyed memory operation.

## Main results

* `WordRAM.Sim.phase_memoryEntries_spec`: the chosen table represents the encoded memory.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing
open scoped Classical

/-- Semantic data supplied to an instruction row, independently of its finite control. -/
structure PhaseData where
  width : ℕ
  cells : Finset ℤ
  cfg : XCfg width
  origins : Fin 8 → ℤ

/-- Select a represented table when the frame encodes the semantic data, and the empty table
otherwise. This choice is only used to state the endpoint of a keyed assignment. -/
noncomputable def phaseMemoryEntries {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x) : List (List Bool × List Bool) :=
  if he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) then
    Classical.choose ((encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
      i.origins (F.cfg ())).mp he).2.1
  else []

/-- The selected table is the witness of the encoding's memory clause when that encoding holds,
and is empty otherwise. -/
theorem phaseMemoryEntries_eq {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x) :
    phaseMemoryEntries a fn i F =
      if he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) then
        Classical.choose ((encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
          i.origins (F.cfg ())).mp he).2.1
      else [] := rfl

/-- Under the row's encoding precondition, the selected entries have the physical keyed-table
layout and represent the indexed RAM memory. -/
theorem phase_memoryEntries_spec {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x)
    (he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ())) :
    KeyTableAt (F.cfg ()) 0 (i.origins 0) (phaseMemoryEntries a fn i F) ∧
      TableOf a i.width i.cells i.cfg.mem (phaseMemoryEntries a fn i F) := by
  classical
  rw [phaseMemoryEntries_eq, dif_pos he]
  exact Classical.choose_spec ((encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
    i.origins (F.cfg ())).mp he).2.1

/-- A bound for the old table, key and value lengths in a single memory operation. -/
def phaseMemoryCost (a : ℕ) (i : PhaseData) : ℕ :=
  (1 + i.cells.card * (i.width + a + i.width + 4)) + (i.width + a) + i.width + 1

/-- The memory cost is the footprint layout bound plus one key, one word and one cell. -/
theorem phaseMemoryCost_eq (a : ℕ) (i : PhaseData) :
    phaseMemoryCost a i =
      (1 + i.cells.card * (i.width + a + i.width + 4)) + (i.width + a) + i.width + 1 := rfl

/-- The table/key/value bank places its value on register two, three or four and uses the two
dedicated scratch tapes. -/
def phaseMemoryBank (dst : Fin 3) : Fin 5 ↪ Fin 8 :=
  ⟨![0, 1, ⟨dst.val + 2, by omega⟩, 6, 7], by fin_cases dst <;> decide⟩

/-- The memory bank sends source indices to the table, key, selected value and scratch tapes. -/
theorem phaseMemoryBank_apply (dst : Fin 3) (r : Fin 5) :
    phaseMemoryBank dst r = ![0, 1, ⟨dst.val + 2, by omega⟩, 6, 7] r := rfl

/-- The RAM encoding and two register words supply every native keyed-row precondition on the
selected memory bank.

**Proof sketch.** Use `phase_memoryEntries_spec` for the shared chosen table and
`tableOf_widths` for its values. The selection lemmas transport layouts without changing their
heads; `phase_scratch_select` supplies the native scratch tapes. -/
theorem phase_memory_pre {S : Type} {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x) (q : S) (dst : Fin 3) (z : ℤ) (v : List Bool)
    (he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()))
    (hk : WordAt (F.cfg ()) 1 (keyBits a i.width z))
    (hv : WordAt (F.cfg ()) (phaseMemoryBank dst 2) v) (hlen : v.length = i.width) :
    let d := (F.cfg q).select (phaseMemoryBank dst)
    let es := phaseMemoryEntries a fn i F
    d.workTapePos 0 = i.origins 0 ∧ KeyTableAt d 0 (i.origins 0) es ∧
      WordAt d 1 (keyBits a i.width z) ∧ WordAt d 2 v ∧
      (∀ e ∈ es, e.2.length = v.length) ∧ ScratchBlank d := by
  have hh := (encodes_iff a fn i.cells i.cfg (Function.Embedding.refl _)
    i.origins (F.cfg ())).mp he
  have hm := phase_memoryEntries_spec a fn i F he
  have hscratch : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (phaseMemoryBank dst r).val := by
    have hs : ∀ d : Fin 3, ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (phaseMemoryBank d r).val := by
      decide
    exact hs dst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Cfg.select_eq, PhaseFrame.cfg_eq, phaseMemoryBank_apply] using hh.1 0
  · apply (phase_keyTableAt_select (phaseMemoryBank dst) (F.cfg q) 0 (i.origins 0) _).mpr
    exact (phase_keyTableAt_congr (F.cfg ()) (F.cfg q) 0 (i.origins 0) _
      (by simp only [PhaseFrame.cfg_eq])).mp hm.1
  · apply (phase_wordAt_select (phaseMemoryBank dst) (F.cfg q) 1 _).mpr
    exact (phase_wordAt_frame F q 1 _).mpr hk
  · apply (phase_wordAt_select (phaseMemoryBank dst) (F.cfg q) 2 _).mpr
    exact (phase_wordAt_frame F q (phaseMemoryBank dst 2) v).mpr hv
  · intro e he'
    exact (tableOf_widths hm.2 e he').2.trans hlen.symm
  · exact phase_scratch_select (phaseMemoryBank dst) F q hscratch
      (phase_frame_scratch fn i.cells i.cfg i.origins F he)

/-- The actual table/key/value length charge is bounded by the semantic footprint cost. -/
theorem phase_memory_cost {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (ht : TableOf a W T m es)
    (i : PhaseData) (hW : W = i.width) (hT : T = i.cells) (z : ℤ)
    (v : List Bool) (hv : v.length = W) :
    keyTableLength es + (keyBits a W z).length + v.length + 1 ≤ phaseMemoryCost a i := by
  rw [keyBits_def, bvBits_length, hv, phaseMemoryCost_eq, ← hW, ← hT]
  have hl := phase_tableOf_layout_bound ht
  omega

/-- Keyed lookup writes the addressed RAM word to the selected word register, preserving all
other frame fields, within a constant times the footprint layout bound.

**Proof sketch.** Choose `exists_keyLookupTM` and the physical table from `Encodes`.
`tableOf_widths` supplies the native value widths, while `tableOf_keyLookup_default` identifies
the lookup result even for an absent zero cell. Place the row with `phase_wordRow` and increase
its allowance using `phase_tableOf_layout_bound`. -/
theorem phase_lookupRow (a : ℕ) (fn : Bool) (z : PhaseData → ℤ) (dst : Fin 3) :
    ∃ C : ℕ, Nonempty (PhaseRow (fun _ => PhaseData)
      (fun i F => Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
        WordAt (F.cfg ()) 1 (keyBits a i.width (z i)) ∧
        PhaseReady i.width (phaseMemoryBank dst 2) F ∧ InRange (i.width + a) (z i))
      (fun i F => F.write (phaseMemoryBank dst 2) (bvBits (i.cfg.mem (z i))))
      (fun i => C * phaseMemoryCost a i) (fun i => C * phaseMemoryCost a i)) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := exists_keyLookupTM
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_wordRow (I := fun _ => PhaseData) _ _ _ _ S M entry exit (phaseMemoryBank dst) 2
  intro x i F hp
  let es := phaseMemoryEntries a fn i F
  have hm := phase_memoryEntries_spec a fn i F hp.1
  obtain ⟨w, hw, hwidth⟩ := (phaseReady_iff i.width (phaseMemoryBank dst 2) F).mp hp.2.2.1
  have hn := phase_memory_pre a fn i F entry dst (z i) w hp.1 hp.2.1 hw hwidth
  have hr := hM (i.origins 0) es (keyBits a i.width (z i)) w
    ((F.cfg entry).select (phaseMemoryBank dst))
    (by simp only [Cfg.select_eq, PhaseFrame.cfg_eq])
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
  rw [hwidth, tableOf_keyLookup_default hm.2 hp.2.2.2] at hr
  have hcost : keyTableLength es + (keyBits a i.width (z i)).length + i.width + 1 ≤
      phaseMemoryCost a i := by
    simpa only [List.length_replicate] using
      phase_memory_cost hm.2 i rfl rfl (z i) (List.replicate i.width false)
        (List.length_replicate ..)
  exact hr.mono (Nat.mul_le_mul_left C hcost) (Nat.mul_le_mul_left C hcost)

/-- The frame after assigning the value to the given RAM address in its represented table. -/
noncomputable def PhaseFrame.assign {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (z : ℤ) (v : BitVec i.width) (F : PhaseFrame x) : PhaseFrame x :=
  { F with
    workTapes := keyTableWrite (F.cfg ()) 0 (i.origins 0)
      (keyAssign (phaseMemoryEntries a fn i F) (keyBits a i.width z) (bvBits v)) }

attribute [simps (config := { isSimp := false }) inputPos workTapes workTapePos output] PhaseFrame.assign

/-- Assignment changes only the table tape by the layout of the updated selected entries. -/
theorem PhaseFrame.assign_eq {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (z : ℤ) (v : BitVec i.width) (F : PhaseFrame x) :
    F.assign a fn i z v =
      { F with
        workTapes := keyTableWrite (F.cfg ()) 0 (i.origins 0)
          (keyAssign (phaseMemoryEntries a fn i F) (keyBits a i.width z) (bvBits v)) } := rfl

/-- Keyed assignment stores register four at the keyed address, within a constant times the
old semantic footprint's table/key/value charge.

**Proof sketch.** Use `phase_memory_pre` for the shared selected table and native preconditions.
`exists_keyAssignTM` gives the five-tape run and `phase_memory_cost` increases its bounds.
`phase_nativeRow` places that run, with `phase_embed_keyTableWrite` identifying the prescribed
assignment frame. -/
theorem phase_assignRow (a : ℕ) (fn : Bool) (z : PhaseData → ℤ)
    (v : (x : List Bool) → (i : PhaseData) → BitVec i.width) :
    ∃ C : ℕ, Nonempty (PhaseRow (fun _ => PhaseData)
      (fun {x} i F => Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
        WordAt (F.cfg ()) 1 (keyBits a i.width (z i)) ∧
        WordAt (F.cfg ()) 4 (bvBits (v x i)) ∧ InRange (i.width + a) (z i))
      (fun {x} i F => F.assign a fn i (z i) (v x i))
      (fun i => C * phaseMemoryCost a i) (fun i => C * phaseMemoryCost a i)) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := exists_keyAssignTM
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_nativeRow (I := fun _ => PhaseData) _ _ _ _ S M entry exit (phaseMemoryBank 2)
    (fun {x} i F => { ((F.cfg entry).select (phaseMemoryBank 2)) with
      state := some exit
      workTapes := keyTableWrite ((F.cfg entry).select (phaseMemoryBank 2)) 0 (i.origins 0)
        (keyAssign (phaseMemoryEntries a fn i F) (keyBits a i.width (z i)) (bvBits (v x i))) })
  · intro x i F hp
    have hn := phase_memory_pre a fn i F entry 2 (z i) (bvBits (v x i))
      hp.1 hp.2.1 hp.2.2.1 (bvBits_length _)
    have hr := hM (i.origins 0) (phaseMemoryEntries a fn i F) (keyBits a i.width (z i))
      (bvBits (v x i)) ((F.cfg entry).select (phaseMemoryBank 2))
      (by simp only [Cfg.select_eq, PhaseFrame.cfg_eq])
      hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
    have hc := phase_memory_cost (phase_memoryEntries_spec a fn i F hp.1).2 i rfl rfl
      (z i) (bvBits (v x i)) (bvBits_length _)
    exact hr.mono (Nat.mul_le_mul_left C hc) (Nat.mul_le_mul_left C hc)
  · intro x i F hp
    simpa only [PhaseFrame.assign_eq, PhaseFrame.cfg_eq, Cfg.select_eq,
      phase_keyTableWrite_as_update, phaseMemoryBank_apply] using
      phase_embed_keyTableWrite (phaseMemoryBank 2) (F.cfg entry) (some exit) F.inputPos 0
        (i.origins 0)
        (keyAssign (phaseMemoryEntries a fn i F) (keyBits a i.width (z i)) (bvBits (v x i)))
  · intro x i F hp
    rfl

/-- A frame assignment preserves the encoding, updates its RAM word and adds the addressed cell
to the allowed footprint. -/
theorem phase_frame_assign_encodes {x : List Bool} (a : ℕ) (fn : Bool)
    (i : PhaseData) (F : PhaseFrame x)
    (he : Encodes a fn i.cells i.cfg (Function.Embedding.refl _) i.origins (F.cfg ()))
    (z : ℤ) (hz : InRange (i.width + a) z) (v : BitVec i.width) :
    Encodes a fn (insert z i.cells) { i.cfg with mem := Function.update i.cfg.mem z v }
      (Function.Embedding.refl _) i.origins ((F.assign a fn i z v).cfg ()) := by
  have hm := phase_memoryEntries_spec a fn i F he
  simpa only [PhaseFrame.assign_eq, PhaseFrame.cfg_eq] using
    phase_encodes_keyAssign fn i.cells i.cfg i.origins (F.cfg ()) he
      (phaseMemoryEntries a fn i F) hm.1 hm.2 z hz v

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseMemoryMachines.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSemantics

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Phases for deterministic memory instructions

Each memory schedule is connected to the extended RAM step through the published instruction
and footprint equations. The resulting finite phases have fresh entries and two distinct exits,
with every run taking the next exit and equal transitions under both choices.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_oneMachine`: the constant-one instruction phase.
* `WordRAM.Sim.phase_binaryMachine`: the add, subtract and multiply instruction phases.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The one instruction has a finite fresh-entry phase, with equal choices and a next-exit run
encoding its exact RAM step. -/
theorem phase_oneMachine (a : ℕ) (fn : Bool) (z : ℤ) (hz : InRange a z) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.base (.one z)) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_constantSchedule a fn z 1 hz
  apply phase_memoryMachine a fn (.base (.one z)) 0 (fun _ => z)
    (fun _ i => BitVec.ofInt i.width 1) R
  · intro i
    simp only [XInstr.touches_def, baseTouches_def, Finset.mem_singleton]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z (BitVec.ofInt i.width 1) }, ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf, effect_def]

/-- Each binary arithmetic instruction has a finite fresh-entry phase that loads its two
original operands, computes and stores the result, then exits at next. -/
theorem phase_binaryMachine (a : ℕ) (fn : Bool) (z j k : ℤ)
    (hz : InRange a z) (hj : InRange a j) (hk : InRange a k) (op : PhaseArith) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn
        (.base (match op with | .add => .add z j k | .sub => .sub z j k | .mul => .mul z j k))
        0 false b x i F) (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_binarySchedule a fn z j k hz hj hk op
  apply phase_memoryMachine a fn _ 0 (fun _ => z)
    (fun _ i => op.value (i.cfg.mem j) (i.cfg.mem k)) R
  · intro i
    cases op <;> simp only [XInstr.touches_def, baseTouches_def, Finset.mem_insert_self]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z (op.value (i.cfg.mem j) (i.cfg.mem k)) },
      ?_, rfl, rfl, rfl⟩
    cases op <;> simp only [xstep_def, hf, effect_def, PhaseArith.value_eq]

/-- Indirect load has a fresh-entry phase whose next exit encodes the addressed original-memory
word stored at the immediate destination. -/
theorem phase_loadMachine (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.base (.load z j)) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_loadSchedule a fn z j hz hj
  apply phase_memoryMachine a fn (.base (.load z j)) 0 (fun _ => z)
    (fun _ i => i.cfg.mem (i.cfg.mem j).toInt) R
  · intro i
    simp only [XInstr.touches_def, baseTouches_def, Finset.mem_insert_self]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z (i.cfg.mem (i.cfg.mem j).toInt) }, ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf, effect_def]

/-- Indirect store has a fresh-entry phase whose next exit encodes the original source value
assigned at the signed address in the destination cell. -/
theorem phase_storeMachine (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.base (.store z j)) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_storeSchedule a fn z j hz hj
  apply phase_memoryMachine a fn (.base (.store z j)) 0 (fun i => (i.cfg.mem z).toInt)
    (fun _ i => i.cfg.mem j) R
  · intro i
    have hd : (i.cfg.mem z).toInt ∈ ({z, j, (i.cfg.mem z).toInt} : Finset ℤ) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self (i.cfg.mem z).toInt))
    simpa only [XInstr.touches_def, baseTouches_def] using hd
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem (i.cfg.mem z).toInt (i.cfg.mem j) }, ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf, effect_def]

/-- Signed halving has a fresh-entry phase whose next exit encodes the arithmetic right shift
stored at its immediate destination. -/
theorem phase_halfMachine (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.half z j) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_halfSchedule a fn z j hz hj
  apply phase_memoryMachine a fn (.half z j) 0 (fun _ => z)
    (fun _ i => (i.cfg.mem j).sshiftRight 1) R
  · intro i
    simp only [XInstr.touches_def, Finset.mem_insert_self]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z ((i.cfg.mem j).sshiftRight 1) }, ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf]

/-- Input access has a fresh-entry phase whose next exit encodes the exact extended-RAM input
bit word assigned to the immediate destination. -/
theorem phase_inputMachine (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn (.rdIn z j) 0 false b x i F)
      (fun _ _ _ => false)) := by
  obtain ⟨R⟩ := phase_inputSchedule a fn z j hz hj
  apply phase_memoryMachine a fn (.rdIn z j) 0 (fun _ => z)
    (fun x i => inBitWord i.width x (i.cfg.mem j).toInt) R
  · intro i
    simp only [XInstr.touches_def, Finset.mem_insert_self]
  · intro b x i P ρ hf hc
    refine ⟨{ i.cfg with
      pc := i.cfg.pc + 1
      mem := Function.update i.cfg.mem z (inBitWord i.width x (i.cfg.mem j).toInt) },
      ?_, rfl, rfl, rfl⟩
    simp only [xstep_def, hf]

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseOperations.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseSchedules

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unary and indirect memory instruction schedules

The unary instructions fetch one word, compute into the result register and assign once.
Indirect load uses sign extension and a second lookup; indirect store fetches the value before
constructing its computed destination key.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_unarySchedule`: the shared fetch, compute and store schedule.
* `WordRAM.Sim.phase_halfSchedule`: signed halving and assignment.
* `WordRAM.Sim.phase_inputSchedule`: read-only input access and assignment.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A computation block whose input is the fetched source word and whose result register is
known gives a complete fetch, compute and immediate-store instruction schedule. -/
theorem phase_unarySchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (v : (x : List Bool) → (i : PhaseData) → BitVec i.width)
    (O : PhaseBlock
      (PhaseState a fn (fun _ i => Function.update
        (Function.update (fun _ => none) 1 (some (keyBits a i.width j))) 2
          (some (bvBits (i.cfg.mem j))))) (PhaseState a fn regs))
    (hv : ∀ x i, regs x i 4 = some (bvBits (v x i))) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (v x i) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  obtain ⟨J⟩ := phase_fetchBlock a fn (fun _ _ _ => none) j 0 hj
  simp only [phaseMemoryBank_apply] at J
  obtain ⟨JO⟩ := J.seq O
  obtain ⟨S⟩ := phase_storeImmediateBlock a fn regs z v hz hv
  exact JO.seq S

/-- Signed halving fetches the source word, shifts it right once with sign retention and
assigns the result at its immediate destination. -/
theorem phase_halfSchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z ((i.cfg.mem j).sshiftRight 1) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₁ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i => Function.update
    (Function.update (fun _ => none) 1 (some (keyBits a i.width j))) 2
      (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update (r₁ x i) 4 (some (bvBits ((i.cfg.mem j).sshiftRight 1)))
  obtain ⟨H⟩ := phase_halfBlock a fn r₁ (fun i => i.cfg.mem j) (by intro x i; rfl)
  exact phase_unarySchedule a fn z j hz hj r₂ (fun _ i => (i.cfg.mem j).sshiftRight 1) H
    (by intro x i; rfl)

/-- Input access fetches its signed source position, reads the bit word and assigns it at the
immediate destination, allowing only the read-only input head to finish elsewhere. -/
theorem phase_inputSchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (inBitWord i.width x (i.cfg.mem j).toInt) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₁ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i => Function.update
    (Function.update (fun _ => none) 1 (some (keyBits a i.width j))) 2
      (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update (r₁ x i) 4
    (some (bvBits (inBitWord i.width x (i.cfg.mem j).toInt)))
  obtain ⟨I⟩ := phase_inputBlock a fn r₁ (fun i => i.cfg.mem j) (by intro x i; rfl)
  exact phase_unarySchedule a fn z j hz hj r₂
    (fun x i => inBitWord i.width x (i.cfg.mem j).toInt) I (by intro x i; rfl)

/-- Indirect load fetches a source address word, sign-extends it to a key, looks up the addressed
word and assigns that result at the immediate destination.

**Proof sketch.** The shared unary schedule supplies the first fetch and final store. Its
middle block composes `phase_signExtendBlock` with a lookup into register four, using
`phase_computed_inRange` for the signed indirect address. All reads use the original memory. -/
theorem phase_loadSchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (i.cfg.mem (i.cfg.mem j).toInt) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₁ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ i => Function.update
    (Function.update (fun _ => none) 1 (some (keyBits a i.width j))) 2
      (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update (r₁ x i) 1
    (some (keyBits a i.width (i.cfg.mem j).toInt))
  let r₃ := fun x i => Function.update (r₂ x i) 4
    (some (bvBits (i.cfg.mem (i.cfg.mem j).toInt)))
  obtain ⟨E⟩ := phase_signExtendBlock a fn r₁ (fun i => i.cfg.mem j) (by intro x i; rfl)
  obtain ⟨L⟩ := phase_lookupBlock a fn r₂ (fun i => (i.cfg.mem j).toInt) 2
    (by intro x i; rfl) (fun i => phase_computed_inRange a (i.cfg.mem j))
  simp only [phaseMemoryBank_apply] at L
  obtain ⟨EL⟩ := E.seq L
  exact phase_unarySchedule a fn z j hz hj r₃ (fun _ i => i.cfg.mem (i.cfg.mem j).toInt) EL
    (by intro x i; rfl)

/-- Indirect store fetches the value first, then the destination address word, sign-extends that
address to its key and assigns the saved value at that computed destination.

**Proof sketch.** Fetch the value into register four before the destination-address fetch into
two, so key construction cannot overwrite a saved computed key. `phase_signExtendBlock`
constructs the final key; `phase_assignBlock` uses the retained value and the signed-address
range. Sequential block contracts account for all dispatches and preserve the original-memory
meaning of every read. -/
theorem phase_storeSchedule (a : ℕ) (fn : Bool) (z j : ℤ)
    (hz : InRange a z) (hj : InRange a j) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert (i.cfg.mem z).toInt i.cells)
        { i.cfg with mem := Function.update i.cfg.mem (i.cfg.mem z).toInt (i.cfg.mem j) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₀ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ _ _ => none
  let r₁ := fun x i => Function.update
    (Function.update (r₀ x i) 1 (some (keyBits a i.width j))) 4 (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update
    (Function.update (r₁ x i) 1 (some (keyBits a i.width z))) 2 (some (bvBits (i.cfg.mem z)))
  let r₃ := fun x i => Function.update (r₂ x i) 1
    (some (keyBits a i.width (i.cfg.mem z).toInt))
  obtain ⟨J⟩ := phase_fetchBlock a fn r₀ j 2 hj
  simp only [phaseMemoryBank_apply] at J
  obtain ⟨Z⟩ := phase_fetchBlock a fn r₁ z 0 hz
  simp only [phaseMemoryBank_apply] at Z
  obtain ⟨E⟩ := phase_signExtendBlock a fn r₂ (fun i => i.cfg.mem z) (by intro x i; rfl)
  obtain ⟨A⟩ := phase_assignBlock a fn r₃ (fun i => (i.cfg.mem z).toInt) (fun _ i => i.cfg.mem j)
    (by intro x i; rfl) (by intro x i; rfl) (fun i => phase_computed_inRange a (i.cfg.mem z))
  obtain ⟨JZ⟩ := J.seq Z
  obtain ⟨JZE⟩ := JZ.seq E
  exact JZE.seq A

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseRegister.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseRows

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Register invariants between instruction rows

The RAM encoding supplies correctly sized registers and dedicated blank scratch. These lemmas
keep the encoding and previously loaded operand words available as the frame rows are sequenced.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_frame_scratch`: an encoded frame supplies the row scratch precondition.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The dedicated scratch tapes in an encoded frame satisfy the row scratch precondition. -/
theorem phase_frame_scratch {a W : ℕ} {x : List Bool} (fn : Bool) (T : Finset ℤ)
    (c : XCfg W) (o : Fin 8 → ℤ) (F : PhaseFrame x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ())) : PhaseScratch F := by
  apply (phaseScratch_iff F).mpr
  intro r hr z
  have hh := ((encodes_iff a fn T c (Function.Embedding.refl _) o (F.cfg ())).mp he).2.2.2.2.2.1
    r hr z
  simpa only [PhaseFrame.cfg_eq] using hh

/-- Each encoded register is ready at its prescribed width: the key width on tape one and
the word width on tapes two through four. -/
theorem phase_frame_ready {a W : ℕ} {x : List Bool} (fn : Bool) (T : Finset ℤ)
    (c : XCfg W) (o : Fin 8 → ℤ) (F : PhaseFrame x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ())) (r : Fin 8)
    (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4) :
    PhaseReady (if r = 1 then W + a else W) r F := by
  have hh := (encodes_iff a fn T c (Function.Embedding.refl _) o (F.cfg ())).mp he
  by_cases hr : r = 1
  · subst r
    rw [if_pos rfl, phaseReady_iff]
    exact hh.2.2.1
  · rw [if_neg hr, phaseReady_iff]
    have hv : r.val ≠ 1 := by
      intro hv
      exact hr (Fin.ext hv)
    exact hh.2.2.2.1 r (by omega) hr₁

/-- A frame word write of the register's prescribed width preserves its RAM encoding. -/
theorem phase_frame_write_encodes {a W : ℕ} {x : List Bool} (fn : Bool) (T : Finset ℤ)
    (c : XCfg W) (o : Fin 8 → ℤ) (F : PhaseFrame x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o (F.cfg ())) (r : Fin 8)
    (hr₀ : 1 ≤ r.val) (hr₁ : r.val ≤ 4) (w : List Bool)
    (hw : w.length = if r = 1 then W + a else W) :
    Encodes a fn T c (Function.Embedding.refl _) o ((F.write r w).cfg ()) := by
  simpa only [PhaseFrame.write_eq, PhaseFrame.cfg_eq] using
    phase_encodes_wordWrite fn T c o (F.cfg ()) he r hr₀ hr₁ w hw

/-- Writing a word of the ready register's width establishes that exact word in the result
frame. -/
theorem phase_frame_write_word {x : List Bool} (F : PhaseFrame x) (r : Fin 8)
    (W : ℕ) (w : List Bool) (hr : PhaseReady W r F) (hw : w.length = W) :
    WordAt ((F.write r w).cfg ()) r w := by
  obtain ⟨old, hold, hwidth⟩ := (phaseReady_iff W r F).mp hr
  simpa only [PhaseFrame.write_eq, PhaseFrame.cfg_eq] using
    phase_wordAt_write (F.cfg ()) r old w hold (hw.trans hwidth.symm)

/-- Writing one frame register preserves every word held on another register. -/
theorem phase_frame_write_other {x : List Bool} (F : PhaseFrame x) (r j : Fin 8)
    (w v : List Bool) (hj : j ≠ r) (hv : WordAt (F.cfg ()) j v) :
    WordAt ((F.write r w).cfg ()) j v := by
  apply (phase_wordAt_congr (F.cfg ()) ((F.write r w).cfg ()) j v ?_ ?_).mp hv
  · simp only [PhaseFrame.write_eq, PhaseFrame.cfg_eq, phase_wordWrite_as_update,
      Function.update_of_ne hj]
  · simp only [PhaseFrame.write_eq, PhaseFrame.cfg_eq]

/-- Removing a configuration's control and reinstalling unit control preserves its RAM
encoding, because every work tape, head and output is unchanged. -/
theorem phase_frame_ofCfg_encodes {a W : ℕ} {S : Type} {x : List Bool} (fn : Bool)
    (T : Finset ℤ) (c : XCfg W) (o : Fin 8 → ℤ) (d : Turing.Cfg 8 Bool S x)
    (he : Encodes a fn T c (Function.Embedding.refl _) o d) :
    Encodes a fn T c (Function.Embedding.refl _) o ((PhaseFrame.ofCfg d).cfg ()) := by
  apply (phase_encodes_congr fn T c c (Function.Embedding.refl _) o d
    ((PhaseFrame.ofCfg d).cfg ()) ?_ ?_ ?_ rfl rfl).mp he
  · simp only [PhaseFrame.cfg_eq, PhaseFrame.ofCfg_eq]
  · simp only [PhaseFrame.cfg_eq, PhaseFrame.ofCfg_eq]
  · simp only [PhaseFrame.cfg_eq, PhaseFrame.ofCfg_eq]

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseRows.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseInvariant
import TCSlib.Complexity.TuringMachine.Build.InputBit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Word rows on the simulation's tape bank

The five-tape word rows use the simulation's two operand registers and result register, or its
key register and input-length tape, while tapes six and seven provide their blank scratch.
The finite machines are independent of the word width and input.

## Main definitions

* `WordRAM.Sim.PhaseFrame.write`: write one word while preserving the other frame fields.

## Main results

* `WordRAM.Sim.phase_wordRow`: place a native word-writing contract on eight tapes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The frame after overwriting a word register, with its input head, work heads and output
unchanged. -/
def PhaseFrame.write {x : List Bool} (r : Fin 8) (w : List Bool) (F : PhaseFrame x) :
    PhaseFrame x :=
  { F with workTapes := wordWrite (F.cfg ()) r w }

attribute [simps (config := { isSimp := false }) inputPos workTapes workTapePos output] PhaseFrame.write

/-- A register write changes just the frame's tapes by `wordWrite` at unit control. -/
theorem PhaseFrame.write_eq {x : List Bool} (r : Fin 8) (w : List Bool) (F : PhaseFrame x) :
    F.write r w = { F with workTapes := wordWrite (F.cfg ()) r w } := rfl

/-- A native five-tape contract gives a finite frame row whenever its embedded endpoint is
the prescribed result frame and its work heads are restored. -/
theorem phase_nativeRow {I : List Bool → Type}
    (P : ∀ {x : List Bool}, I x → PhaseFrame x → Prop)
    (f : ∀ {x : List Bool}, I x → PhaseFrame x → PhaseFrame x)
    (B E : ∀ {x : List Bool}, I x → ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (M : MultiTapeTM 5 Bool S) (entry exit : S)
    (σ : Fin 5 ↪ Fin 8) (post : ∀ {x : List Bool}, I x → PhaseFrame x → Turing.Cfg 5 Bool S x)
    (h : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), P i F →
      ReachesWithin M ((F.cfg entry).select σ) {some exit} (B i) (E i) (post i F))
    (he : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), P i F →
      embedEmitCfg σ F.workTapes F.workTapePos F.output (post i F) = (f i F).cfg exit)
    (hh : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), P i F →
      (f i F).workTapePos = F.workTapePos) : Nonempty (PhaseRow I P f B E) := by
  refine ⟨⟨S, inferInstance, inferInstance, embedEmitTM σ M, entry, exit, hh, ?_⟩⟩
  intro x i F hp
  have hr := phase_reaches_embed σ M (F.cfg entry) {some exit} (B i) (E i) _ (h i F hp)
  have he' := he i F hp
  simpa only [PhaseFrame.cfg_eq, he'] using hr

/-- Placing a native five-tape word-writing row gives a finite row over frames on eight tapes.
The source precondition may be any predicate that supplies the native contract.

**Proof sketch.** Apply `phase_reaches_embed` to the selected native contract and
`phase_embed_wordWrite` to its endpoint. `phase_wordWrite_as_update` identifies that endpoint
with `PhaseFrame.write` independently of the installed control state. -/
theorem phase_wordRow {I : List Bool → Type}
    (P : ∀ {x : List Bool}, I x → PhaseFrame x → Prop)
    (v : ∀ {x : List Bool}, I x → List Bool) (B E : ∀ {x : List Bool}, I x → ℕ)
    (S : Type) [Fintype S] [DecidableEq S] (M : MultiTapeTM 5 Bool S) (entry exit : S)
    (σ : Fin 5 ↪ Fin 8) (r : Fin 5)
    (h : ∀ {x : List Bool} (i : I x) (F : PhaseFrame x), P i F →
      ReachesWithin M ((F.cfg entry).select σ) {some exit} (B i) (E i)
        { ((F.cfg entry).select σ) with
          state := some exit
          workTapes := wordWrite ((F.cfg entry).select σ) r (v i) }) :
    Nonempty (PhaseRow I P (fun i F => F.write (σ r) (v i)) B E) := by
  apply phase_nativeRow (I := I) P _ B E S M entry exit σ _ h
  · intro x i F hp
    simpa only [PhaseFrame.write_eq, PhaseFrame.cfg_eq, Cfg.select_eq,
      phase_wordWrite_as_update] using
      phase_embed_wordWrite σ (F.cfg entry) (some exit) F.inputPos r (v i)
  · intro x i F hp
    rfl

/-- A delimited word of the specified width is available at a register. -/
def PhaseReady {x : List Bool} (W : ℕ) (r : Fin 8) (F : PhaseFrame x) : Prop :=
  ∃ w, WordAt (F.cfg ()) r w ∧ w.length = W

/-- Register readiness means that a word of the specified width is delimited at its head. -/
theorem phaseReady_iff {x : List Bool} (W : ℕ) (r : Fin 8) (F : PhaseFrame x) :
    PhaseReady W r F ↔ ∃ w, WordAt (F.cfg ()) r w ∧ w.length = W := Iff.rfl

/-- The two dedicated scratch tapes of a frame are blank everywhere. -/
def PhaseScratch {x : List Bool} (F : PhaseFrame x) : Prop :=
  ∀ r : Fin 8, 6 ≤ r.val → ∀ z : ℤ, F.workTapes r z = none

/-- Scratch blankness is pointwise blankness of tapes six and seven. -/
theorem phaseScratch_iff {x : List Bool} (F : PhaseFrame x) :
    PhaseScratch F ↔ ∀ r : Fin 8, 6 ≤ r.val → ∀ z : ℤ, F.workTapes r z = none := Iff.rfl

/-- The operand/result bank: source tapes two and three, result tape four, scratch six and seven. -/
def phaseArithBank : Fin 5 ↪ Fin 8 :=
  ⟨![2, 3, 4, 6, 7], by decide⟩

/-- The arithmetic bank sends its five indices to `2, 3, 4, 6, 7`, respectively. -/
theorem phaseArithBank_apply (r : Fin 5) : phaseArithBank r = ![2, 3, 4, 6, 7] r := rfl

/-- Installing a different control state does not change a frame's word layouts. -/
theorem phase_wordAt_frame {S : Type} {x : List Bool} (F : PhaseFrame x) (q : S)
    (r : Fin 8) (w : List Bool) : WordAt (F.cfg q) r w ↔ WordAt (F.cfg ()) r w := by
  apply phase_wordAt_congr
  · simp only [PhaseFrame.cfg_eq]
  · simp only [PhaseFrame.cfg_eq]

/-- A bank whose last two source tapes lie on the dedicated scratch tapes satisfies the native
blank-scratch precondition of the word rows. -/
theorem phase_scratch_select {S : Type} {x : List Bool} (σ : Fin 5 ↪ Fin 8)
    (F : PhaseFrame x) (q : S) (hσ : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (σ r).val)
    (hF : PhaseScratch F) : ScratchBlank ((F.cfg q).select σ) := by
  apply (scratchBlank_iff _).mpr
  intro r hr z
  simpa only [Cfg.select_eq, PhaseFrame.cfg_eq] using
    (phaseScratch_iff F).mp hF (σ r) (hσ r hr) z

/-- An integer-constant writer on a selected register is a finite frame row, uniform in the
width supplied by its index and linear in that width.

**Proof sketch.** Choose `exists_wordIntTM` once for the constant and extension amount. Read
register readiness, transport its word to the selection, and supply the native blank scratch
with `phase_scratch_select`. `phase_wordRow` places the contract without changing its bounds. -/
theorem phase_intRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (c : ℤ) (a : ℕ) (σ : Fin 5 ↪ Fin 8)
    (hσ : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (σ r).val) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => PhaseReady (width i + a) (σ 2) F ∧ PhaseScratch F)
      (fun i F => F.write (σ 2) (bvBits (BitVec.ofInt (width i + a) c)))
      (fun i => C * (width i + 1)) (fun i => C * (width i + 1))) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := exists_wordIntTM c a
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_wordRow (I := I) _ _ _ _ S M entry exit σ 2
  intro x i F hp
  obtain ⟨w, hw, hwidth⟩ := (phaseReady_iff (width i + a) (σ 2) F).mp hp.1
  apply hM (W := width i) w ((F.cfg entry).select σ)
  · simp only [Cfg.select_eq, PhaseFrame.cfg_eq]
  · exact (phase_wordAt_select σ (F.cfg entry) 2 w).mpr
      ((phase_wordAt_frame F entry (σ 2) w).mpr hw)
  · exact hwidth
  · exact phase_scratch_select σ F entry hσ hp.2

/-- The three binary arithmetic instructions use the same two-source register interface. -/
inductive PhaseArith where
  | add
  | sub
  | mul

/-- The word result of a binary arithmetic instruction. -/
def PhaseArith.value {W : ℕ} (op : PhaseArith) (u v : BitVec W) : BitVec W :=
  match op with
  | .add => u + v
  | .sub => u - v
  | .mul => u * v

/-- Binary arithmetic returns the sum, difference or product selected by its instruction. -/
theorem PhaseArith.value_eq {W : ℕ} (op : PhaseArith) (u v : BitVec W) :
    op.value u v = match op with
      | .add => u + v
      | .sub => u - v
      | .mul => u * v := rfl

/-- The native time allowance is quadratic for multiplication and linear for addition/subtraction. -/
def PhaseArith.steps (op : PhaseArith) (W : ℕ) : ℕ :=
  match op with
  | .mul => (W + 1) ^ 2
  | _ => W + 1

/-- The binary arithmetic time allowance is `(W+1)^2` for multiplication and `W+1` otherwise. -/
theorem PhaseArith.steps_eq (op : PhaseArith) (W : ℕ) :
    op.steps W = match op with
      | .mul => (W + 1) ^ 2
      | _ => W + 1 := rfl

/-- Each binary arithmetic instruction has the common native five-tape contract, with its
own uniform constant and the appropriate linear or quadratic time allowance. -/
theorem PhaseArith.native (op : PhaseArith) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 5 Bool S)
      (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Turing.Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) →
        WordAt d 2 w → w.length = W → ScratchBlank d →
        ReachesWithin M d {some exit} (C * op.steps W) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (op.value u v)) } := by
  cases op with
  | add => exact exists_wordAddTM
  | sub => exact exists_wordSubTM
  | mul => exact exists_wordMulTM

/-- Binary arithmetic reads registers two and three and writes register four, uniformly in
the indexed word width. Addition/subtraction take linear time; multiplication takes quadratic
time; the radius is always linear.

**Proof sketch.** Choose the shared contract `PhaseArith.native` and place it with
`phase_wordRow` on `phaseArithBank`. Word preconditions are transported by
`phase_wordAt_select` and `phase_wordAt_frame`; `phase_scratch_select` supplies blank scratch. -/
theorem phase_arithRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u v : ∀ {x : List Bool} (i : I x), BitVec (width i)) (op : PhaseArith) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => WordAt (F.cfg ()) 2 (bvBits (u i)) ∧
        WordAt (F.cfg ()) 3 (bvBits (v i)) ∧ PhaseReady (width i) 4 F ∧ PhaseScratch F)
      (fun i F => F.write 4 (bvBits (op.value (u i) (v i))))
      (fun i => C * op.steps (width i)) (fun i => C * (width i + 1))) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := op.native
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_wordRow (I := I) _ _ _ _ S M entry exit phaseArithBank 2
  intro x i F hp
  obtain ⟨w, hw, hwidth⟩ := (phaseReady_iff (width i) 4 F).mp hp.2.2.1
  apply hM (u i) (v i) w ((F.cfg entry).select phaseArithBank)
  · simp only [Cfg.select_eq, PhaseFrame.cfg_eq]
  · exact (phase_wordAt_select phaseArithBank (F.cfg entry) 0 _).mpr
      ((phase_wordAt_frame F entry 2 _).mpr hp.1)
  · exact (phase_wordAt_select phaseArithBank (F.cfg entry) 1 _).mpr
      ((phase_wordAt_frame F entry 3 _).mpr hp.2.1)
  · exact (phase_wordAt_select phaseArithBank (F.cfg entry) 2 w).mpr
      ((phase_wordAt_frame F entry 4 w).mpr hw)
  · exact hwidth
  · exact phase_scratch_select phaseArithBank F entry (by decide) hp.2.2.2

/-- The key-writing bank reads register two and writes register one, using scratch six/seven. -/
def phaseKeyBank : Fin 5 ↪ Fin 8 :=
  ⟨![2, 3, 1, 6, 7], by decide⟩

/-- The key bank sends its five indices to `2, 3, 1, 6, 7`, respectively. -/
theorem phaseKeyBank_apply (r : Fin 5) : phaseKeyBank r = ![2, 3, 1, 6, 7] r := rfl

/-- A native one-source word row with a fixed width extension lifts to the selected source and
destination registers of a frame, with unchanged linear time and radius allowances.

**Proof sketch.** Choose the supplied native contract, read destination readiness, transport the
source and destination words, and obtain blank scratch with `phase_scratch_select`.
`phase_wordRow` then supplies the finite eight-tape machine. This adapter is shared by arithmetic
halving and sign extension. -/
theorem phase_unaryRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u : ∀ {x : List Bool} (i : I x), BitVec (width i)) (a : ℕ)
    (f : ∀ W : ℕ, BitVec W → BitVec (W + a)) (σ : Fin 5 ↪ Fin 8)
    (hσ : ∀ r : Fin 5, 3 ≤ r.val → 6 ≤ (σ r).val)
    (hnative : ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 5 Bool S)
      (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (v : BitVec W) (w : List Bool) (d : Turing.Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits v) → WordAt d 2 w → w.length = W + a →
        ScratchBlank d → ReachesWithin M d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (f W v)) }) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => WordAt (F.cfg ()) (σ 0) (bvBits (u i)) ∧
        PhaseReady (width i + a) (σ 2) F ∧ PhaseScratch F)
      (fun i F => F.write (σ 2) (bvBits (f (width i) (u i))))
      (fun i => C * (width i + 1)) (fun i => C * (width i + 1))) := by
  obtain ⟨S, hfin, hdec, M, entry, exit, C, hM⟩ := hnative
  letI := hfin
  letI := hdec
  refine ⟨C, ?_⟩
  apply phase_wordRow (I := I) _ _ _ _ S M entry exit σ 2
  intro x i F hp
  obtain ⟨w, hw, hwidth⟩ := (phaseReady_iff (width i + a) (σ 2) F).mp hp.2.1
  apply hM (u i) w ((F.cfg entry).select σ)
  · simp only [Cfg.select_eq, PhaseFrame.cfg_eq]
  · exact (phase_wordAt_select σ (F.cfg entry) 0 _).mpr
      ((phase_wordAt_frame F entry (σ 0) _).mpr hp.1)
  · exact (phase_wordAt_select σ (F.cfg entry) 2 w).mpr
      ((phase_wordAt_frame F entry (σ 2) w).mpr hw)
  · exact hwidth
  · exact phase_scratch_select σ F entry hσ hp.2.2

/-- Arithmetic halving reads register two and writes register four, preserving the other frame
fields within linear time and radius. -/
theorem phase_halfRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u : ∀ {x : List Bool} (i : I x), BitVec (width i)) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => WordAt (F.cfg ()) 2 (bvBits (u i)) ∧
        PhaseReady (width i) 4 F ∧ PhaseScratch F)
      (fun i F => F.write 4 (bvBits ((u i).sshiftRight 1)))
      (fun i => C * (width i + 1)) (fun i => C * (width i + 1))) := by
  simpa only [phaseArithBank_apply, Nat.add_zero] using
    phase_unaryRow width u 0 (fun _ v => v.sshiftRight 1) phaseArithBank (by decide)
      exists_wordHalfTM

/-- Sign extension reads register two and writes the extended address word to key register one,
within linear time and radius with a constant depending on the extension amount. -/
theorem phase_signExtendRow {I : List Bool → Type} (width : ∀ {x : List Bool}, I x → ℕ)
    (u : ∀ {x : List Bool} (i : I x), BitVec (width i)) (a : ℕ) :
    ∃ C : ℕ, Nonempty (PhaseRow I
      (fun i F => WordAt (F.cfg ()) 2 (bvBits (u i)) ∧
        PhaseReady (width i + a) 1 F ∧ PhaseScratch F)
      (fun i F => F.write 1 (bvBits ((u i).signExtend (width i + a))))
      (fun i => C * (width i + 1)) (fun i => C * (width i + 1))) := by
  simpa only [phaseKeyBank_apply] using
    phase_unaryRow width u a (fun W v => v.signExtend (W + a)) phaseKeyBank (by decide)
      (exists_wordSignExtendTM a)

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseSchedules.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCompute

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Register schedules for memory instructions

An immediate read writes its address key then performs one lookup. Instruction schedules
sequence these reads, compute a result and make one final assignment. The represented memory
is unchanged before the last assignment, so every table scan charges the original footprint.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_fetchBlock`: write an immediate key and load the addressed RAM word.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- Fetching an in-range immediate address writes its key and loads its RAM word into a selected
word register, retaining the encoded memory and other known words. -/
theorem phase_fetchBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : ℤ) (dst : Fin 3) (hz : InRange a z) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (PhaseState a fn (fun x i =>
        Function.update (Function.update (regs x i) 1 (some (keyBits a i.width z)))
          (phaseMemoryBank dst 2) (some (bvBits (i.cfg.mem z)))))) := by
  obtain ⟨K⟩ := phase_keyBlock a fn regs z
  obtain ⟨L⟩ := phase_lookupBlock a fn
    (fun x i => Function.update (regs x i) 1 (some (keyBits a i.width z))) (fun _ => z) dst
    (by intro x i; exact Function.update_self ..)
    (fun i => phase_inRange_mono (by omega) hz)
  exact K.seq L

/-- Storing the known result word at an immediate address writes that address key, then performs
one assignment and updates the encoded memory and footprint. -/
theorem phase_storeImmediateBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (z : ℤ) (v : (x : List Bool) → (i : PhaseData) → BitVec i.width)
    (hz : InRange a z) (hv : ∀ x i, regs x i 4 = some (bvBits (v x i))) :
    Nonempty (PhaseBlock (PhaseState a fn regs)
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (v x i) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  obtain ⟨K⟩ := phase_keyBlock a fn regs z
  obtain ⟨A⟩ := phase_assignBlock a fn
    (fun x i => Function.update (regs x i) 1 (some (keyBits a i.width z))) (fun _ => z) v
    (by intro x i; exact Function.update_self ..)
    (by intro x i; simpa only [Function.update_of_ne (by decide : (4 : Fin 8) ≠ 1)] using hv x i)
    (fun i => phase_inRange_mono (by omega) hz)
  exact K.seq A

/-- A constant-word instruction computes its constant on register four, writes its destination
key and assigns that word once. This schedule is shared by `one` and each fixed coin branch. -/
theorem phase_constantSchedule (a : ℕ) (fn : Bool) (z value : ℤ) (hz : InRange a z) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (BitVec.ofInt i.width value) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  obtain ⟨V⟩ := phase_constBlock a fn (fun _ _ _ => none) value
  obtain ⟨S⟩ := phase_storeImmediateBlock a fn
    (fun _ i => Function.update (fun _ => none) 4 (some (bvBits (BitVec.ofInt i.width value))))
    z (fun _ i => BitVec.ofInt i.width value) hz (by intro x i; exact Function.update_self ..)
  exact V.seq S

/-- A binary arithmetic instruction fetches its two original-memory operands, computes the
result and assigns it once at its immediate destination.

**Proof sketch.** Two `phase_fetchBlock` calls load registers two and three. Known-register
updates preserve the first operand during the second fetch. `phase_arithBlock` computes into
register four, and `phase_storeImmediateBlock` makes the sole memory change. `PhaseBlock.seq`
combines the four blocks and their uniform allowances. -/
theorem phase_binarySchedule (a : ℕ) (fn : Bool) (z j k : ℤ)
    (hz : InRange a z) (hj : InRange a j) (hk : InRange a k) (op : PhaseArith) :
    Nonempty (PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert z i.cells)
        { i.cfg with mem := Function.update i.cfg.mem z (op.value (i.cfg.mem j) (i.cfg.mem k)) }
        (Function.Embedding.refl _) i.origins (F.cfg ()))) := by
  let r₀ : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool) := fun _ _ _ => none
  let r₁ := fun x i => Function.update
    (Function.update (r₀ x i) 1 (some (keyBits a i.width j))) 2 (some (bvBits (i.cfg.mem j)))
  let r₂ := fun x i => Function.update
    (Function.update (r₁ x i) 1 (some (keyBits a i.width k))) 3 (some (bvBits (i.cfg.mem k)))
  let r₃ := fun x i => Function.update (r₂ x i) 4
    (some (bvBits (op.value (i.cfg.mem j) (i.cfg.mem k))))
  obtain ⟨J⟩ := phase_fetchBlock a fn r₀ j 0 hj
  simp only [phaseMemoryBank_apply] at J
  obtain ⟨K⟩ := phase_fetchBlock a fn r₁ k 1 hk
  simp only [phaseMemoryBank_apply] at K
  obtain ⟨O⟩ := phase_arithBlock a fn r₂ (fun i => i.cfg.mem j) (fun i => i.cfg.mem k) op
    (by intro x i; rfl) (by intro x i; rfl)
  obtain ⟨S⟩ := phase_storeImmediateBlock a fn r₃ z
    (fun _ i => op.value (i.cfg.mem j) (i.cfg.mem k)) hz (by intro x i; rfl)
  obtain ⟨JK⟩ := J.seq K
  obtain ⟨JKO⟩ := JK.seq O
  exact JKO.seq S

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseSemantics.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseControl
import TCSlib.Complexity.RAMSimulation.Sim.PhaseOperations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Semantic postconditions of instruction phases

The tape schedules describe memory words and register contents. The semantic postcondition
connects their final encoding with the extended RAM step for any program whose current
instruction is the one being simulated and any compatible coin stream.

## Main definitions

* `WordRAM.Sim.PhasePost`: the next RAM step, encoding and selected program counter.

## Main results

* `WordRAM.Sim.phase_post_of_write`: a correct final memory assignment gives the semantic
  next-instruction postcondition.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; §2.1.2.)
-/

namespace WordRAM.Sim

open Turing

/-- The frame encodes the next extended RAM configuration for every matching program and
compatible coin stream, and its program counter agrees with the selected next/jump exit. -/
def PhasePost (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ) (taken b : Bool)
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) : Prop :=
  ∀ (P : XProgram) (ρ : List Bool), P.getD i.cfg.pc (.base .reject) = ins →
    (∀ z : ℤ, ins = .coin z → ρ.getD i.cfg.rd false = b) →
    ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
      Encodes a fn (i.cells ∪ ins.touches i.cfg.mem) c'
        (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
      (if taken then c'.pc = label else c'.pc = i.cfg.pc + 1)

/-- The semantic postcondition quantifies matching fetches and compatible coin streams, then
provides the next configuration, its enlarged encoding and the selected program counter. -/
theorem phasePost_iff (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ) (taken b : Bool)
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) :
    PhasePost a fn ins label taken b x i F ↔
      ∀ (P : XProgram) (ρ : List Bool), P.getD i.cfg.pc (.base .reject) = ins →
        (∀ z : ℤ, ins = .coin z → ρ.getD i.cfg.rd false = b) →
        ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
          Encodes a fn (i.cells ∪ ins.touches i.cfg.mem) c'
            (Function.Embedding.refl _) i.origins (F.cfg ()) ∧
          (if taken then c'.pc = label else c'.pc = i.cfg.pc + 1) := Iff.rfl

/-- A final assignment at a touched address gives the next-instruction postcondition whenever
the RAM step has that memory and output and advances its program counter.

**Proof sketch.** Enlarge the assignment's footprint from `insert z T` to `T ∪ touches` with
`phase_encodes_mono`. The matching RAM step may also update its coin count or control, which
are absent from the tape encoding; `phase_encodes_congr` transfers the encoded memory/output to
that configuration. -/
theorem phase_post_of_write (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ) (b : Bool)
    (x : List Bool) (i : PhaseData) (F : PhaseFrame x) (z : ℤ) (v : BitVec i.width)
    (he : Encodes a fn (insert z i.cells) { i.cfg with mem := Function.update i.cfg.mem z v }
      (Function.Embedding.refl _) i.origins (F.cfg ()))
    (hz : z ∈ ins.touches i.cfg.mem)
    (hstep : ∀ (P : XProgram) (ρ : List Bool), P.getD i.cfg.pc (.base .reject) = ins →
      (∀ k : ℤ, ins = .coin k → ρ.getD i.cfg.rd false = b) →
      ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
        c'.mem = Function.update i.cfg.mem z v ∧ c'.out = i.cfg.out ∧ c'.pc = i.cfg.pc + 1) :
    PhasePost a fn ins label false b x i F := by
  apply (phasePost_iff a fn ins label false b x i F).mpr
  intro P ρ hf hc
  obtain ⟨c', hs, hm, ho, hp⟩ := hstep P ρ hf hc
  have hT : insert z i.cells ⊆ i.cells ∪ ins.touches i.cfg.mem := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hq | hq
    · subst q
      exact Finset.mem_union_right _ hz
    · exact Finset.mem_union_left _ hq
  have he' := phase_encodes_mono fn _ _ _ (Function.Embedding.refl _) i.origins (F.cfg ()) he hT
  refine ⟨c', hs, ?_, hp⟩
  exact (phase_encodes_congr fn _ { i.cfg with mem := Function.update i.cfg.mem z v } c'
    (Function.Embedding.refl _) i.origins (F.cfg ()) (F.cfg ()) rfl rfl rfl hm.symm ho.symm).mp he'

/-- A deterministic memory-writing schedule with the specified RAM step semantics gives a
fresh-entry phase with a next exit and an unused jump exit.

**Proof sketch.** `phase_machine_ofBlock` supplies the finite control and two-exit run.
`PhaseMachine.weaken` changes its memory-layout postcondition to `PhasePost` using
`phase_post_of_write`, without changing the machine or its allowance. -/
theorem phase_memoryMachine (a : ℕ) (fn : Bool) (ins : XInstr) (label : ℕ)
    (z : PhaseData → ℤ) (v : (x : List Bool) → (i : PhaseData) → BitVec i.width)
    (R : PhaseBlock (PhaseState a fn (fun _ _ _ => none))
      (fun x i F => Encodes a fn (insert (z i) i.cells)
        { i.cfg with mem := Function.update i.cfg.mem (z i) (v x i) }
        (Function.Embedding.refl _) i.origins (F.cfg ())))
    (hz : ∀ i, z i ∈ ins.touches i.cfg.mem)
    (hstep : ∀ (b : Bool) (x : List Bool) (i : PhaseData) (P : XProgram) (ρ : List Bool),
      P.getD i.cfg.pc (.base .reject) = ins →
      (∀ k : ℤ, ins = .coin k → ρ.getD i.cfg.rd false = b) →
      ∃ c' : XCfg i.width, xstep P x ρ i.cfg = .inl c' ∧
        c'.mem = Function.update i.cfg.mem (z i) (v x i) ∧
        c'.out = i.cfg.out ∧ c'.pc = i.cfg.pc + 1) :
    Nonempty (PhaseMachine false (PhaseState a fn (fun _ _ _ => none))
      (fun b x i F => PhasePost a fn ins label false b x i F) (fun _ _ _ => false)) := by
  obtain ⟨M⟩ := phase_machine_ofBlock R
  apply M.weaken (by intro x i F hp; exact hp)
  intro b x i F he
  exact phase_post_of_write a fn ins label b x i F (z i) (v x i) he (hz i) (hstep b x i)

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseTable.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Memory-table invariants for instruction phases

The phase machines access a RAM cell through its two's-complement key. These lemmas connect
`Turing.keyLookup` and `Turing.keyAssign` to the memory represented by `TableOf`. Range
hypotheses are explicit: keys identify cells only within their signed range.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.keyBits_eq_iff`: equality of in-range keys is equality of cells.
* `WordRAM.Sim.tableOf_mono`, `WordRAM.Sim.tableOf_widths`, `WordRAM.Sim.tableOf_length_le`:
  footprint monotonicity, register widths and the entry-count bound.
* `WordRAM.Sim.tableOf_keyLookup`, `WordRAM.Sim.tableOf_keyLookup_default`: correct memory
  lookup, with the zero default used by the machine row.
* `WordRAM.Sim.phase_bvBits_zero`: the all-false representation of the zero word.
* `WordRAM.Sim.tableOf_keyAssign`: the memory invariant after an assignment.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9: memory represented by address-value pairs.)
-/

namespace WordRAM.Sim

open Turing

/-- Two cells in the signed key range have the same key exactly when they are equal.

**Proof sketch.** `bvBits_injective` recovers the words from their bit lists.
`WordRAM.toInt_wd` recovers each integer from its word, using the supplied range hypotheses. -/
theorem keyBits_eq_iff {a W : ℕ} {i j : ℤ} (hi : InRange (W + a) i)
    (hj : InRange (W + a) j) : keyBits a W i = keyBits a W j ↔ i = j := by
  constructor
  · intro h
    have hw := bvBits_injective (by simpa only [keyBits_def] using h)
    have he := congrArg BitVec.toInt hw
    exact (toInt_wd hi).symm.trans (he.trans (toInt_wd hj))
  · rintro rfl
    rfl

/-- Enlarging the allowed cell set preserves the memory represented by a table. -/
theorem tableOf_mono {a W : ℕ} {T U : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) (hTU : T ⊆ U) :
    TableOf a W U m es := by
  obtain ⟨hn, hs, hc⟩ := (tableOf_iff a W T m es).mp h
  refine (tableOf_iff a W U m es).mpr ⟨hn, ?_, hc⟩
  intro e he
  obtain ⟨z, hz, hr, heq⟩ := hs e he
  exact ⟨z, hTU hz, hr, heq⟩

/-- Every key in a represented memory has the key width, and every value has the word width. -/
theorem tableOf_widths {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) :
    ∀ e ∈ es, e.1.length = W + a ∧ e.2.length = W := by
  intro e he
  obtain ⟨z, _, _, rfl⟩ := ((tableOf_iff a W T m es).mp h).2.1 e he
  exact ⟨by rw [keyBits_def, bvBits_length], bvBits_length _⟩

/-- A represented memory table has at most as many entries as its allowed cell set.

**Proof sketch.** The distinct table keys form a finset with `es.length` elements by
`List.toFinset_card_of_nodup`. Entry soundness puts it inside the image of the allowed cell
set under `keyBits`; `Finset.card_le_card` and `Finset.card_image_le` give the bound. -/
theorem tableOf_length_le {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) : es.length ≤ T.card := by
  obtain ⟨hn, hs, _⟩ := (tableOf_iff a W T m es).mp h
  have hsub : (es.map Prod.fst).toFinset ⊆ T.image (keyBits a W) := by
    intro k hk
    obtain ⟨e, he, hek⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    obtain ⟨z, hz, _, heq⟩ := hs e he
    refine Finset.mem_image.mpr ⟨z, hz, ?_⟩
    simpa only [heq] using hek
  calc
    es.length = (es.map Prod.fst).toFinset.card := by
      rw [List.toFinset_card_of_nodup hn, List.length_map]
    _ ≤ (T.image (keyBits a W)).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le

/-- Looking up a cell in the signed key range returns its memory word, defaulting to the
zero word when the cell has no stored entry.

**Proof sketch.** Read `keyLookup_def` and inspect the first matching entry. If it exists,
`TableOf` identifies its cell and `keyBits_eq_iff` identifies that cell with the query.
If it does not exist, the coverage clause of `TableOf` forces the query's memory word to be
zero, since any nonzero word would have supplied a matching key. -/
theorem tableOf_keyLookup {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) {z : ℤ}
    (hz : InRange (W + a) z) :
    (keyLookup es (keyBits a W z)).getD (bvBits (0 : BitVec W)) = bvBits (m z) := by
  obtain ⟨_, hs, hc⟩ := (tableOf_iff a W T m es).mp h
  rw [keyLookup_def]
  cases hf : es.find? (fun e => e.1 = keyBits a W z) with
  | none =>
    have hzero : m z = 0 := by
      by_contra hn
      obtain ⟨e, he, hek⟩ := List.mem_map.mp (hc z hz hn)
      have hnot := (List.find?_eq_none.mp hf) e he
      exact hnot (by simpa only [decide_eq_true_eq] using hek)
    rw [hzero]
    rfl
  | some e =>
    have he := List.mem_of_find?_eq_some hf
    have hek : e.1 = keyBits a W z :=
      of_decide_eq_true (List.find?_some (p := fun e : List Bool × List Bool => e.1 = keyBits a W z) hf)
    obtain ⟨w, _, hw, heq⟩ := hs e he
    have hwz : w = z := (keyBits_eq_iff hw hz).mp (by simpa only [heq] using hek)
    subst w
    simp only [Option.map_some, Option.getD_some, heq]

/-- The bits of the zero word are precisely a word-width list of false bits. -/
theorem phase_bvBits_zero (W : ℕ) : bvBits (0 : BitVec W) = List.replicate W false := by
  have hz : (fun i : Fin W => (0 : BitVec W).getLsbD i.val) = fun _ => false := by
    funext i
    exact BitVec.getLsbD_zero
  rw [bvBits_def, hz, List.ofFn_const]

/-- The lookup row's all-false default returns exactly the queried memory word. -/
theorem tableOf_keyLookup_default {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) {z : ℤ}
    (hz : InRange (W + a) z) :
    (keyLookup es (keyBits a W z)).getD (List.replicate W false) = bvBits (m z) := by
  simpa only [phase_bvBits_zero] using tableOf_keyLookup h hz

/-! ## Assignment's list invariant -/

/-- Assignment retains precisely the entries with different keys, together with the new entry.

**Proof sketch.** Use `keyAssign_def`. When the key occurs, membership in the replacement map
is membership in an unchanged entry or in the inserted pair; the occurrence supplies a witness
for the inserted pair. When it does not occur, the definition appends that pair, and every old
entry has a different key. -/
private theorem phase_keyAssign_mem (es : List (List Bool × List Bool)) (k v : List Bool)
    (e : List Bool × List Bool) :
    e ∈ keyAssign es k v ↔ e = (k, v) ∨ e ∈ es ∧ e.1 ≠ k := by
  rw [keyAssign_def]
  split_ifs with h
  · obtain ⟨e₀, he₀, hk₀⟩ := List.any_eq_true.mp h
    have hk₀' : e₀.1 = k := of_decide_eq_true hk₀
    constructor
    · intro he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      split_ifs with hk
      · exact Or.inl rfl
      · exact Or.inr ⟨he', hk⟩
    · rintro (rfl | ⟨he, hk⟩)
      · exact List.mem_map.mpr ⟨e₀, he₀, if_pos hk₀'⟩
      · exact List.mem_map.mpr ⟨e, he, if_neg hk⟩
  · have hnone : ∀ e' ∈ es, e'.1 ≠ k := by
      intro e' he' hk
      apply h
      exact List.any_eq_true.mpr ⟨e', he', by simpa only [decide_eq_true_eq] using hk⟩
    constructor
    · intro he
      rcases List.mem_append.mp he with he | he
      · exact Or.inr ⟨he, hnone e he⟩
      · exact Or.inl (List.mem_singleton.mp he)
    · rintro (rfl | ⟨he, _⟩)
      · exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
      · exact List.mem_append.mpr (Or.inl he)

/-- Assignment preserves distinct keys.

**Proof sketch.** In the replacement case the list of keys is unchanged. In the append case,
`List.any_eq_true` shows that the appended key was absent, so `List.nodup_append` applies. -/
private theorem phase_keyAssign_nodup (es : List (List Bool × List Bool)) (k v : List Bool)
    (hn : (es.map Prod.fst).Nodup) : ((keyAssign es k v).map Prod.fst).Nodup := by
  rw [keyAssign_def]
  split_ifs with h
  · have heq : (es.map (fun e => if e.1 = k then (k, v) else e)).map Prod.fst =
        es.map Prod.fst := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e _
      by_cases hk : e.1 = k
      · simp only [Function.comp_apply, if_pos hk]
        exact hk.symm
      · simp only [Function.comp_apply, if_neg hk]
    rw [heq]
    exact hn
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨hn, ?_, ?_⟩
    · exact List.nodup_singleton k
    · intro a ha b hb hab
      have hb' : b = k := List.mem_singleton.mp hb
      rw [hab, hb'] at ha
      obtain ⟨e, he, hek⟩ := List.mem_map.mp ha
      apply h
      exact List.any_eq_true.mpr ⟨e, he, by simpa only [decide_eq_true_eq] using hek⟩

/-- Assigning an in-range cell preserves the represented memory, adding that cell to the
allowed footprint and updating its word.

**Proof sketch.** `phase_keyAssign_nodup` preserves distinct keys, and
`phase_keyAssign_mem` separates the new entry from unchanged entries with different keys.
`keyBits_eq_iff` turns different keys into different in-range cells, so the unchanged entries
remain sound for the updated memory. For coverage the assigned cell has its new entry;
every other nonzero cell keeps its old entry. -/
theorem tableOf_keyAssign {a W : ℕ} {T : Finset ℤ} {m : ℤ → BitVec W}
    {es : List (List Bool × List Bool)} (h : TableOf a W T m es) {z : ℤ}
    (hz : InRange (W + a) z) (v : BitVec W) :
    TableOf a W (insert z T) (Function.update m z v)
      (keyAssign es (keyBits a W z) (bvBits v)) := by
  obtain ⟨hn, hs, hc⟩ := (tableOf_iff a W T m es).mp h
  refine (tableOf_iff a W (insert z T) (Function.update m z v) _).mpr
    ⟨phase_keyAssign_nodup es _ _ hn, ?_, ?_⟩
  · intro e he
    rcases (phase_keyAssign_mem es _ _ e).mp he with heq | ⟨he, hne⟩
    · refine ⟨z, Finset.mem_insert_self _ _, hz, ?_⟩
      rw [heq, Function.update_self]
    · obtain ⟨y, hy, hyr, heq⟩ := hs e he
      have hyz : y ≠ z := by
        intro hyz
        apply hne
        rw [heq, hyz]
      refine ⟨y, Finset.mem_insert_of_mem hy, hyr, ?_⟩
      rw [heq, Function.update_of_ne hyz]
  · intro y hyr hnonzero
    by_cases hyz : y = z
    · subst y
      refine List.mem_map.mpr ⟨(keyBits a W z, bvBits v), ?_, rfl⟩
      exact (phase_keyAssign_mem es _ _ _).mpr (Or.inl rfl)
    · have hm : m y ≠ 0 := by
        simpa only [Function.update_of_ne hyz] using hnonzero
      obtain ⟨e, he, hek⟩ := List.mem_map.mp (hc y hyr hm)
      have hne : e.1 ≠ keyBits a W z := by
        intro hez
        exact hyz ((keyBits_eq_iff hyr hz).mp (hek.symm.trans hez))
      exact List.mem_map.mpr ⟨e, (phase_keyAssign_mem es _ _ e).mpr (Or.inr ⟨he, hne⟩), hek⟩

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseTape.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseCore
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framing and placement of instruction rows

The word and keyed-table rows run on five selected tapes. Their native endpoints preserve all
other data. These lemmas read the tape predicates through their published characterizations
and place the bounded runs on the simulation's eight tapes.

## Main definitions

No new definitions.

## Main results

* `WordRAM.Sim.phase_wordAt_congr`: word layout depends only on the selected tape and head.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- A word layout is unchanged when its tape and head are unchanged, regardless of control,
input head and output. -/
theorem phase_wordAt_congr {K : ℕ} {S S' : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (e : Turing.Cfg K Bool S' x) (r : Fin K) (w : List Bool)
    (ht : d.workTapes r = e.workTapes r) (hp : d.workTapePos r = e.workTapePos r) :
    WordAt d r w ↔ WordAt e r w := by
  rw [wordAt_iff, wordAt_iff, ht, hp]

/-- A keyed-table layout depends only on its physical tape, including the blank right tail. -/
theorem phase_keyTableAt_congr {K : ℕ} {S S' : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (e : Turing.Cfg K Bool S' x) (r : Fin K) (o : ℤ)
    (es : List (List Bool × List Bool)) (ht : d.workTapes r = e.workTapes r) :
    KeyTableAt d r o es ↔ KeyTableAt e r o es := by
  rw [keyTableAt_iff, keyTableAt_iff, tableAt_iff, tableAt_iff, ht]

/-- Encoding depends on the memory and output of the RAM configuration and the work tapes,
work heads and output of the Turing configuration, independently of both controls and the input
head. -/
theorem phase_encodes_congr {K a W : ℕ} {S S' : Type} {x : List Bool} (fn : Bool)
    (T : Finset ℤ) (c c' : XCfg W) (σ : Fin 8 ↪ Fin K) (o : Fin 8 → ℤ)
    (d : Turing.Cfg K Bool S x) (e : Turing.Cfg K Bool S' x)
    (ht : d.workTapes = e.workTapes) (hp : d.workTapePos = e.workTapePos)
    (ho : d.output = e.output) (hm : c.mem = c'.mem) (hc : c.out = c'.out) :
    Encodes a fn T c σ o d ↔ Encodes a fn T c' σ o e := by
  simp only [encodes_iff, keyTableAt_iff, tableAt_iff, wordAt_iff, ht, hp, ho, hm, hc]

/-- Placing a bounded source run on selected tapes preserves its time and radius bounds and
frames every unselected tape. The source starts at the host's selection, with empty output.

**Proof sketch.** `embedEmitCfg_select` identifies the host start. The lockstep
`embedEmitTM_runFrom` then transfers the run and cut; selected head positions are the source's
by `embedEmitCfg_selected_pos`, and the other heads stay fixed by
`embedEmitCfg_unselected`. -/
theorem phase_reaches_embed {m : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin 8) (M : MultiTapeTM m Bool S) (d : Turing.Cfg 8 Bool S x)
    (X : Set (Option S)) (B E : ℕ) (post : Turing.Cfg m Bool S x)
    (h : ReachesWithin M (d.select σ) X B E post) :
    ReachesWithin (embedEmitTM σ M) d X B E
      (embedEmitCfg σ d.workTapes d.workTapePos d.output post) := by
  obtain ⟨t, ht, hcut, henv, hrun⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h
  have transport (s : ℕ) : (embedEmitTM σ M).runFrom d s =
      embedEmitCfg σ d.workTapes d.workTapePos d.output (M.runFrom (d.select σ) s) := by
    have hh := embedEmitTM_runFrom σ M d.workTapes d.workTapePos d.output (d.select σ) s
    rwa [embedEmitCfg_select] at hh
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · intro s hs
    rw [transport, embedEmitCfg_state]
    exact hcut s hs
  · intro s hs j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨r, rfl⟩ := hj
      rw [transport, embedEmitCfg_selected_pos]
      simpa only [Cfg.select_eq] using henv s hs r
    · rw [transport, (embedEmitCfg_unselected σ d.workTapes d.workTapePos d.output
        (M.runFrom (d.select σ) s) j hj).2, sub_self, abs_zero]
      exact Int.natCast_nonneg E
  · rw [transport, hrun]

/-- Rewriting a delimited word with another word of the same length preserves its delimiters
and establishes the new word layout.

**Proof sketch.** Read `wordWrite_apply` inside the word interval and `wordAt_iff` at its
unchanged boundaries. Off the interval, the allowed offsets are just `-1` and the word length;
`bufferTape_left` and `bufferTape_nat` identify both boundary cells as blank. -/
theorem phase_wordAt_write {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (r : Fin K) (w v : List Bool)
    (hw : WordAt d r w) (hv : v.length = w.length) :
    WordAt { d with workTapes := wordWrite d r v } r v := by
  apply (wordAt_iff _ r v).mpr
  intro p hp hp'
  change wordWrite d r v r (d.workTapePos r + p) = FinTM.bufferTape v p
  rw [wordWrite_apply]
  by_cases h : 0 ≤ p ∧ p < (v.length : ℤ)
  · rw [if_pos ⟨rfl, by omega, by omega⟩, add_sub_cancel_left]
  · rw [if_neg (by omega), (wordAt_iff d r w).mp hw p hp (by omega)]
    have hb : p = -1 ∨ p = (v.length : ℤ) := by omega
    rcases hb with rfl | rfl
    · rw [FinTM.bufferTape_left, FinTM.bufferTape_left]
    · rw [FinTM.bufferTape_nat, FinTM.bufferTape_nat,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- A simultaneous control/input-head update and replacement of one selected tape commutes
with forwarding embedding; all unselected tapes remain the host frame.

**Proof sketch.** Apply `embedEmitCfg_eq`. Selection preserves each selected tape and head by
`Cfg.select_eq`; the update at a selected index agrees by injectivity of the tape embedding.
At every unselected index the update is absent, by `Function.update_of_ne`. -/
theorem phase_embed_update {m : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin 8) (d : Turing.Cfg 8 Bool S x) (q : Option S)
    (ip : Fin (x.length + 2)) (r : Fin m) (u : ℤ → Option Bool) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output
      { (d.select σ) with
        state := q
        inputPos := ip
        workTapes := Function.update (d.select σ).workTapes r u } =
      { d with state := q, inputPos := ip, workTapes := Function.update d.workTapes (σ r) u } := by
  apply embedEmitCfg_eq
  · rfl
  · rfl
  · simp only [Cfg.select_eq, List.append_nil]
  · intro i
    constructor
    · change Function.update (d.select σ).workTapes r u i =
        Function.update d.workTapes (σ r) u (σ i)
      rw [Function.update_apply, Function.update_apply]
      simp only [σ.injective.eq_iff, Cfg.select_eq]
    · simp only [Cfg.select_eq]
  · intro j hj
    have hne : j ≠ σ r := fun h => hj ⟨r, h.symm⟩
    exact ⟨(Function.update_of_ne hne u d.workTapes).symm, rfl⟩

/-! ## Single-tape replacement -/

/-- A conditional patch confined to one tape is a function update of that tape. -/
private theorem phase_single_tape_update {K : ℕ} (tapes : Fin K → ℤ → Option Bool)
    (r : Fin K) (p : Fin K → ℤ → Prop) [∀ j q, Decidable (p j q)]
    (v : Fin K → ℤ → Option Bool) :
    (fun j q => if j = r ∧ p j q then v j q else tapes j q) =
      Function.update tapes r (fun q => if p r q then v r q else tapes r q) := by
  funext j q
  rw [Function.update_apply]
  by_cases hj : j = r
  · subst j
    simp only [if_true, true_and]
  · simp only [hj, false_and, if_false]

/-- A word write is replacement of just its destination tape; the replacement keeps that
tape's outer frame and writes the new word over its length. -/
theorem phase_wordWrite_as_update {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (r : Fin K) (w : List Bool) :
    wordWrite d r w = Function.update d.workTapes r (fun q =>
      if d.workTapePos r ≤ q ∧ q < d.workTapePos r + (w.length : ℤ)
      then FinTM.bufferTape w (q - d.workTapePos r) else d.workTapes r q) := by
  exact (funext fun j => funext fun q => wordWrite_apply d r w j q).trans
    (phase_single_tape_update d.workTapes r
      (fun j q => d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ))
      (fun j q => FinTM.bufferTape w (q - d.workTapePos j)))

/-- A word on a selected source tape is exactly the word on its corresponding host tape. -/
theorem phase_wordAt_select {m : ℕ} {S : Type} {x : List Bool} (σ : Fin m ↪ Fin 8)
    (d : Turing.Cfg 8 Bool S x) (r : Fin m) (w : List Bool) :
    WordAt (d.select σ) r w ↔ WordAt d (σ r) w := by
  simp only [wordAt_iff, Cfg.select_eq]

/-- A keyed table on a selected source tape is exactly that table on the corresponding host
tape, with the same origin and blank tail. -/
theorem phase_keyTableAt_select {m : ℕ} {S : Type} {x : List Bool} (σ : Fin m ↪ Fin 8)
    (d : Turing.Cfg 8 Bool S x) (r : Fin m) (o : ℤ) (es : List (List Bool × List Bool)) :
    KeyTableAt (d.select σ) r o es ↔ KeyTableAt d (σ r) o es := by
  simp only [keyTableAt_iff, tableAt_iff, Cfg.select_eq]

/-- A native word-write endpoint embeds as the same word write on the corresponding host
tape, with its state and input-head updates preserved. -/
theorem phase_embed_wordWrite {m : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin 8) (d : Turing.Cfg 8 Bool S x) (q : Option S)
    (ip : Fin (x.length + 2)) (r : Fin m) (w : List Bool) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output
      { (d.select σ) with
        state := q
        inputPos := ip
        workTapes := wordWrite (d.select σ) r w } =
      { d with state := q, inputPos := ip, workTapes := wordWrite d (σ r) w } := by
  simpa only [phase_wordWrite_as_update, Cfg.select_eq] using
    phase_embed_update σ d q ip r (fun z =>
      if d.workTapePos (σ r) ≤ z ∧ z < d.workTapePos (σ r) + (w.length : ℤ)
      then FinTM.bufferTape w (z - d.workTapePos (σ r)) else d.workTapes (σ r) z)

/-- A keyed-table write is replacement of its single destination tape, retaining that tape's
outer frame beyond the written layout. -/
theorem phase_keyTableWrite_as_update {K : ℕ} {S : Type} {x : List Bool}
    (d : Turing.Cfg K Bool S x) (r : Fin K) (o : ℤ) (es : List (List Bool × List Bool)) :
    keyTableWrite d r o es = Function.update d.workTapes r (fun q =>
      if o ≤ q ∧ q < o + (keyTableLength es : ℤ)
      then fieldsTape (tableFields [true] (keyFields es)) (q - o) else d.workTapes r q) :=
  (funext fun j => funext fun q => keyTableWrite_apply d r o es j q).trans
    (phase_single_tape_update d.workTapes r
      (fun _ q => o ≤ q ∧ q < o + (keyTableLength es : ℤ))
      (fun _ q => fieldsTape (tableFields [true] (keyFields es)) (q - o)))

/-- A native keyed-table write embeds as the same layout write on its corresponding host tape,
with its state and input-head updates preserved. -/
theorem phase_embed_keyTableWrite {m : ℕ} {S : Type} {x : List Bool}
    (σ : Fin m ↪ Fin 8) (d : Turing.Cfg 8 Bool S x) (q : Option S)
    (ip : Fin (x.length + 2)) (r : Fin m) (o : ℤ) (es : List (List Bool × List Bool)) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output
      { (d.select σ) with
        state := q
        inputPos := ip
        workTapes := keyTableWrite (d.select σ) r o es } =
      { d with state := q, inputPos := ip, workTapes := keyTableWrite d (σ r) o es } := by
  simpa only [phase_keyTableWrite_as_update, Cfg.select_eq] using
    phase_embed_update σ d q ip r (fun z =>
      if o ≤ z ∧ z < o + (keyTableLength es : ℤ)
      then fieldsTape (tableFields [true] (keyFields es)) (z - o) else d.workTapes (σ r) z)

end WordRAM.Sim
```

## ===== TCSlib/Complexity/RAMSimulation/Sim/PhaseTests.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.PhaseControl

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Word tests and branching instruction blocks

The sign and nonzero tests inspect a known operand without changing the frame. They have two
live exits, and can be prefixed by an ordinary instruction block through the same seam contract.

## Main definitions

* `WordRAM.Sim.PhaseTestKind`: sign or nonzero testing of a word.
* `WordRAM.Sim.PhaseBranch`: a bounded two-exit deterministic block.

## Main results

* `WordRAM.Sim.phase_embed_state`: installing only a native endpoint state preserves the frame.
* `WordRAM.Sim.PhaseTestKind.native`: the common native word-test interface.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9.)
-/

namespace WordRAM.Sim

open Turing

/-- The two native word tests used by branch and output instructions. -/
inductive PhaseTestKind where
  | sign
  | nonzero

/-- The bit returned by the selected sign or nonzero test. -/
def PhaseTestKind.bit {W : ℕ} (op : PhaseTestKind) (u : BitVec W) : Bool :=
  match op with
  | .sign => decide (u.toInt < 0)
  | .nonzero => decide (u ≠ 0)

/-- The sign test reports a negative signed value, and the nonzero test reports a nonzero word. -/
theorem PhaseTestKind.bit_eq {W : ℕ} (op : PhaseTestKind) (u : BitVec W) :
    op.bit u = match op with
      | .sign => decide (u.toInt < 0)
      | .nonzero => decide (u ≠ 0) := rfl

/-- The two native tests share the same untouched-frame, restored-head and linear-bound
interface, with distinct yes and no exits. -/
theorem PhaseTestKind.native (op : PhaseTestKind) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (M : MultiTapeTM 5 Bool S)
      (entry yes no : S) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (d : Turing.Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → ScratchBlank d →
        ReachesWithin M d {some yes, some no} (C * (W + 1)) (C * (W + 1))
          { d with state := some (if op.bit u then yes else no) } := by
  cases op with
  | sign => simpa only [bit_eq, decide_eq_true_eq] using exists_wordSignTM
  | nonzero => simpa only [bit_eq, decide_eq_true_eq] using exists_wordNonzeroTM

/-- A native endpoint that changes only control embeds to the same host frame with that
control, because selecting and reinstalling a bank leaves its original tape functions intact. -/
theorem phase_embed_state {S : Type} {x : List Bool} (σ : Fin 5 ↪ Fin 8)
    (d : Turing.Cfg 8 Bool S x) (q : Option S) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output { d.select σ with state := q } =
      { d with state := q } := by
  simpa only [Cfg.select_eq, Function.update_eq_self] using
    phase_embed_update σ d q d.inputPos 0 (d.workTapes (σ 0))

/-- A finite deterministic two-exit block returns a frame satisfying its postcondition at the
yes or no exit selected by its indexed Boolean flag, restores heads and obeys phase allowances. -/
structure PhaseBranch
    (P Q : (x : List Bool) → PhaseData → PhaseFrame x → Prop)
    (flag : List Bool → PhaseData → Bool) where
  State : Type
  finite : Fintype State
  decEq : DecidableEq State
  machine : MultiTapeTM 8 Bool State
  entry : State
  yes : State
  no : State
  distinct : yes ≠ no
  constant : ℕ
  run : ∀ x i F, P x i F → ∃ G : PhaseFrame x, Q x i G ∧
    G.workTapePos = F.workTapePos ∧
    ReachesWithin machine (F.cfg entry) {some yes, some no}
      (constant * phaseTime i x) (constant * phaseSpace i x)
      (G.cfg (if flag x i then yes else no))

/-- Testing a known operand in register two gives a two-exit block with the selected sign or
nonzero flag, without changing its encoding, known words or frame.

**Proof sketch.** Choose the common native test contract, select the arithmetic tape bank and
supply the known word and encoded blank scratch. `phase_reaches_embed` places its run and
`phase_embed_state` identifies the unchanged frame at its selected exit. The native linear
allowances are bounded by the common phase units. -/
theorem phase_testBlock (a : ℕ) (fn : Bool)
    (regs : (x : List Bool) → PhaseData → Fin 8 → Option (List Bool))
    (u : (i : PhaseData) → BitVec i.width) (op : PhaseTestKind)
    (hu : ∀ x i, regs x i 2 = some (bvBits (u i))) :
    Nonempty (PhaseBranch (PhaseState a fn regs) (PhaseState a fn regs)
      (fun _ i => op.bit (u i))) := by
  obtain ⟨S, hfin, hdec, M, entry, yes, no, C, hy, hM⟩ := op.native
  letI := hfin
  letI := hdec
  refine ⟨⟨S, inferInstance, inferInstance, embedEmitTM phaseArithBank M,
    entry, yes, no, hy, C, ?_⟩⟩
  intro x i F hp
  obtain ⟨he, hregs⟩ := (phaseState_iff a fn regs x i F).mp hp
  have hw : WordAt ((F.cfg entry).select phaseArithBank) 0 (bvBits (u i)) := by
    apply (phase_wordAt_select phaseArithBank (F.cfg entry) 0 _).mpr
    simpa only [phaseArithBank_apply] using
      (phase_wordAt_frame F entry 2 _).mpr (hregs 2 _ (hu x i))
  have hs := phase_scratch_select phaseArithBank F entry
    (by simp only [phaseArithBank_apply]; decide)
    (phase_frame_scratch fn i.cells i.cfg i.origins F he)
  have hn := hM (u i) ((F.cfg entry).select phaseArithBank)
    (by simp only [Cfg.select_eq, PhaseFrame.cfg_eq]) hw hs
  have hr := phase_reaches_embed phaseArithBank M (F.cfg entry) _ _ _ _ hn
  rw [phase_embed_state] at hr
  refine ⟨F, hp, rfl, ?_⟩
  apply ReachesWithin.mono _ (Nat.mul_le_mul_left C (phase_units i x).2.2.1)
    (Nat.mul_le_mul_left C (phase_units i x).2.2.2.1)
  simpa only [PhaseFrame.cfg_eq] using hr

end WordRAM.Sim
```
