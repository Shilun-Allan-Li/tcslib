## ===== campaign/items/ram-tm/briefs/COMMON.md =====

# RAM fills: rules common to every brief

These rules bind every RAM fill (tier 1 `fill-ram-wordsize`, tier 3 `fill-ram-classes`, and
later the tier 2 fills). Each brief adds its targets, owned file and route.

## Repository and base

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`, the same repository as your exchange
  checkout.
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
    `Quot.sound`, or, for a target that cites a still-admitted declaration, exactly that
    dependency on `sorryAx` and nothing else. Run it through a scratch file, not in the
    library;
  - every module that imports the owned file elaborates with zero errors.

## REPORT.md checklist

- [ ] The base, and each target: proved, or the frontier and the reason.
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

## ===== campaign/items/ram-tm/briefs/fill-ram-wordsize.md =====

# RAM fill (Codex): tier 1, the word size (`RAMSimulation/WordSize`, 3 admissions)

Read `COMMON.md` (bundled) first; its rules bind. **Fill name:** `fill-ram-wordsize`.
**Base:** the commit given in the dispatch prompt, on `complexity/ram-simulation`.

## What this is

`TCSlib/Complexity/RAMSimulation/WordSize.lean` defines the stage-2 word-size hypothesis:

```lean
def WordSizeComputable (W TW SW : ℕ → ℕ) : Prop :=
  ∃ M : Turing.FinTM Bool, ∀ x : List Bool, ∃ t ≤ TW x.length,
    M.ComputesInTime x (W x.length).bits t ∧ M.tm.spaceUsed (M.tm.initCfg x) t ≤ SW x.length
```

It also states three admitted results. Their statements were audited on 2026-10-14 and
rechecked against the base on 2026-11-17; they are frozen. **This fill proves all three.**

## Targets

1. **`WordSizeComputable.mono`**: larger bounds. This is the same machine and the same halting
   times. The definition is in the same file, so it may be unfolded.
2. **`wordSizeComputable_logSpace (c : ℕ)`**: some `a` with
   `WordSizeComputable (fun n => c * logSpace n) (fun n => a * (n + 1)) (fun n => a * logSpace n)`.
   The time is **linear** and the space is logarithmic.
3. **`wordSizeComputable_of_spaceConstructible (hS : SpaceConstructible S) (c : ℕ)`**: some `a`
   and `TW` with `WordSizeComputable (fun n => c * S n) TW (fun n => a * S n)`. The time `TW` is
   unconstrained, but it must be a function of `n` only.

## Route (the maintainer's reading; you choose the construction)

**Target 2.** One machine, in stages. Each stage after the first works on a word of length
`O(log n)`, so its time is far below linear.
- **First stage:** `Nat.bits |x|`. `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed`
  (`Build/Catalog`) gives a machine that computes `x ↦ Nat.bits |x|` within `c₀·(|x| + 1)` steps
  and `c₀·(Nat.size |x| + 1)` cells. The work-tape contract `Turing.exists_inputLengthTM`
  (`Build/InputLength`) writes `Nat.bits |x|` on a work tape within `C·(|x| + 1)` steps, with
  head envelope `C·(|bits |x|| + 1)`. It is the natural first stage of a composed machine.
- **Note:** `logSpace n = |Nat.bits n|` for `n ≥ 1`, and `logSpace 0 = 1`. Read `logSpace`
  through `Complexity.logSpace_eq`.
- **Next stages:** the length of that word in binary, then multiplication by the constant `c`
  (repeated addition, or shift-and-add), then emission as `Nat.bits (c * logSpace n)` on the
  output tape. `c = 0` gives the empty word.
- **Composition:** `Build/Seam` (`seamCompTM`, `seamCompTM_run`, `seamCompTM_run_ofCfg`,
  `seamCompTM_spaceUsed_le_add`, `seamCompTM_spaceUsed_le_add_ofCfg`) and `Build/Embed`
  (`embedSilentTM`). The time bound needs `poly(log n) ≤ a·(n + 1)` for a suitable `a`. Prove
  it once, as a private arithmetic lemma.
- **Not usable:** `Complexity.spaceConstructible_logSpace` (`SpaceComplexity/Constructible`)
  computes `Nat.bits (logSpace n)` in logarithmic space but bounds no time. Its private machine
  `b3a_log_machine` cannot be cited across files.

**Target 3.** `SpaceConstructible S` gives `logSpace ≤ S` and a machine `M_S` with
`M_S.ComputesInSpace (fun x => Nat.bits (S |x|)) (c_S * S ·)`. Read both through
`Complexity.spaceConstructible_iff` and `Turing.FinTM.computesInSpace_iff`.
- Run `M_S` with its output captured on a work tape (`embedSilentTM`), multiply by `c`, and emit.
- **Space:** `c_S·S + O(log (c·S) + 1) ≤ a·S`, because `S ≥ logSpace ≥ 1`.
- **Time:** `ComputesInSpace` gives each input a halting time. Take `TW n` to be the maximum
  over the `2^n` inputs of length `n` (a `Finset.sup` over `List.Vector`, or a classical choice
  of bound), plus the multiplication's cost.

**Shared helper.** Targets 2 and 3 both need "multiply a binary word on a work tape by the
constant `c`". Write it once as a private machine with its run and space lemmas, and cite it
twice.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/RAMSimulation/WordSize.lean`.
- **Imports:** you may add imports of existing `TCSlib/Complexity/TuringMachine/Build/*`
  modules, which the construction needs. List each one in `REPORT.md` with the reason. Do not
  add any other import.
- **Statements** stay byte-identical. The machines are private, in a section
  `/-! ## Machines -/` before the targets.

## Downstream check

`RAMSimulation/Simulation`, `RAMSimulation/Classes` and the facade
`TCSlib/Complexity/RAMSimulation.lean` import this file. Elaborate all three.

## Size and frontier

Target 2 is the hardest and may run to several hundred lines. Deliver in this order:
1. target 1;
2. the shared multiplication helper;
3. target 3;
4. target 2.

A frontier after any of these steps is acceptable; checkpoint zips are welcome.

## ===== campaign/items/ram-tm/recheck/README.md =====

# Statement recheck of the 14 admissions (2026-11-17, against `complexity/ram-simulation` at `8fe5003d`, whose Lean is `main` `5cb25d52`)

- **Statements:** all 14 elaborate on the branch (main builds them, `oleans-cc91f4`). Their
  class targets unfold to the shapes the stage-2 simulation delivers (`RamDefs.out.txt`). The
  nine tier 3 bound arithmetics close with `logSpace ≥ 1` and `logSpace ≤ S`. **No statement
  change is needed.**
- **Cited names:** all 51 identifiers cited in the three files' docstrings exist in the build
  (`RamCited.out.txt`, one hit each; `HaltsWithin.mono` resolves to `WordRAM.HaltsWithin.mono`
  among three).
- **Stale line pointers:** six of the eight `File.lean:line` pointers in the docstrings have
  drifted (Catalog 2033 → 2219, Embed 241 → 253, InputCall 294 → 291, Seam 813 → 886,
  AlphabetReduction 546 → 545, Constructible 485 → 480 and 329 → 324). InputLength 473 and
  WordRAM/Basic 62–63 are still right. The fills drop line numbers from the sketches they
  rewrite (`briefs/COMMON.md` rule 5).
- **Missing readers for tier 3 (rule 10):** `mem_DTIME_iff` (ClassP/DTIME), `mem_NSPACE_iff`
  and `FinNDTM.decidesInSpace_iff` (SpaceComplexity/NSPACE), `NL_eq` (SpaceClasses), and
  equations for `outputOf`, `simTime`, `simSpace` (RAMSimulation/Simulation). Existing:
  `mem_SPACE_iff`, `decidesInSpace_iff`, `computesInSpace_iff`, `LOGSPACE_eq`, `mem_P_iff`,
  `decidesInTime_iff`, `spaceConstructible_iff`, `logSpace_eq`.

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

## ===== campaign/items/ram-tm/PLAN.md =====

# RAM machines on Turing machines: planning note (2026-11-17)

**Ruling (Seyoon, 2026-11-17):** "all I wanted was to prove the 14 pending admissions for now".
The scope is **route C** below: prove stage 2's 14 admitted declarations, whose statements were
gated on 2026-10-14. Routes A, B and D (the book's RAM TM, a single-tape target) are not pursued
for now; §2–§5 keep the analysis for later. This work goes on a future branch into `main` and
must not delay the closeout's integration.

## 0. The work: 14 admitted declarations in three tiers

| Tier | File | Declarations | Nature | Size estimate |
|---|---|---|---|---|
| 1 | `RAMSimulation/WordSize` (3) | `WordSizeComputable.mono`, `wordSizeComputable_logSpace`, `wordSizeComputable_of_spaceConstructible` | small: monotonicity; machines for `bits(c·logSpace n)` and `bits(c·S n)` from existing length and constructibility rows | 100–300 lines |
| 2 | `RAMSimulation/Simulation` (2) | `exists_simulation`, `exists_ndSimulation` | **the main work**: a phase host over `P`'s positions with one framed contract per instruction kind (find-by-key in the (address, word) table, two-tape add and subtract mod `2^W`, shift-and-add multiply, sign test, `half`, overwrite or append an entry, input seek, output append, and `coin` as a choice step), a start-up (word size, ruler, length copy, `initMem`), and the simulation induction over `XStepsIn` | several thousand lines; several fills |
| 3 | `RAMSimulation/Classes` (9) | `mem_DTIME_of_decides`, `mem_P_of_decides`, `mem_P_of_decides_logWord`, `mem_SPACE_of_decides`, `mem_LOGSPACE_of_decides`, `computesInSpace_of_computes`, `mem_SPACE_mul_of_decides`, `mem_NSPACE_of_accepts`, `mem_NL_of_accepts` | corollaries of tier 2 and tier 1 plus bound arithmetic; can be proved first against tier 2's statements | 300–800 lines |

**Order.**
1. **Re-check the statements** against today's library. They were gated before MIG-1, R4 and the
   closeout. Check that every name cited in the proof sketches still exists with the cited
   contract; `phaseHostTM`, `exists_inputSeekTM`, `exists_inputLengthTM`, `embedSilentTM` and
   `Contract` do.
2. **Tiers 1 and 3**, while tier 2 is still admitted. Tier 3 only cites tier 2's statements.
3. **Tier 2**, in fills: the start-up, the instruction rows (grouped), the table invariant and
   the simulation induction, then the nondeterministic variant.

**Base and fillers (Seyoon, 2026-11-17):**
- **Base:** start **after W7, from `main`**, which by then has the campaign's machine library.
  Until then, only preparation: the statement re-check and the briefs.
- **Tools:** merge the `seyoon-devtools` branch into the work branch first, for the wrappers and the gate kit (`devtools/seyoon/gatekit/`).
- **Fillers:** Codex, as delegated fills. The maintainer writes briefs per tier and stages them
  on the exchange for Seyoon to dispatch, then reviews and lands each delivery with a gate.

## 1. What was deferred, and what exists

- **The deferral.** The chapter 1 plan (`campaign/design/plans/AroraBarakChapter1Plan.md` §5 and
  its decision log) put "the RAM-TM exercise (Ex 1.9)" in Phase 5, "deferred to a much later
  effort". The backlog repeats it ("Phase 5, deliberately unscheduled").
- **The book's exercise** ([AB09], Exercise 1.9, p. 35), as I recall it; the wording needs checking
  against the 2009 text. A *RAM Turing machine* has an infinite array `A`, one work tape
  designated as the address tape, two symbols `R` and `W`, and a state `q_access`. On entering
  `q_access`:
  - with `⌞i⌟ R` on the address tape, `A[i]` is written next to the `R`;
  - with `⌞i⌟ W σ` on the address tape, `A[i]` is set to `σ`.

  The exercise: if `f` is computable within time `T(n)` (time-constructible) by a RAM TM, then
  `f ∈ DTIME(T(n)²)`. AB09's `DTIME` is multi-tape.
- **Already in TCSlib (from `main`):**
  - **The word RAM's "stage 2"** (`TCSlib/Complexity/RAMSimulation/`; design §15a–§16b; backlog
    PROG-4). [AFM26]'s word RAM, extended with `rdIn`, `emit`, `coin` and `half`, is simulated by a
    multi-tape `FinTM Bool` within `TW n + A·(t+1)·(f·(W+1) + W² + n + 1)` steps.
    - The statements were gated on 2026-10-14 and the proofs are pending: 14 admissions
      (`Simulation` 2, `Classes` 9, `WordSize` 3).
    - The deterministic statement cites [AB09, Exercise 1.9] as its source, with documented
      deviations: a word RAM rather than the book's RAM TM, and an explicit bound rather than
      `T(n)²`.
  - **Single tape:** `Turing.FinTM.one_work_tape_binary` (`Robustness/SingleTape`), [AB09]
    Claims 1.5 and 1.6. A `FinTM Bool` computing `f` within `T` gives a one-work-tape
    `FinTM Bool` within `c·(T n + 1)²`. It is proved, with standard axioms.

## 2. The bound: what is true, and where "quadratic" can fail

The obvious construction stores the array as a list of `(address, symbol)` pairs on a work tape
and scans it at each access. Its cost depends on how long addresses can get:

- **In the book's model, addresses are cheap to make long.** After writing one address of length
  `ℓ`, flipping its last bit gives a new address of length `ℓ` in `O(1)` steps. So `T` steps can
  create about `T` distinct addresses of length about `T`, and the list grows to about `T²`
  cells. One access then costs `Θ(T²)` steps, and the naive total is **`T³`, not `T²`**. I have
  not found the argument that gives `T²` in this model, and there may be a better data structure.
  **This needs settling before any statement is gated.**
- **Log-cost models give `T²`.** If an access to address `i` is charged `|⌞i⌟|` steps, as in the
  word RAM where addresses are words of `W` bits, the list has total length `O(T)`, so an access
  costs `O(T)` and the total is `O(T²)` on a multi-tape machine. Stage 2's bound is of this kind.
- **Single tape adds a square on top.** Composing any multi-tape bound `B` with
  `one_work_tape_binary` gives `c·(B + 1)²`. So:
  - "RAM to single tape in quadratic time" via the multi-tape route is **quartic in `T`** for a
    `T²` multi-tape simulation;
  - it is quadratic only in the multi-tape bound `B`.

  A direct single-tape construction in `O(T²)` would be a new result rather than the book's; I
  have not checked whether it holds for either model.

## 3. Route options

| Route | Model | Target | Bound | Work |
|---|---|---|---|---|
| **A** | Book's RAM TM (new definition) | multi-tape `FinTM` (`DTIME`) | `T²` if §2's question resolves; else `T³` honestly | new model and semantics; list-store simulation; Claim-style ledger |
| **B** | Book's RAM TM | one work tape | `c·(B + 1)²`, with `B` route A's bound | route A, then `one_work_tape_binary` (proved) |
| **C** | The word RAM (stage 2) | multi-tape | stage 2's explicit bound | prove the 14 pending admissions; the statements already exist |
| **D** | The word RAM | one work tape | `c·(simTime + 1)²` | route C, then `one_work_tape_binary`; a short corollary |

**Recommendation, pending §4.** D is the smallest new surface: route C's statements are already
gated, and D is a short corollary of C and the proved single-tape theorem. It gives a single-tape
machine whose overhead is quadratic in the multi-tape simulation's time. If the goal is the
book's exercise itself, A and B need §2's question settled first.

## 4. Decisions for Seyoon (answered for now: route C, the 14 admissions)

1. **The model:** the book's RAM TM (A, B), [AFM26]'s word RAM (C, D), or both.
2. **The target:** multi-tape (`DTIME`, as in the book), a single work tape, or both.
3. **The bound:** in "quadratic overhead", quadratic in what? The RAM's step count `T` (needs §2
   resolved for the book's model), or the multi-tape simulation's time (route D)? Should a `T³`
   statement be acceptable for the book's model if `T²` does not hold there?
4. **The relation to stage 2:** should this branch also prove stage 2's 14 pending admissions, or
   are they someone else's work on `main`? Their author and status should be confirmed first.

## 5. Draft statement shapes (unchecked; for discussion only)

**Route D**, a corollary of stage 2's deterministic form:

```lean
/-- Stage 2 on one work tape: a word-RAM program is simulated by a single-work-tape binary
machine with quadratic overhead in stage 2's time bound. [AB09, Exercise 1.9 with Claims 1.5 and
1.6] -/
theorem WordRAM.exists_oneTape_simulation (P : XProgram) (fn : Bool) {W TW SW T F : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW)
    (hP : ∀ x, ∃ v o, HaltsWithin P x [] (W x.length) (T x.length) v o (F x.length))
    (g : List Bool → List Bool)
    (hg : ∀ x v o, HaltsWithin P x [] (W x.length) (T x.length) v o (F x.length) →
      g x = outputOf fn v o) :
    ∃ (M : Turing.FinTM Bool) (A c : ℕ), M.k = 1 ∧
      M.ComputesFunInTime g fun n => c * (simTime A TW n (W n) (T n) (F n) + 1) ^ 2
```

Its proof would be `exists_simulation`, then `computesFunInTime_iff`, then
`one_work_tape_binary`, with monotonicity of `simTime` in `t` and `f`. One check is still open:
`ComputesFunInTime` needs one bound per input length, so `hP` and `hg` take `T` and `F` as
functions of `|x|`.

**Route A**, the book's model. The new definitions would be:
- `Turing.RAMTM`, a `MultiTapeTM` with a designated address tape, `R`/`W` symbols and an access
  state;
- its configuration, which adds the array `ℕ → Option Γ`;
- its step and `ComputesInTime`.

The theorem:

```lean
/-- [AB09, Exercise 1.9]. -/
theorem Turing.RAMTM.mem_DTIME_sq {T : ℕ → ℕ} (hT : TimeConstructible T) (M : RAMTM …)
    (f : List Bool → List Bool) (hM : M.ComputesFunInTime f T) :
    ∃ M' : FinTM Bool, ∃ c, M'.ComputesFunInTime f fun n => c * (T n + 1) ^ 2
```

This is only true if §2's question resolves in favor of `T²`. Otherwise the exponent is 3, or
the model charges an access by its address length.

## 6. Next steps once §4 is decided

1. Check Exercise 1.9's wording against the 2009 text (route A or B).
2. Settle §2: find or rule out a `T²` argument for the book's model.
3. Write the statement file on a new branch from `main`, after the closeout's W7 merges, then a
   statement gate.
4. Plan the fills; for route D, a single maintainer PR.

## ===== TCSlib/Complexity/RAMSimulation/WordSize.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Constructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The word size of a simulated word RAM

Stage 2 (backlog PROG-4) runs a word-RAM program with a word size `W` that depends on the input
length, and its machine computes `W (|x|)` itself, once, at the start (design §16b item 1). The
hypothesis is `WordRAM.WordSizeComputable W TW SW` (user decision, 2026-10-12): some machine
writes `W (|x|)` in binary within `TW (|x|)` steps and `SW (|x|)` work cells. Two bridges supply
it for the two kinds of consumer:

* `wordSizeComputable_logSpace`: `W = c · logSpace`, in linear time and logarithmic space, for
  the P and L grades (from the input-length counter R8.5c);
* `wordSizeComputable_of_spaceConstructible`: `W = c · S` in space `O(S)`, for Savitch's shape
  (from the constructibility witness of `S`).

`Complexity.SpaceConstructible` is not used directly: it has no time clause, so the P grade could
not use it, and it carries the conjunct `logSpace ≤ S`, which stage 2 does not need.

## Main definitions

* `WordRAM.WordSizeComputable`.

## Main results (statements gated 2026-10-14, `audits/stage2-statements-findings.md`; proofs pending)

* `WordRAM.WordSizeComputable.mono`.
* `WordRAM.wordSizeComputable_logSpace`, `WordRAM.wordSizeComputable_of_spaceConstructible`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3 and §4.1, p. 79: time- and space-constructible
  functions.)
-/

namespace WordRAM

/-- **The word size is computable within `TW` and `SW`**: some finite binary machine, on every
input `x`, halts within `TW |x|` steps with the binary representation of `W (|x|)` on its output
tape (`Nat.bits`, as in `Complexity.SpaceConstructible` and `Complexity.TimeConstructible`), having
visited at most `SW |x|` work cells up to then. The stage-2 machine runs it once, at the start,
with its output captured on a work tape, and pays `TW` and `SW` once. Deviation: it bounds time
and space together, where [AB09] has separate time- and space-constructibility (§1.3, §4.1);
design §16b item 1. -/
def WordSizeComputable (W TW SW : ℕ → ℕ) : Prop :=
  ∃ M : Turing.FinTM Bool, ∀ x : List Bool, ∃ t ≤ TW x.length,
    M.ComputesInTime x (W x.length).bits t ∧ M.tm.spaceUsed (M.tm.initCfg x) t ≤ SW x.length

/-- A word size computable within `TW` and `SW` is computable within any larger bounds.

**Proof sketch.** The same machine and halting times; `t ≤ TW n ≤ TW' n`, and the space bound
weakens pointwise. -/
theorem WordSizeComputable.mono {W TW SW TW' SW' : ℕ → ℕ} (h : WordSizeComputable W TW SW)
    (hT : ∀ n, TW n ≤ TW' n) (hS : ∀ n, SW n ≤ SW' n) : WordSizeComputable W TW' SW' := by
  sorry

/-- **Logarithmic word sizes** (the P and L grades): for every `c`, the word size
`c · (⌊log₂ n⌋ + 1)` is computable in linear time and logarithmic space.

**Proof sketch.** R8.5c (`Turing.exists_inputLengthTM`, `Build/InputLength.lean:473`) writes
`Nat.bits |x|` on a work tape within `C·(|x| + 1)` steps and `C·(|bits |x|| + 1)` cells; setting
its first cell to `true` gives a word of length `logSpace |x|` at every length, `|x| = 0`
included. This is the route of `Complexity.spaceConstructible_logSpace`
(`SpaceComplexity/Constructible.lean:485`), whose private machine `b3a_log_machine` (`:329`)
bounds the space but states no time, so the fill states its time or re-derives it from
`Turing.FinTM.computesFunInTime_lengthBits_spaceUsed` (`Build/Catalog.lean:2033`). A counter pass
over that word writes its length in binary, a carry pass multiplies it by `c`, and the result is
emitted. Time `O(|x| + 1)`; space `O(logSpace |x|)`, since `logSpace n ≥ 1`. -/
theorem wordSizeComputable_logSpace (c : ℕ) :
    ∃ a : ℕ, WordSizeComputable (fun n => c * Complexity.logSpace n) (fun n => a * (n + 1))
      (fun n => a * Complexity.logSpace n) := by
  sorry

/-- **Space-constructible word sizes** (Savitch's shape): if `S` is space-constructible, then for
every `c` the word size `c · S(n)` is computable in space `O(S(n))`, within some time bound `TW`
that is not controlled and that the space grades do not need.

**Proof sketch.** Run the constructibility witness with its output captured on a work tape (the
R1 silent embedding `Turing.embedSilentTM`, `Build/Embed.lean:241`), multiply by `c` with a carry
pass, and emit. Space: `c_S·S + O(log (c·S) + 1) ≤ a·S`, since `S ≥ logSpace ≥ 1` (a conjunct of
`Complexity.SpaceConstructible`). Time: the witness halts on every input, since
`Turing.FinTM.ComputesInSpace` asks for a halting time; so the largest halting time over the
`2^n` inputs of length `n`, plus the multiplication, is a bound `TW n`. -/
theorem wordSizeComputable_of_spaceConstructible {S : ℕ → ℕ}
    (hS : Complexity.SpaceConstructible S) (c : ℕ) :
    ∃ (a : ℕ) (TW : ℕ → ℕ), WordSizeComputable (fun n => c * S n) TW (fun n => a * S n) := by
  sorry

end WordRAM
```

## ===== TCSlib/Complexity/RAMSimulation/Simulation.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Extended
import TCSlib.Complexity.RAMSimulation.WordSize
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NondeterministicSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Stage 2: the word RAM on Turing machines

A program `P` of the extended word RAM (`WordRAM.XProgram`: the nine vendored instructions and
`rdIn`, `emit`, `coin`, `half`) is run on an input `x`, a coin stream `ρ` and a word size
`W = W (|x|)`. Stage 2 (backlog PROG-4; design §15a, §15d, §16b) says that one `FinTM Bool`
simulates it, instruction by instruction, with a polynomial time overhead and a space bound
linear in the number of cells touched times the word size: with `n = |x|`,

* time `TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)`;
* space `SW n + A·(f·(W + 1) + W + logSpace n + 1)`;

where `t` bounds the RAM's steps, `f` the number of cells it touches, `W` is computed within
time `TW` and space `SW` (`WordRAM.WordSizeComputable`), and `A` depends on `P` only. The
nondeterministic form is the same with one `FinNDTM` choice step per `coin`, under bounds that
are uniform over all coin streams.

**Deviations from the shape drafted in design §15a**, each read off the code (design §15d):

* *No separate address width.* Addresses are words: `load` reads `m (m j).toInt` and `store`
  writes at `(m i).toInt` (`TCSlib/Programs/WordRAM/Basic.lean:62-63`), and the immediate
  addresses are constants of `P`. So a table entry has `W + O_P(1)` bits, and `f·(W + a)`
  becomes `f·(W + 1)`, the constant going into `A`.
* *The input seek is linear.* R8.5b (`Turing.exists_inputSeekTM`, `Build/InputCall.lean:294`)
  seeks position `p` within `C·(|w| + pos + p + 1)` steps for a position word `w`, with work
  envelope `C·(|w| + 1)`; here `|w| ≤ W` and `pos, p ≤ n + 1`. So the per-step seek term is `n`,
  not `n·log n`.
* *The word size's own cost* is added once, as `TW n` and `SW n`.

## Main definitions

* `WordRAM.simTime`, `WordRAM.simSpace`: the two bounds.
* `WordRAM.outputOf`: what the machine leaves on its output tape, in verdict or function mode.

## Main results (statements gated 2026-10-14, `audits/stage2-statements-findings.md`; proofs pending)

* `WordRAM.exists_simulation`: stage 2, deterministic form.
* `WordRAM.exists_ndSimulation`: stage 2, nondeterministic form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9, p. 35: a RAM Turing machine is simulated with
  polynomial overhead; §2.1.2: NDTMs; Definition 4.1; §4.3.1: read-once certificates.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit
  `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05), Apache-2.0: the word RAM of
  `EndStatement.lean` (vendored as `TCSlib/Programs/WordRAM/Basic.lean`), extended in
  `TCSlib/Programs/WordRAM/Extended.lean`, is the simulated model.
-/

namespace WordRAM

/-- **The time bound of stage 2**: computing the word size, then `t + 1` simulated steps, each at
most one scan of a table of `f` entries of `W + O(1)` bits, one shift-and-add multiplication of
`W`-bit words, and one input seek. -/
def simTime (A : ℕ) (TW : ℕ → ℕ) (n W t f : ℕ) : ℕ :=
  TW n + A * (t + 1) * (f * (W + 1) + W ^ 2 + n + 1)

/-- **The space bound of stage 2**: computing the word size, then the memory table (`f` entries
of `W + O(1)` bits), `O(1)` words of scratch, and the input length in binary. -/
def simSpace (A : ℕ) (SW : ℕ → ℕ) (n W f : ℕ) : ℕ :=
  SW n + A * (f * (W + 1) + W + Complexity.logSpace n + 1)

/-- What the stage-2 machine leaves on its output tape: in verdict mode (`fn = false`) the
one-bit verdict, as `Turing.FinTM.DecidesInTime` and `Turing.FinTM.DecidesInSpace` read it; in
function mode (`fn = true`) the emitted word, as `Turing.FinTM.ComputesInSpace` reads it. -/
def outputOf (fn v : Bool) (o : List Bool) : List Bool := if fn then o else [v]

/-- **Stage 2, deterministic form** (design §15a, §16b; backlog PROG-4). For every program `P` of
the extended word RAM, every output mode `fn` and every word size `W` computable within `TW` and
`SW`, there are a finite binary machine `M` and a constant `A` such that: whenever `P`, run on
`x` with word size `W (|x|)` and the empty coin stream (coins read `0`), gives the verdict `v`
within `t` steps, having emitted `o` and touched at most `f` cells, then `M` halts on `x` within
`TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` steps with `outputOf fn v o` on its output tape,
having visited at most `SW n + A·(f·(W + 1) + W + logSpace n + 1)` work cells (`n = |x|`).
[AB09, Exercise 1.9]

Deviations: [AB09] has a RAM Turing machine with a symbol array and the bound `T(n)²`; this is
[AFM26]'s word RAM with input, output and coins, and the bound is explicit in steps, cells and
word size. From design §15a's draft shape: no separate address width, a seek term `n` rather than
`n·log n`, and the word size's own cost added (module docstring).

**Proof sketch.** The machine is a phase host (`Turing.phaseHostTM`, `Build/Seam.lean:813`) over
the finitely many positions of `P`, after a start-up. It works over `Bool` with fields of fixed
width `W + O_P(1)` measured against the ruler below; a richer alphabet would need a per-input
alphabet reduction, which is not public today (`Turing.FinTM.alphabet_reduction` has
length-indexed bounds; its per-input core `arTM_computes`, `Robustness/AlphabetReduction.lean:546`,
is private; there is no nondeterministic variant).
1. *Start-up.* Run the word-size witness with its output captured on a work tape (the R1 silent
   embedding `Turing.embedSilentTM`, `Build/Embed.lean:241`), turn `Nat.bits W` into a unary
   ruler of `W` cells, count `|x|` into a private binary copy (R8.5c,
   `Turing.exists_inputLengthTM`), and install the table entry `-1 ↦ |x| mod 2^W`
   (`WordRAM.initMem`). Cost `TW n + O(n + W²)`, space `SW n + O(W + logSpace n)`.
2. *One phase per position.* Each instruction kind is a framed contract (`Turing.Contract`,
   MIG-0a, landing first) whose precondition says that the tapes encode a RAM configuration (a
   memory table of (address, word) pairs, the position as the phase, the ruler, the length copy)
   and whose endpoint encodes its `xstep`. The new rows (design §15a) are find-by-key in the
   table with the key on another tape; two-tape addition and subtraction modulo `2^W`;
   shift-and-add multiplication; the sign test (`bltz`); the arithmetic shift (`half`); in-place
   overwrite or append of a table entry; the input seek R8.5b (`rdIn`, after a range test of the
   position against `|x|`, `O(W + logSpace n)`); and an output append (`emit`, in function mode
   only). `coin` writes `0`. Each costs at most `A·(f·(W + 1) + W² + n + 1)` steps on a table of
   at most `f + 1` entries.
3. *Simulation.* Induction on the `XStepsIn` run: the encoding invariant holds after every
   step, and the table holds only cells of the footprint `K` and `-1`, so at most
   `|K| + 1 ≤ f + 1` entries of `W + O_P(1)` bits.
4. *Verdict.* At `accept` or `reject`, write `[v]` in verdict mode, and halt. -/
theorem exists_simulation (P : XProgram) (fn : Bool) {W TW SW : ℕ → ℕ}
    (hW : WordSizeComputable W TW SW) :
    ∃ (M : Turing.FinTM Bool) (A : ℕ), ∀ (x : List Bool) (t f : ℕ) (v : Bool) (o : List Bool),
      HaltsWithin P x [] (W x.length) t v o f →
        M.ComputesInTime x (outputOf fn v o) (simTime A TW x.length (W x.length) t f) ∧
        M.tm.spaceUsed (M.tm.initCfg x) (simTime A TW x.length (W x.length) t f) ≤
          simSpace A SW x.length (W x.length) f := by
  sorry

/-- **Stage 2, nondeterministic form** (design §15c, §16b item 4; backlog PROG-4). For every
program `P` of the extended word RAM and every word size `W` computable within `TW` and `SW`,
there are a finite binary nondeterministic machine `N` and a constant `A` such that: if, on the
input `x`, **every** coin stream lets `P` give a verdict within `t` steps touching at most `f`
cells (bounds uniform over the streams, as `NTIME` and `NSPACE` require), then every branch of
`N` of length `T = simTime …` has halted, every such branch has visited at most `simSpace …` work
cells, and `N` accepts `x` within `T` exactly when some coin stream makes `P` accept.
[AB09, Exercise 1.9 with §2.1.2 and Definition 4.1; the coins are read once, as the certificate
of §4.3.1]

**Proof sketch.** As `exists_simulation`, in verdict mode, with one change: the phase for
`coin i` is a single choice step whose two transitions write `0` or `1` into the table entry of
`i`, and every other state has two equal transitions. A branch, a choice word `w` of length `T`,
then simulates the RAM run whose coin stream is the subsequence of `w` at the coin steps;
conversely every coin stream is realized by a branch that places its bits there, padded to length
`T`. Every branch is a run of `P` on some stream, so the uniform bounds bound every branch. On
the stretches between coin steps the branch is the deterministic run of the slice
`N.tm.fixChoice false` (`Turing.NDTM.runWith_eq_fixChoice_runFrom`, in `TuringMachine/Nondeterministic.lean`),
whose phases are those of `exists_simulation`. -/
theorem exists_ndSimulation (P : XProgram) {W TW SW : ℕ → ℕ} (hW : WordSizeComputable W TW SW) :
    ∃ (N : Turing.FinNDTM Bool) (A : ℕ), ∀ (x : List Bool) (t f : ℕ),
      (∀ ρ : List Bool, ∃ (v : Bool) (o : List Bool), HaltsWithin P x ρ (W x.length) t v o f) →
        N.tm.HaltsWithin x (simTime A TW x.length (W x.length) t f) ∧
        (∀ w : List Bool, w.length = simTime A TW x.length (W x.length) t f →
          N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ simSpace A SW x.length (W x.length) f) ∧
        (N.AcceptsWithin x (simTime A TW x.length (W x.length) t f) ↔
          ∃ (ρ o : List Bool), HaltsWithin P x ρ (W x.length) t true o f) := by
  sorry

end WordRAM
```

## ===== TCSlib/Complexity/RAMSimulation.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.WordSize
import TCSlib.Complexity.RAMSimulation.Simulation
import TCSlib.Complexity.RAMSimulation.Classes

/-!
# Word-RAM programs on Turing machines

Stage 2 of the programming layer (`machine-library-design.md` §15d, backlog PROG-4): one Turing
machine that simulates a program of the extended word RAM (`WordRAM.XInstr`,
`TCSlib/Programs/WordRAM/Extended.lean`), in deterministic and nondeterministic forms, and the
complexity classes that follow from a program's time, cells and word size. The statements passed
their gate on 2026-10-14 (`audits/stage2-statements-findings.md`); their proofs are pending.

## Contents

- `RAMSimulation.WordSize`: the word-size hypothesis `WordRAM.WordSizeComputable` and its two
  bridges (`c · logSpace`, and `c · S` from a space-constructible `S`)
- `RAMSimulation.Simulation`: stage 2, `WordRAM.exists_simulation` and
  `WordRAM.exists_ndSimulation`, with their time and space bounds
- `RAMSimulation.Classes`: the nine corollaries (DTIME, P, SPACE, L, log-space transducers,
  Savitch's `SPACE(S·S)` shape, NSPACE and NL)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6, Exercise 1.9; §4.1.)
* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the word RAM
  and the language whose programs stage 2 runs (see `TCSlib/Programs` and the repository NOTICE).
-/
```

## ===== TCSlib/Complexity/TuringMachine/Build/InputLength.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.CounterLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the input length in binary (§12.8, R8.5c)

The native-input row R8.5c of the §12.8 rich-alphabet design
(`machine-library-design.md` §12.8a §3, §12.8b): count the native input into a
little-endian binary word on a dedicated work tape, `Nat.bits |x|`, in linear
time and logarithmic work space. It is a `Bool` module; a rich host runs it
lifted along its digit embedding (`Turing.MultiTapeTM.liftSymbols`), with
unchanged time and space. The record template and the initial record
(`Build/RecordTable.lean`) take their position width from it, and the
space-constructibility witnesses of chapter 4 count with it.

**Status: proved.** The framed input-length contract is proved by a single
input pass with a binary counter, followed by the public input rewind.

## Design

* **Own module** (§12.8b decision proposal W1-5): the natural home is beside
  `Turing.exists_inputSeekTM` in `Build/InputCall.lean`, which an in-flight fill
  batch owns. This module imports only `Build/CounterLoop`, so the
  constructibility files can import it without the record layer; 12.2c may fold
  it into `Build/InputCall.lean`.
* **Framed output.** The dedicated tape need only be blank on the interval the
  word and its two delimiters occupy, so the module also runs on a tape that
  carries unrelated data elsewhere.
* **Input position.** The module starts with the input head at `1` and returns it
  there, as `Turing.inputCopyTM` and `Turing.inputFoldTM` do.

## Main results

* `Turing.exists_inputLengthTM` — write `Nat.bits |x|` on a dedicated tape
  (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3 and §4.1: a machine counts its input
  length in binary with a work-tape counter in `O(log n)` space; p. 79, the
  space-constructibility of `log n`.)
-/

namespace Turing

/-- The six phases of the single-pass input counter. -/
private inductive InputLengthPhase where
  | count | carry | back | returnStart | returnScan | done
  deriving DecidableEq, Fintype

/-- The framed counter's only hand-built table: there is no public input-driven
counter. Carry and work-head rewind implement the counting phase of Catalog's
`f2_counterTM`; the native-input return uses the public input-fold transition
and rewind contract.

**Fill appendix.** The input-advance step is separate from the carry, costing
one extra step per round. A round with `p` cleared digits therefore costs
`2*p + 3`; its cost plus twice the change in the true-bit count is five.
The exit is stationary so the least exit time has the same exact finish. -/
private def inputLengthMachine : MultiTapeTM 1 Bool InputLengthPhase where
  q₀ := .count
  tr := fun phase inp work =>
    match phase with
    | .count =>
      match inp with
      | some _ => inputMoveAction .pos .carry
      | none => inputMoveAction 0 .returnStart
    | .carry =>
      if work 0 = some true then tapeAction 0 0 (some (some false)) .pos .carry
      else tapeAction 0 0 (some (some true)) .neg .back
    | .back =>
      match work 0 with
      | some _ => tapeAction 0 0 none .neg .back
      | none => tapeAction 0 0 none .pos .count
    | .returnStart => FinTM.controlAction .neg (some .returnScan)
    | .returnScan =>
      ((inputFoldTM 1 (fun (_ : Unit) (_ : Bool) => ()) ()).tr (.bwd ()) inp work).mapState
        (fun q => match q with | .done _ => .done | _ => .returnScan)
    | .done => inputMoveAction 0 .done

/-- Splitting the canonical digits at their first zero also gives the successor's
canonical digits. The second alternative is the width-extension case.

**Proof sketch.** Binary induction removes the low digit. A zero ends the carry;
a one adds one cleared digit to the induction hypothesis. -/
private theorem inputLength_digits (n : ℕ) :
    ∃ p : ℕ, ∃ v : List Bool,
      (n.bits = List.replicate p true ++ false :: v ∨
        n.bits = List.replicate p true ∧ v = []) ∧
      (n + 1).bits = List.replicate p false ++ true :: v := by
  induction n using Nat.binaryRec' with
  | zero => exact ⟨0, [], Or.inr ⟨by simp, rfl⟩, by simp⟩
  | bit b n h ih =>
    cases b with
    | false =>
      refine ⟨0, n.bits, Or.inl ?_, ?_⟩
      · simpa using Nat.bits_append_bit n false h
      · simpa only [Nat.bit_val, Bool.toNat_false, Nat.add_zero,
          List.replicate_zero, List.nil_append] using Nat.bit1_bits n
    | true =>
      obtain ⟨p, v, old, next⟩ := ih
      refine ⟨p + 1, v, ?_, ?_⟩
      · rw [Nat.bits_append_bit n true h, List.replicate_succ]
        rcases old with old | ⟨old, rfl⟩
        · exact Or.inl (by simp [old])
        · exact Or.inr ⟨by simp [old], rfl⟩
      · have he : Nat.bit true n + 1 = 2 * (n + 1) := by
          simp [Nat.bit_val]; omega
        rw [he, Nat.bit0_bits (n + 1) (by omega), next, List.replicate_succ]
        rfl


/-- The split gives the potential change and the maximal visited offset. -/
private theorem inputLength_charge (n p : ℕ) (v : List Bool)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v) :
    (n + 1).bits.count true + p = n.bits.count true + 1 ∧
      p < (n + 1).bits.length := by
  rw [next]
  rcases old with old | ⟨old, rfl⟩ <;> simp [old, List.count_append, List.count_replicate] <;> omega

/-- A counter trace configuration. Only a prefix of the replacement word has
been written; all cells outside that prefix retain their entry values. -/
private def inputLengthCfg {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (r : ℕ) (s : InputLengthPhase) (ip : Fin (x.length + 2))
    (z : ℤ) : Cfg 1 Bool InputLengthPhase x :=
  { state := some s
    inputPos := ip
    workTapes := fun _ a =>
      if d.workTapePos 0 ≤ a ∧ a < d.workTapePos 0 + (r : ℤ)
      then FinTM.bufferTape w (a - d.workTapePos 0)
      else d.workTapes 0 a
    workTapePos := fun _ => d.workTapePos 0 + z
    output := d.output }

/-- The unwritten prefix with zero head offset leaves the data fields alone. -/
private theorem inputLengthCfg_zero {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (s : InputLengthPhase) (ip : Fin (x.length + 2)) :
    inputLengthCfg d w 0 s ip 0 = {d with state := some s, inputPos := ip} := by
  apply Cfg.ext <;> simp only [inputLengthCfg, Nat.cast_zero, add_zero]
  · funext j a
    have : j = 0 := Subsingleton.elim _ _
    subst j
    split_ifs with h
    · omega
    · rfl
  · funext j
    exact congrArg d.workTapePos (Subsingleton.elim _ _)

/-- Writing the next prefix cell follows the public framed-write identity.

**Proof sketch.** The one-tape action supplies the configuration update;
`catalog_write_take` supplies the entire tape equality, including its frame. -/
private theorem inputLength_write {x : List Bool} (d : Cfg 1 Bool InputLengthPhase x)
    (w : List Bool) (r : ℕ) (hr : r < w.length) (s s' : InputLengthPhase)
    (ip : Fin (x.length + 2)) (m : SignType)
    (htr : inputLengthMachine.tr s
      (inputLengthCfg d w r s ip r).inputSymbol
      (inputLengthCfg d w r s ip r).workTapeSymbols =
        tapeAction 0 0 (some (some w[r])) m s') :
    inputLengthMachine.step (inputLengthCfg d w r s ip r) =
      inputLengthCfg d w (r + 1) s' ip ((r : ℤ) + m) := by
  rw [step_of_tapeAction_write _ _ 0 0 (some w[r]) m rfl htr]
  apply Cfg.ext
  · rfl
  · simp only [inputLengthCfg, moveInputPos_zero]
  · funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simpa only [Function.update_self, inputLengthCfg] using
      catalog_write_take (d.workTapes 0) (d.workTapePos 0) w r hr
  · funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [Function.update_self, inputLengthCfg]
    omega
  · rfl


/-- One input symbol drives one framed increment, including width extension.

**Proof sketch.** The forward configurations replace successive low bits by
zeros; the first non-true cell is replaced by one on the turn. The return
configurations keep this prefix and move over its zeros to the left delimiter.
The two direct inductions concern this cyclic table, whose return state starts
the next round. At every intermediate time the head is between minus one and
`p`, relative to the entry head. -/
private theorem inputLength_round {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (n p : ℕ) (v : List Bool)
    (hs : d.state = some .count) (hip : d.inputPos.val = n + 1) (hn : n < x.length)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v)
    (htape : ∀ a : ℤ, -1 ≤ a → a ≤ (n.bits.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = FinTM.bufferTape n.bits a) :
    inputLengthMachine.runFrom d (2 * p + 3) =
        inputLengthCfg d (n + 1).bits (p + 1) .count
          (moveInputPos d.inputPos .pos) 0 ∧
      ∀ u ≤ 2 * p + 3,
        d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
        (inputLengthMachine.runFrom d u).workTapePos 0 ≤ d.workTapePos 0 + (p : ℤ) := by
  let w := (n + 1).bits
  let ip := moveInputPos d.inputPos .pos
  let F := fun r : ℕ => inputLengthCfg d w r .carry ip r
  let R := fun r : ℕ => inputLengthCfg d w (p + 1) .back ip ((r : ℤ) - 1)
  let D := inputLengthCfg d w (p + 1) .count ip 0
  have plen : p < w.length := (inputLength_charge n p v old next).2
  have oldlen : p ≤ n.bits.length := by
    rcases old with h | ⟨h, _⟩ <;> simp [h]
  have fzero : inputLengthMachine.step d = F 0 := by
    have hi : d.inputSymbol = some x[n] := inputSymbolInner n (by omega) hn
    rw [step_of_inputMoveAction _ _ .pos hs (q' := .carry) (by
      simp [inputLengthMachine, hi])]
    exact (inputLengthCfg_zero d w .carry ip).symm
  have forward (r : ℕ) (hr : r < p) : inputLengthMachine.step (F r) = F (r + 1) := by
    have read : (F r).workTapeSymbols 0 = some true := by
      have cell := htape r (by omega) (by omega)
      have bit : n.bits[r]? = some true := by
        rcases old with h | ⟨h, _⟩ <;>
          simp [h, List.getElem?_append, hr]
      simpa [F, inputLengthCfg, Cfg.workTapeSymbols, FinTM.bufferTape_nat] using
        cell.trans (by simpa using bit)
    have digit : w[r] = false := by
      simp [w, next, hr]
    simpa only [F, Nat.cast_add, Nat.cast_one, SignType.cast] using
      inputLength_write d w r (by omega) .carry .carry ip .pos (by
        simp only [F] at read
        simp [inputLengthMachine, read, digit])
  have turn : inputLengthMachine.step (F p) = R p := by
    have read : (F p).workTapeSymbols 0 ≠ some true := by
      have cell := htape p (by omega) (by omega)
      have bit : n.bits[p]? ≠ some true := by
        rcases old with h | ⟨h, _⟩ <;> simp [h]
      simpa [F, inputLengthCfg, Cfg.workTapeSymbols, cell] using bit
    have digit : w[p] = true := by simp [w, next]
    simpa only [F, R, SignType.cast, sub_eq_add_neg] using
      inputLength_write d w p plen .carry .back ip .neg (by
        simp only [F] at read
        simp [inputLengthMachine, read, digit])
  have backward (r : ℕ) (hr : r < p) : inputLengthMachine.step (R (r + 1)) = R r := by
    have read : (R (r + 1)).workTapeSymbols 0 = some false := by
      have digit : w[r]? = some false := by
        simp [w, next, List.getElem?_append, hr]
      simp [R, inputLengthCfg, Cfg.workTapeSymbols, show (r : ℤ) < p + 1 by omega,
        FinTM.bufferTape_nat, digit]
    rw [step_of_tapeAction_move _ _ 0 0 .neg rfl (q' := .back) (by
      simp [inputLengthMachine, read])]
    apply Cfg.ext <;> simp only [R, inputLengthCfg, moveInputPos_zero]
    funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [Function.update_self, SignType.cast]
    omega
  have entry : inputLengthMachine.step (R 0) = D := by
    have read : (R 0).workTapeSymbols 0 = none := by
      have cell := htape (-1) (by omega) (by omega)
      simpa [R, inputLengthCfg, Cfg.workTapeSymbols, FinTM.bufferTape_left] using cell
    rw [step_of_tapeAction_move _ _ 0 0 .pos rfl (q' := .count) (by
      simp [inputLengthMachine, read])]
    apply Cfg.ext <;> simp only [R, D, inputLengthCfg, moveInputPos_zero]
    funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    simp [SignType.cast]
  have step_run (a : Cfg 1 Bool InputLengthPhase x) (u : ℕ) :
      inputLengthMachine.runFrom a (u + 1) =
        inputLengthMachine.step (inputLengthMachine.runFrom a u) :=
    MultiTapeTM.runFrom_succ_eq_step'
  have reachesF : ∀ r ≤ p, inputLengthMachine.runFrom d (r + 1) = F r := by
    intro r
    induction r with
    | zero => intro _; rw [Nat.zero_add, MultiTapeTM.runFrom_one]; exact fzero
    | succ r ih =>
      intro hr
      rw [step_run, ih (by omega), forward r (by omega)]
  have reachesR : ∀ r ≤ p, inputLengthMachine.runFrom d (p + 2 + r) = R (p - r) := by
    intro r
    induction r with
    | zero =>
      intro _
      simpa only [Nat.add_zero, Nat.sub_zero] using
        (show inputLengthMachine.runFrom d (p + 2) = R p by
          rw [show p + 2 = (p + 1) + 1 by omega, step_run,
            reachesF p le_rfl, turn])
    | succ r ih =>
      intro hr
      rw [show p + 2 + (r + 1) = (p + 2 + r) + 1 by omega,
        step_run, ih (by omega)]
      rw [show p - r = (p - (r + 1)) + 1 by omega, backward _ (by omega)]
  have finish : inputLengthMachine.runFrom d (2 * p + 3) = D := by
    rw [show 2 * p + 3 = (p + 2 + p) + 1 by omega,
      step_run, reachesR p le_rfl, Nat.sub_self, entry]
  refine ⟨finish, ?_⟩
  intro u hu
  by_cases hz : u = 0
  · subst u; simp
  by_cases hf : u ≤ p + 1
  · rw [show u = (u - 1) + 1 by omega, reachesF _ (by omega)]
    simp only [F, inputLengthCfg]
    constructor <;> omega
  by_cases hb : u ≤ 2 * p + 2
  · rw [show u = p + 2 + (u - (p + 2)) by omega, reachesR _ (by omega)]
    simp only [R, inputLengthCfg]
    constructor <;> omega
  · rw [show u = 2 * p + 3 by omega, finish]
    simp only [D, inputLengthCfg, add_zero]
    constructor <;> omega

/-- A completely written word agrees with its buffer throughout the originally
blank slot, including both delimiters. -/
private theorem inputLengthCfg_read {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (w : List Bool) (s : InputLengthPhase)
    (ip : Fin (x.length + 2)) (N : ℕ)
    (blank : ∀ a : ℤ, -1 ≤ a → a ≤ (N : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = none)
    (a : ℤ) (ha : -1 ≤ a) (hb : a ≤ (N : ℤ)) :
    (inputLengthCfg d w w.length s ip 0).workTapes 0 (d.workTapePos 0 + a) =
      FinTM.bufferTape w a := by
  simp only [inputLengthCfg, add_sub_cancel_left]
  split_ifs with h
  · rfl
  · rw [blank a ha hb]
    by_cases hn : 0 ≤ a
    · have hw' : w.length ≤ a.toNat := by omega
      simp [FinTM.bufferTape, hn, List.getElem?_eq_none hw']
    · simp [FinTM.bufferTape, hn]

/-- Consecutive canonical counter words differ only in the overwritten carry
prefix; overwriting that prefix therefore composes the two exterior frames.

**Proof sketch.** Below the origin nothing is touched. Inside the new prefix
the two sides read the new word. Above it the old and new words have the same
suffix, and their upper boundaries agree there, even on width extension. -/
private theorem inputLengthCfg_merge {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (n p : ℕ) (v : List Bool)
    (old : n.bits = List.replicate p true ++ false :: v ∨
      n.bits = List.replicate p true ∧ v = [])
    (next : (n + 1).bits = List.replicate p false ++ true :: v)
    (ip ip' : Fin (x.length + 2)) :
    inputLengthCfg (inputLengthCfg d n.bits n.bits.length .count ip 0)
        (n + 1).bits (p + 1) .count ip' 0 =
      inputLengthCfg d (n + 1).bits (n + 1).bits.length .count ip' 0 := by
  have plen : p < (n + 1).bits.length := (inputLength_charge n p v old next).2
  apply Cfg.ext <;> simp only [inputLengthCfg, add_zero]
  funext j a
  by_cases hlow : d.workTapePos 0 ≤ a
  · by_cases hpre : a < d.workTapePos 0 + ((p + 1 : ℕ) : ℤ)
    · have hnew : a < d.workTapePos 0 + ((n + 1).bits.length : ℤ) := by omega
      simp only [hlow, hpre, hnew, and_self, ite_true]
    · have offset : p + 1 ≤ (a - d.workTapePos 0).toNat := by omega
      have sameEnd : a < d.workTapePos 0 + (n.bits.length : ℤ) ↔
          a < d.workTapePos 0 + ((n + 1).bits.length : ℤ) := by
        rcases old with h | ⟨h, hv⟩
        · simp [h, next]
        · simp [h, next, hv]; omega
      have suffix : FinTM.bufferTape n.bits (a - d.workTapePos 0) =
          FinTM.bufferTape (n + 1).bits (a - d.workTapePos 0) := by
        simp only [FinTM.bufferTape, if_pos (by omega : 0 ≤ a - d.workTapePos 0)]
        rcases old with h | ⟨h, hv⟩
        · simp only [h, next, List.getElem?_append,
            List.length_replicate, if_neg (by omega : ¬(a - d.workTapePos 0).toNat < p)]
          rw [List.getElem?_cons, List.getElem?_cons]
          simp [show (a - d.workTapePos 0).toNat - p ≠ 0 by omega]
        · simp [h, next, hv, List.getElem?_eq_none, offset]; omega
      simp only [hlow, hpre, true_and, ite_false, sameEnd, suffix]
  · simp only [hlow, false_and, ite_false]

/-- Counting the first `n` input symbols preserves the exterior frame and pays
exactly five units per symbol after including twice the true-bit potential.

**Proof sketch.** Induct on the number of symbols. The framed round theorem
provides each physical segment, the digit split identifies its next canonical
word, and the frame-composition lemma joins it to the original configuration.
The potential equation telescopes, while both segments' head intervals fit the
new binary width. -/
private theorem inputLength_count {x : List Bool}
    (d : Cfg 1 Bool InputLengthPhase x) (hs : d.state = some .count)
    (hip : d.inputPos = 1)
    (blank : ∀ a : ℤ, -1 ≤ a → a ≤ (x.length.bits.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + a) = none) :
    ∀ n (hn : n ≤ x.length), ∃ t,
      t + 2 * n.bits.count true = 5 * n ∧
      inputLengthMachine.runFrom d t =
        inputLengthCfg d n.bits n.bits.length .count ⟨n + 1, by omega⟩ 0 ∧
      ∀ u ≤ t,
        d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
        (inputLengthMachine.runFrom d u).workTapePos 0 ≤ d.workTapePos 0 + (n.bits.length : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨0, by simp, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_zero]
      simp only [Nat.zero_bits, List.length_nil, inputLengthCfg_zero]
      apply Cfg.ext <;> simp [hs, hip]
    · intro u hu
      have : u = 0 := by omega
      subst u
      simp
  | succ n ih =>
    intro hn
    obtain ⟨t, charge, reached, bounded⟩ := ih (by omega)
    obtain ⟨p, v, old, next⟩ := inputLength_digits n
    have accounting := inputLength_charge n p v old next
    let ip : Fin (x.length + 2) := ⟨n + 1, by omega⟩
    let c := inputLengthCfg d n.bits n.bits.length .count ip 0
    have oldwidth : n.bits.length ≤ x.length.bits.length :=
      Complexity.LogProg.length_bits_mono (show n ≤ x.length by omega)
    have newwidth : n.bits.length ≤ (n + 1).bits.length :=
      Complexity.LogProg.length_bits_mono (Nat.le_succ n)
    have field (a : ℤ) (ha : -1 ≤ a) (hb : a ≤ (n.bits.length : ℤ)) :
        c.workTapes 0 (c.workTapePos 0 + a) = FinTM.bufferTape n.bits a := by
      simpa only [c, inputLengthCfg, add_zero] using
        inputLengthCfg_read d n.bits .count ip x.length.bits.length blank a ha (by omega)
    have round := inputLength_round c n p v rfl rfl (by omega) old next field
    have inext : moveInputPos c.inputPos .pos = (⟨n + 1 + 1, by omega⟩ : Fin (x.length + 2)) := by
      rw [moveInputPos_pos_of_ne_right _ (by simp only [c, inputLengthCfg, ip]; omega)]
      rfl
    have ctime : inputLengthMachine.runFrom d t = c := reached
    refine ⟨t + (2 * p + 3), by omega, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_add, ctime, round.1, inext]
      exact inputLengthCfg_merge d n p v old next ip _
    · intro u hu
      by_cases before : u ≤ t
      · obtain ⟨lower, upper⟩ := bounded u before
        exact ⟨lower, by omega⟩
      · have localBound := round.2 (u - t) (by omega)
        rw [show u = t + (u - t) by omega, MultiTapeTM.runFrom_add, ctime]
        have hcpos : c.workTapePos 0 = d.workTapePos 0 := by simp [c, inputLengthCfg]
        rw [hcpos] at localBound
        exact ⟨localBound.1, by omega⟩

/-- **R8.5c, the input length** (design §12.8a §3, §12.8b). There is a `Bool`
module with an entry and an exit state and `K + 1` tapes with the following
contract. Start it at its entry with the input head at position `1`, tape `0`
blank on the `|bits |x|| + 2` cells from one left of its head to one right of
where the word will end, and the other tapes blank. It reaches its exit within
`C·(|x| + 1)` steps, and not earlier. At that point tape `0` holds
`Nat.bits |x|` from its head, and every other cell, every head, the input
position and the output are as they were. Up to the exit every work head stays
within `C·(|bits |x|| + 1)` cells of its entry position, so the work space is
logarithmic in `|x|` however far the input head travels. At `x = []` nothing is
written, since `Nat.bits 0 = []`.

**Proof sketch.** One pass over the input drives an in-place binary counter on
tape `0`. For each input symbol, move the input head right and increment the
counter: the carry turns the maximal `true` prefix to `false` and writes `true`
on the next cell, which is the blank just after the word when the counter
overflows, so the width grows by one cell exactly at the powers of two. A
return pass brings the counter head back to its first cell, guided by the
blank delimiter on its left. At the input's right end marker, walk the input
head back to position `1` (the `Turing.inputFoldTM_run_ofCfg` return) and exit.
The increments from `0` to `|x|` cost `Σ_v (2·p_v + 2)` for the true-prefix
lengths `p_v`, which telescopes against twice the number of `true` cells, as
in `Turing.counterOverhead_le_of_le` mirrored, so the total is linear in
`|x|`. Route: the counting phase is the transition table of Catalog's private
`f2_counterTM` without its emission, framed; no public input-driven loop host
exists (`Turing.counterLoopTM` needs its round count on a tape, which is what
is being computed), so the fill proves the framed round induction for this
table directly and records the pair with `f2_counterTM` for 12.2c, which can
re-derive `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed` from this row.
The counter head stays in `[pos - 1, pos + |bits |x||]`. -/
theorem exists_inputLengthTM :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM (K + 1) Bool S)
      (entry exit : S) (C : ℕ),
      ∀ {x : List Bool} (d : Cfg (K + 1) Bool S x), d.state = some entry → d.inputPos = 1 →
        (∀ p : ℤ, -1 ≤ p → p ≤ ((Nat.bits x.length).length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + p) = none) →
        (∀ j : Fin (K + 1), j ≠ 0 → ∀ p, d.workTapes j p = none) →
        ∃ t ≤ C * (x.length + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin (K + 1),
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤
              ((C * ((Nat.bits x.length).length + 1) : ℕ) : ℤ)) ∧
          R.runFrom d t =
            { d with
              state := some exit
              workTapes := fun j q =>
                if j = 0 ∧ d.workTapePos j ≤ q ∧
                    q < d.workTapePos j + ((Nat.bits x.length).length : ℤ)
                  then FinTM.bufferTape (Nat.bits x.length) (q - d.workTapePos j)
                else d.workTapes j q } := by
  refine ⟨0, InputLengthPhase, inferInstance, inferInstance, inputLengthMachine,
    .count, .done, 6, ?_⟩
  intro x d hs hip blank _
  obtain ⟨t, charge, counted, countHeads⟩ := inputLength_count d hs hip blank x.length le_rfl
  let c := inputLengthCfg d x.length.bits x.length.bits.length .count
    (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0
  let back : Cfg 1 Bool InputLengthPhase x := {c with state := some .returnStart}
  have endSymbol : c.inputSymbol = none := by
    apply Cfg.inputSymbol_of_end
    rfl
  have turn : inputLengthMachine.step c = back := by
    rw [step_of_inputMoveAction _ _ 0 rfl (q' := .returnStart) (by
      simp [inputLengthMachine, endSymbol])]
    simp only [moveInputPos_zero]
    rfl
  obtain ⟨r, hr, returned, returnHeads⟩ := FinTM.rewind_heads inputLengthMachine
    .returnStart .returnScan (some .done) (by intros; rfl)
    (by
      intro inp work
      change (((inputFoldTM 1 (fun (_ : Unit) (_ : Bool) => ()) ()).tr
        (.bwd ()) inp work).mapState
        (fun q => match q with | .done _ => InputLengthPhase.done | _ => .returnScan)) = _
      rw [inputFoldTM_tr_bwd]
      cases inp <;> simp only [inputMoveAction_eq, FinTM.controlAction_def]
      all_goals
        change Action.mk _ _ _ _ = _
        simp only [Action.mapState_inputTape, Action.mapState_output,
          Action.mapState_state, Option.map_some]
        congr 1 <;> first | rfl | exact funext (Action.mapState_workTapes _ _)) back rfl
  have reachedBack : inputLengthMachine.runFrom d (t + 1) = back := by
    rw [MultiTapeTM.runFrom_succ_eq_step', counted]
    exact turn
  have finish : inputLengthMachine.runFrom d (t + 1 + r) =
      {back with state := some .done, inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, reachedBack, returned]
  have deadline : t + 1 + r ≤ 6 * (x.length + 1) := by
    have hr' : r ≤ x.length + 3 := by simpa [back, c, inputLengthCfg] using hr
    omega
  have heads (u : ℕ) (hu : u ≤ t + 1 + r) :
      d.workTapePos 0 - 1 ≤ (inputLengthMachine.runFrom d u).workTapePos 0 ∧
      (inputLengthMachine.runFrom d u).workTapePos 0 ≤
        d.workTapePos 0 + (x.length.bits.length : ℤ) := by
    by_cases h : u ≤ t
    · exact countHeads u h
    · have hu' : u - (t + 1) ≤ r := by omega
      rw [show u = t + 1 + (u - (t + 1)) by omega,
        MultiTapeTM.runFrom_add, reachedBack, returnHeads _ hu']
      simp only [back, c, inputLengthCfg, add_zero]
      constructor <;> omega
  -- The public fixed-stop entry contract keeps the exact completed configuration.
  obtain ⟨first, firstLe, firstCut, firstEnd⟩ := MultiTapeTM.exists_first_entry_of_fixed
    inputLengthMachine (fun q => q = .done) d
    {back with state := some .done, inputPos := 1} (t + 1 + r)
    (by
      rintro z ⟨q, hq, rfl⟩
      rw [step_of_inputMoveAction _ _ 0 hq (q' := .done) rfl]
      simp only [moveInputPos_zero]
      apply Cfg.ext <;> simp [hq])
    ⟨.done, rfl, rfl⟩ finish
  have same : inputLengthMachine.runFrom d (t + 1 + r) =
      inputLengthMachine.runFrom d first := finish.trans firstEnd.symm
  refine ⟨first, firstLe.trans deadline, ?_, ?_, ?_⟩
  · intro u hu hs
    exact firstCut u hu ⟨.done, hs, rfl⟩
  · intro u hu j
    have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
    subst j
    obtain ⟨lower, upper⟩ := heads u (hu.trans firstLe)
    apply abs_le.mpr
    push_cast
    constructor <;> omega
  · rw [← same, finish]
    apply Cfg.ext
    · rfl
    · exact hip.symm
    · funext j a
      have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
      subst j
      simp [back, c, inputLengthCfg]
    · funext j
      have hj : j = 0 := Fin.ext (by have h := j.isLt; omega)
      subst j
      simp [back, c, inputLengthCfg]
    · rfl

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Seam.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.CfgFacts
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: seam composition (R2)

The configuration-level sequencing layer of the machine-construction
library (`machine-library-design.md` §12, R2): sequential composition of
two controllers over **any tape alphabet and from arbitrary
configurations** (the `_ofCfg` theorems; alphabet-generic since §13d G1). If
`M₁` carries a configuration `c₀` to `c₁` within `T₁` under a first-return
cut, and `M₂` carries `c₁` to `c₂` within `T₂`, the dispatch-glued
composite carries `c₀` to `c₂` within `T₁ + 1 + T₂` — the explicit
constant is `1`, one silent stationary dispatch step at the seam. The
canonical `Turing.Cfg.ofWords` seams of
`TCSlib.Complexity.TuringMachine.Build.Convention` are the `Bool`
specialization (`Turing.seamCompTM_run` and its siblings). This is the generic form of the
per-batch dispatch gluing re-proved in every A-chain and emitter batch,
and it exists at the configuration level precisely because the emitter
round-1 finding stands: *function-level* contracts cannot deliver
clean-return seams, so composing `ComputesFunInTime` contracts can never
replace this combinator.

**Status: proved.** The composite is a real definition
(state-sum dispatch in `Turing.bufferedCompTM`'s style, kept minimal), and
every §12 contract is proved (§12 fill epoch F1, gate closed 2026-10-09). The
§12.8 two-exit row `Turing.seamCompTM₂_run_ofCfg` (R8.8) is proved from the left
prefix `Turing.seamCompTM_runFrom_left` and the existing right lockstep.
The **phase host** `Turing.phaseHostTM`, with `Turing.phaseHostTM_run` (proved), is the
finite-dispatch generalization: many phases and a redirect table, one dispatch step per
redirect (landed before the §12.8 fill for the record rows). Its start state is
`Turing.phaseHostTM_q₀`, its table off the redirects `Turing.phaseHostTM_tr_of_red_none` and at a
redirect `Turing.phaseHostTM_tr_of_red_some`, and `Turing.phaseHostTM_run_le` runs a last phase up
to its exit without a dispatch.

## Design

* The glue is a **state sum** `S₁ ⊕ S₂`: left states run `M₁`'s table,
  right states run `M₂`'s, and the designated left anchor `exit` takes one
  stationary, silent, write-free transition to the right anchor `entry`.
  Dispatch-on-anchor (rather than dispatch-on-halt) matches the ABI: seam
  contracts end at a **live** anchor (`Build/Loop.lean`'s `hstart`/
  `hround` shape), and the catalog routines of
  `TCSlib.Complexity.TuringMachine.Build.Catalog` exit at live anchors.
* The space clause is stated in the **sharp per-tape form** (frozen
  decision 12.1): the headline is per-tape containment of visited sets —
  the composite's visited set on every work tape is contained in the
  union of the phases' — which implies both the per-tape sum bound and
  the max bound for disjointly-owned tapes, stated as corollaries.

## Main definitions

* `Turing.seamCompTM` — the dispatch-glued composite of two machines over
  any alphabet; at `Bool`, its canonical use is between `Turing.Cfg.ofWords`
  seams.
* `Turing.seamCompTM₂` — a continuation on each of two exit anchors (§12.8,
  R8.8).

## Main results

* `Turing.seamCompTM_run` — seam-to-seam composition within
  `T₁ + 1 + T₂`.
* `Turing.seamCompTM_firstReturn` — the composite inherits a first-return
  cut at the final anchor, so composites **whose phases satisfy the stated
  cuts** chain (round-1 finding R3: the cut excludes positive
  entry-equals-exit calls — those route through the release adapter below).
* `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`,
  `Turing.seamCompTM_visitedByTapeHead_ofCfg` — the **general-configuration**
  composition (round-1 repair R2): phase two starts from phase one's
  returned configuration with only the control state replaced, so arbitrary
  frames, displaced inactive heads, and accumulated output cross the
  dispatch intact; the canonical `Cfg.ofWords` theorems are its instances.
* `Turing.seamReleaseTM`, `Turing.seamReleaseTM_firstReturn`,
  `Turing.seamReleaseTM_visitedByTapeHead` — the **fresh-entry/release
  adapter** (round-1 repair R3): the entry action executes unconditionally
  from a fresh start state, so a positive call that returns to its own
  anchor becomes seam-consumable.
* `Turing.seamCompTM_visitedByTapeHead` — per-tape visited-set
  containment (the headline space clause, decision 12.1).
* `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM₂_run_ofCfg` — the left
  prefix of a seam under a strict exit cut, and the two-exit composition
  (§12.8, R8.8; the latter a statement).
* `Turing.seamCompTM_runFrom_right` — the right segment after the dispatch, at any
  offset (promoted from the private `seamComp_right` at MIG-0b; set-valued exits need it).
* `Turing.seamReleaseTM_step_fresh`, `Turing.seamReleaseTM_step_inr`,
  `Turing.seamReleaseTM_runFrom_pos` — the release adapter's steps and its pointwise
  lockstep at every positive time (promoted from the private `seamRelease_*` lemmas at
  MIG-0b, design §16a item 5).
* `Turing.seamCompTM_spaceUsed_le_add_ofCfg` — the general-configuration sum bound on total
  space, with phase two's endpoint unconstrained.
* `Turing.seamCompTM_spaceUsedByTape_le_add`,
  `Turing.seamCompTM_spaceUsed_le_add`,
  `Turing.seamCompTM_spaceUsedByTape_le_max` — the sum and
  max-for-disjointly-owned-tapes corollaries.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; phase-sequenced simulations
  are the folklore engine of §1.4–§1.7.)
* [Balbach22] F. Balbach, *The Cook–Levin theorem*, Isabelle AFP entry
  `Cook_Levin`, 2022. (The composition-combinator architecture precedent,
  as in `TCSlib.Complexity.TuringMachine.Composition`.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model): the seam-composition shape is
  `StackRename`'s `executes_in_sum`.
-/

namespace Turing

variable {k : ℕ} {S₁ S₂ : Type*} {x : List Bool}

/-- **R2, the seam composite** (design §12; [Bon26], `executes_in_sum`).
The dispatch-glued sequential composite of `M₁` and `M₂`, over any tape
alphabet (at `Bool`, typically between `Turing.Cfg.ofWords` seams): states
are the sum `S₁ ⊕ S₂`, left states run
`M₁`'s transition table and right states `M₂`'s (each halting where its
phase halts), except that the designated left anchor `exit` takes one
stationary, silent, write-free dispatch step to the right anchor `entry`.
The composite starts at `M₁`'s initial state; a run launched at a left
seam anchor is the intended use. -/
def seamCompTM {Symbol : Type*} [DecidableEq S₁] (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) :
    MultiTapeTM k Symbol (S₁ ⊕ S₂) where
  q₀ := Sum.inl M₁.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      if s = exit then ⟨0, fun _ => (none, 0), none, some (Sum.inr entry)⟩
      else
        let a := M₁.tr s inp w
        ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inl⟩
    | Sum.inr s =>
      let a := M₂.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- At a right state, the seam composite uses the second machine's action with its
successor state injected into the right summand. -/
theorem seamCompTM_tr_inr {Symbol : Type*} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry q : S₂)
    (inp : Option Symbol) (work : Fin k → Option Symbol) :
    (seamCompTM M₁ exit M₂ entry).tr (Sum.inr q) inp work =
      (M₂.tr q inp work).mapState Sum.inr := by
  change Action.mk (M₂.tr q inp work).inputTape (M₂.tr q inp work).workTapes
    (M₂.tr q inp work).output ((M₂.tr q inp work).state.map Sum.inr) = _
  rw [← Action.mapState_inputTape Sum.inr (M₂.tr q inp work),
    ← funext (Action.mapState_workTapes Sum.inr (M₂.tr q inp work)),
    ← Action.mapState_output Sum.inr (M₂.tr q inp work),
    ← Action.mapState_state Sum.inr (M₂.tr q inp work)]

/-- Away from the exit, one left step is exactly the state-mapped source step,
including the absorbing halted case. -/
private lemma seamComp_step_left {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    (c : Cfg k Symbol S₁ x) (hc : c.state ≠ some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (M₁.step c).mapState Sum.inl := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    have hq : q ≠ exit := fun h => hc (hs.trans (congrArg some h))
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    dsimp only [seamCompTM]
    rw [if_neg hq]
    rfl

/-- Right steps commute with state mapping, even after a source halt.

**Proof sketch.** Renaming preserves the input and work reads. A halted configuration
stays fixed on both sides. For a live state, the right transition row and
`Cfg.mapState_apply` identify the two steps. -/
private lemma seamComp_step_right {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) (c : Cfg k Symbol S₂ x) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inr) =
      (M₂.step c).mapState Sum.inr := by
  have hin : (c.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).inputSymbol = c.inputSymbol :=
    Cfg.inputSymbol_congr _ _ (by rw [Cfg.mapState_inputPos])
  have hwork : (c.mapState (Sum.inr : S₂ → S₁ ⊕ S₂)).workTapeSymbols = c.workTapeSymbols := by
    funext i
    rw [Cfg.workTapeSymbols_eq, Cfg.workTapeSymbols_eq,
      Cfg.mapState_workTapes, Cfg.mapState_workTapePos]
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt (cfg := c.mapState (Sum.inr : S₂ → S₁ ⊕ S₂))
        (by rw [Cfg.mapState_state, hs, Option.map_none]),
      MultiTapeTM.step_of_halt hs]
  | some q =>
    rw [MultiTapeTM.step_of_some (cfg := c.mapState (Sum.inr : S₂ → S₁ ⊕ S₂))
        (q := Sum.inr q) (by rw [Cfg.mapState_state, hs, Option.map_some]),
      MultiTapeTM.step_of_some hs, hin, hwork, seamCompTM_tr_inr]
    exact Cfg.mapState_apply Sum.inr _ c

/-- A stationary, silent, write-free action changes only the control field. -/
private lemma seam_stationary_apply {Symbol : Type*} {x : List Symbol} (c : Cfg k Symbol S₁ x) (q : S₁) :
    (Action.mk 0 (fun _ => (none, 0)) none (some q)).apply c =
      { c with state := some q } := by
  simp [Action.apply]

/-- Dispatch preserves all data of an arbitrary live exit configuration. -/
private lemma seamComp_dispatch {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    (c : Cfg k Symbol S₁ x) (hc : c.state = some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (c.mapState fun _ => entry).mapState Sum.inr := by
  unfold MultiTapeTM.step
  simp only [Cfg.mapState, hc, Option.map_some]
  dsimp only [seamCompTM]
  rw [if_pos rfl, seam_stationary_apply]

/-- **R8.8, the left prefix of a seam** (design §12.8a; promoted from the
private `seamComp_left`, finding SC-4 of the §12.7 statement gate). If `M₁`,
started from an arbitrary configuration `c`, avoids its exit anchor at every
time strictly below `T`, then for every `t ≤ T` the composite started from the
left-mapped `c` is at the left-mapped `M₁` configuration at `t`. No endpoint
equation is required, and the endpoint itself is included. This is the
trajectory statement a host with two exits needs on the branch it does not
take.

**Proof sketch.** Induct on the time; the cut licenses the left-step
identity at every predecessor strictly before the endpoint. -/
theorem seamCompTM_runFrom_left {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c : Cfg k Symbol S₁ x} {T : ℕ}
    (hcut : ∀ t < T, (M₁.runFrom c t).state ≠ some exit)
    (t : ℕ) (ht : t ≤ T) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c.mapState Sum.inl) t =
      (M₁.runFrom c t).mapState Sum.inl := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      seamComp_step_left M₁ exit M₂ entry _ (hcut t (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']

/-- **The seam's right segment** (promoted from the private `seamComp_right` at MIG-0b, with its
universes and its proof; MIG-0a's export of the same name, over `Type`, is this statement's
instance): after the dispatch step, the composite runs the second machine in lockstep, for any
number of steps, from the first machine's endpoint with its state replaced by the second entry.
Set-valued exits need it.

**Proof sketch.** Split the run at the dispatch, use left lockstep and
the exit equation, then iterate the unconditional right-step identity. -/
theorem seamCompTM_runFrom_right {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (t : ℕ) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + t) =
      (M₂.runFrom (c₁.mapState fun _ => entry) t).mapState Sum.inr := by
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step',
    seamCompTM_runFrom_left M₁ exit M₂ entry hcut T₁ le_rfl, h₁,
    seamComp_dispatch M₁ exit M₂ entry c₁ hexit]
  exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
    (seamComp_step_right M₁ exit M₂ entry) _ t

/-- General endpoint composition, shared by the frozen public forms. -/
private lemma seamComp_run_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) = c₃.mapState Sum.inr :=
  (seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut T₂).trans
    (congrArg (Cfg.mapState Sum.inr) h₂)

/-- The right final anchor is absent before the total time.
**Proof sketch.** Through the left endpoint, constructor disjointness
excludes the anchor. Afterwards, right lockstep transports the phase-two
cut at the time remaining after dispatch. -/
private lemma seamComp_firstReturn_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry q₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  intro t ht
  by_cases hleft : t ≤ T₁
  · rw [seamCompTM_runFrom_left M₁ exit M₂ entry hcut t hleft]
    cases (M₁.runFrom c₀ t).state <;> simp [Cfg.mapState]
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut]
    intro heq
    apply hcut₂ (t - (T₁ + 1)) (by omega)
    change Option.map Sum.inr
      (M₂.runFrom (c₁.mapState fun _ => entry) (t - (T₁ + 1))).state =
        some (Sum.inr q₂) at heq
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
    exact hq.trans (congrArg some (Sum.inr.inj heq))

/-- Every visited position belongs to one of the two exact run segments.
**Proof sketch.** A time at most the left duration uses left lockstep.
Every later time is dispatch time plus a unique nonnegative offset, at
most the right duration; right lockstep supplies its image witness. -/
private lemma seamComp_visited_general {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
  have ht' := Finset.mem_range.mp ht
  by_cases hleft : t ≤ T₁
  · rw [seamCompTM_runFrom_left M₁ exit M₂ entry hcut t hleft]
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamCompTM_runFrom_right M₁ exit M₂ entry h₁ hexit hcut]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨t - (T₁ + 1), Finset.mem_range.mpr (by omega), rfl⟩

/-- **R2, seam-to-seam composition** (design §12;
[Bon26], `executes_in_sum`). If `M₁` carries the seam
`Cfg.ofWords start w₀` to the seam `Cfg.ofWords exit w₁` in exactly `T₁`
steps without visiting the anchor `exit` earlier (the first-return cut),
and `M₂` carries `Cfg.ofWords entry w₁` to `Cfg.ofWords q₂ w₂` in exactly
`T₂` steps, then the composite carries the left-mapped first seam to the
right-mapped last seam in exactly `T₁ + 1 + T₂` steps — the explicit
dispatch constant is `1`, not `O(1)`.

**Proof sketch.** Three segments composed with
`Turing.MultiTapeTM.runFrom_add`. (i) *Phase one lockstep*: on left
states other than the anchor, one composite step is the `Sum.inl`-mapped
`M₁` step; the cut guarantees the anchor is not visited before `T₁`, so
induction carries the left-mapped configuration to time `T₁`, where it is
`Cfg.ofWords (Sum.inl exit) w₁`. (ii) *Dispatch*: at the anchor the
composite takes the stationary silent step, and a stationary write-free
action fixes every tape, head, and the output of a seam configuration, so
time `T₁ + 1` is exactly `Cfg.ofWords (Sum.inr entry) w₁`. (iii) *Phase
two lockstep*: on right states one composite step is the
`Sum.inr`-mapped `M₂` step (`Turing.MultiTapeTM.runFrom_comm_of_step`),
carrying the seam to the right-mapped `Cfg.ofWords q₂ w₂` at time
`T₁ + 1 + T₂`. The degenerate case `T₁ = 0` (so `start = exit`,
`w₀ = w₁`) is covered because the dispatch step alone performs the
phase-one handover. -/
theorem seamCompTM_run [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) :
    (seamCompTM M₁ exit M₂ entry).runFrom
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) =
      Cfg.ofWords (Sum.inr q₂) w₂ := by
  have h₂' : M₂.runFrom
      ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry) T₂ =
        Cfg.ofWords q₂ w₂ := by
    simpa only [Cfg.ofWords_mapState] using h₂
  simpa only [Cfg.ofWords_mapState] using
    seamComp_run_general M₁ exit M₂ entry h₁ (Cfg.ofWords_state exit w₁) hcut h₂'

/-- **R2, the inherited first-return cut** (design
§12). Under the hypotheses of `seamCompTM_run`, if additionally `M₂` does
not visit its final anchor `q₂` strictly before `T₂`, then the composite
does not visit `Sum.inr q₂` strictly before `T₁ + 1 + T₂` — so a
composite is itself a seam-to-seam routine and chains under further
`seamCompTM` applications.

**Proof sketch.** Split the window. Before and at `T₁` the composite's
state is a left state (phase-one lockstep of `seamCompTM_run`), never
`Sum.inr q₂` by constructor disjointness. From `T₁ + 1` on, the
composite's state is the `Sum.inr` image of `M₂`'s state at the shifted
time (phase-two lockstep), and `Sum.inr` injectivity turns the `M₂` cut
into the composite cut; a mid-phase `M₂` halt is excluded because halting
absorbs and would contradict `h₂`'s live anchor at `T₂`. -/
theorem seamCompTM_firstReturn [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (Cfg.ofWords (input := x) entry w₁) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom
          (Cfg.ofWords (input := x) (Sum.inl start) w₀) t).state ≠
        some (Sum.inr q₂) := by
  have hcut₂' : ∀ t < T₂,
      (M₂.runFrom ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry)
        t).state ≠ some q₂ := by
    simpa only [Cfg.ofWords_mapState] using hcut₂
  simpa only [Cfg.ofWords_mapState] using
    seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ (Cfg.ofWords_state exit w₁) hcut hcut₂'

/-- **R2 space, the per-tape headline** (design §12,
frozen decision 12.1: the sharp per-tape form). On every work tape `i`,
the composite's visited set over the whole composed run is contained in
the union of the two phases' visited sets. This is the statement the sum
and max corollaries below both project from; it is deliberately the
containment itself, since downstream applications may depend on the
sharpness.

**Proof sketch.** Decompose the trajectory by the two lockstep segments
of `seamCompTM_run`: times `0, …, T₁` reproduce `M₁`'s head positions
(phase-one lockstep), time `T₁ + 1` is the dispatch step, which is
stationary — the head sits at the seam origin, already visited by both
phases' initial configurations — and times `T₁ + 1, …, T₁ + 1 + T₂`
reproduce `M₂`'s positions shifted by `T₁ + 1` (phase-two lockstep).
Every trajectory point therefore lies in one of the two phases' images;
conclude by `Finset.image` monotonicity over the split of
`Finset.range`. -/
theorem seamCompTM_visitedByTapeHead [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i ∪
        M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i := by
  simpa only [Cfg.ofWords_mapState] using
    seamComp_visited_general (T₂ := T₂) M₁ exit M₂ entry h₁ (Cfg.ofWords_state exit w₁) hcut i

/-- **R2′ space, the general per-tape headline**
(round-1 repair R2): under the hypotheses of `Turing.seamCompTM_run_ofCfg`,
on every work tape the composite's visited set over the composed run is
contained in the union of the two phases' visited sets — the
general-configuration form of `Turing.seamCompTM_visitedByTapeHead`, from
which the canonical corollaries project.

**Proof sketch.** As the canonical headline: the two lockstep segments
reproduce the phases' trajectories, and the dispatch step is stationary at
a point both phases' endpoint/start configurations already visit. -/
theorem seamCompTM_visitedByTapeHead_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  exact seamComp_visited_general M₁ exit M₂ entry h₁ hexit hcut i

/-- **R2′ space, the general sum bound**: under the hypotheses of
`Turing.seamCompTM_visitedByTapeHead_ofCfg` (phase one carries `c₀` to `c₁` in `T₁` steps,
first reaching the live anchor `exit` there), the composite's total space usage over `T₁ + 1 + T₂`
steps is at most phase one's up to `T₁` plus phase two's over `T₂` steps from `c₁` with its
control state replaced by `entry`. Phase two's endpoint is unconstrained (it may halt, or be no
seam), which the canonical `Turing.seamCompTM_spaceUsed_le_add` cannot express.

**Proof sketch.** On every tape, `Finset.card_le_card` on
`Turing.seamCompTM_visitedByTapeHead_ofCfg`, then `Finset.card_union_le`; sum over the tapes
(`Turing.MultiTapeTM.spaceUsed_eq_sum`, `Turing.MultiTapeTM.spaceUsedByTape_eq_card`). -/
theorem seamCompTM_spaceUsed_le_add_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) :
    (seamCompTM M₁ exit M₂ entry).spaceUsed (c₀.mapState Sum.inl) (T₁ + 1 + T₂) ≤
      M₁.spaceUsed c₀ T₁ + M₂.spaceUsed (c₁.mapState fun _ => entry) T₂ := by
  rw [MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum, MultiTapeTM.spaceUsed_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [MultiTapeTM.spaceUsedByTape_eq_card, MultiTapeTM.spaceUsedByTape_eq_card,
    MultiTapeTM.spaceUsedByTape_eq_card]
  exact (Finset.card_le_card (seamCompTM_visitedByTapeHead_ofCfg M₁ exit M₂ entry
    (T₂ := T₂) h₁ hexit hcut i)).trans (Finset.card_union_le _ _)

/-- **R2 space, the per-tape sum corollary** (design
§12, decision 12.1). On every work tape, the composite's space usage is
at most the sum of the phases' space usages on that tape.

**Proof sketch.** `Finset.card_le_card` on
`seamCompTM_visitedByTapeHead`, then `Finset.card_union_le`. -/
theorem seamCompTM_spaceUsedByTape_le_add [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).spaceUsedByTape
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
      M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i +
        M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i := by
  exact (Finset.card_le_card
    (seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂ w₀ w₁ w₂
      T₁ T₂ h₁ hcut h₂ i)).trans (Finset.card_union_le _ _)

/-- **R2 space, the total sum corollary** (design
§12). The composite's total space usage is at most the sum of the
phases' total space usages.

**Proof sketch.** The `Cfg.ofWords` instance of `seamCompTM_spaceUsed_le_add_ofCfg`: renaming a
seam's state gives the seam at the renamed state (`Turing.Cfg.ofWords_mapState`). -/
theorem seamCompTM_spaceUsed_le_add [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) :
    (seamCompTM M₁ exit M₂ entry).spaceUsed
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) ≤
      M₁.spaceUsed (Cfg.ofWords (input := x) start w₀) T₁ +
        M₂.spaceUsed (Cfg.ofWords (input := x) entry w₁) T₂ := by
  simpa only [Cfg.ofWords_mapState] using seamCompTM_spaceUsed_le_add_ofCfg (T₂ := T₂)
    M₁ exit M₂ entry h₁ (Cfg.ofWords_state exit w₁) hcut

/-- **R2 space, the max corollary for disjointly-owned tapes** (spec, fill
pending — design §12, frozen decision 12.1: the sharpest available form).
If one of the two phases is *idle* on tape `i` — its visited set is the
seam-origin singleton `{0}` — then the composite's space usage on `i` is
bounded by the **max** of the phases' usages, not their sum. Under a
tape-ownership discipline (each work tape owned by one phase, the other
phase never moving its head there) this gives per-tape space equal to the
owner's, which is what the chapter-4 consumers depend on.

**Proof sketch.** From `seamCompTM_visitedByTapeHead` the composite's
visited set is contained in the union, and the idle side's singleton
`{0}` is already contained in the other side's visited set — a seam
configuration has every head at the origin, so `0` is in every phase's
visited set at every horizon. The union collapses to the non-idle side's
set; `Finset.card_le_card` and `le_max_left/right` finish. -/
theorem seamCompTM_spaceUsedByTape_le_max [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k)
    (hown : M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i
        = {0} ∨
      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i = {0}) :
    (seamCompTM M₁ exit M₂ entry).spaceUsedByTape
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
      max (M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i)
        (M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i) := by
  have hzero₁ : (0 : ℤ) ∈
      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₁), rfl⟩
  have hzero₂ : (0 : ℤ) ∈
      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₂), rfl⟩
  have hsub := seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂
    w₀ w₁ w₂ T₁ T₂ h₁ hcut h₂ i
  rcases hown with hown | hown
  · rw [hown, Finset.union_eq_right.mpr
      (Finset.singleton_subset_iff.mpr hzero₂)] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_right _ _)
  · rw [hown, Finset.union_eq_left.mpr
      (Finset.singleton_subset_iff.mpr hzero₁)] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_left _ _)

/-- **R2′, general-configuration seam-to-seam composition** (spec, fill
pending — round-1 repair R2): the `Cfg.ofWords` restriction of
`Turing.seamCompTM_run` is lifted. If `M₁` carries an arbitrary
configuration `c₀` to `c₁` in exactly `T₁` steps, first reaching the anchor
`exit` there, and `M₂` carries `c₁` **with only the control state replaced
by `entry`** to `c₃` in `T₂` steps, then the composite carries the
`Sum.inl`-mapped `c₀` to the `Sum.inr`-mapped `c₃` in exactly
`T₁ + 1 + T₂` steps: the dispatch step is stationary, silent, and
write-free, so displaced inactive heads, noncanonical tape contents, the
input position, and **accumulated output** all cross it intact — exactly
the seams the round-1 audit exhibited (`emitterP2_relocate_run`'s arbitrary
frames, `exists_emitCallTM`'s nonempty output) that no `Cfg.ofWords`
endpoint can describe. The canonical `seamCompTM_run` is the
`Cfg.ofWords` instance.

**Proof sketch.** Identical three-segment decomposition to
`seamCompTM_run` — phase-one `Sum.inl` lockstep under the cut, one
dispatch step, phase-two `Sum.inr` lockstep via `Cfg.mapState_apply` —
with the single new observation that a stationary write-free action fixes
**every** field of an arbitrary configuration, not only a canonical one
(`Turing.Action.apply` componentwise). Fill obligations, named: the two
lockstep inductions over `Cfg.mapState`, the dispatch-step field check,
and the `ofWords` specialization recovering the canonical theorem. -/
theorem seamCompTM_run_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁] (M₁ : MultiTapeTM k Symbol S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) =
      c₃.mapState Sum.inr := by
  exact seamComp_run_general M₁ exit M₂ entry h₁ hexit hcut h₂

/-- **R2′, the general inherited first-return cut**
(round-1 repair R2): under the hypotheses of
`Turing.seamCompTM_run_ofCfg`, if `M₂` first reaches `q₂` at `T₂`, the
composite first reaches `Sum.inr q₂` at `T₁ + 1 + T₂`.

**Proof sketch.** As `seamCompTM_firstReturn`, over the general lockstep
segments: left times produce `Sum.inl` states, right times the
`Sum.inr`-mapped `M₂` states at shifted time, and injectivity of the
constructors transports the cuts. -/
theorem seamCompTM_firstReturn_ofCfg {Symbol : Type*} {x : List Symbol} [DecidableEq S₁]
    (M₁ : MultiTapeTM k Symbol S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry : S₂) (q₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₁ x} {c₃ : Cfg k Symbol S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃)
    (hq : c₃.state = some q₂)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  exact seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ hexit hcut hcut₂

/-- **R8.8, the two-exit seam** (design §12.8a). Attach a continuation to each
of two exit anchors of a host: `M₁` after `e₁` and `M₂` after `e₂`, by nesting
two `Turing.seamCompTM`s. The host `M₀` with two live anchors is typically
`Turing.counterLoopTM` with its `done` and `escape`. -/
def seamCompTM₂ {Symbol : Type*} {S₀ : Type*} [DecidableEq S₀] [DecidableEq S₁]
    (M₀ : MultiTapeTM k Symbol S₀) (e₁ e₂ : S₀) (M₁ : MultiTapeTM k Symbol S₁) (entry₁ : S₁)
    (M₂ : MultiTapeTM k Symbol S₂) (entry₂ : S₂) :
    MultiTapeTM k Symbol ((S₀ ⊕ S₁) ⊕ S₂) :=
  seamCompTM (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂

/-- **R8.8, the two-exit seam, general configurations** (design §12.8a).
Suppose the host `M₀`, from an arbitrary configuration `c₀`, reaches `c₁` at
exactly `T₀` and meets neither of the distinct anchors `e₁`, `e₂` earlier.
If `c₁` is at `e₁`, then for every `t` the two-exit composite at `T₀ + 1 + t`
is `M₁`'s run, from `c₁` with only the control state replaced by `entry₁`, at
`t`, mapped into the composite's states; the `M₂` summand is never entered.
Symmetrically, if `c₁` is at `e₂`, the composite at `T₀ + 1 + t` is `M₂`'s run
from `c₁` at `entry₂`. The dispatch costs one stationary step in either branch,
and the continuation runs unboundedly, halting included, so its own first-return
and trajectory statements transfer.

**Proof sketch.** Branch `e₁`: the outer seam's left machine is the inner
composite, whose states stay away from the outer exit `Sum.inl e₂`: before
`T₀` by the cut, at `T₀` because `e₁ ≠ e₂`, and afterwards because they are
`Sum.inr` states or halted. So `Turing.seamCompTM_runFrom_left` for the outer
seam reduces the run to the inner composite's, which `Turing.seamCompTM_run_ofCfg`
and the right lockstep of the inner seam evaluate. Branch `e₂`: the inner
composite reaches `Sum.inl e₂` at `T₀` by `Turing.seamCompTM_runFrom_left`,
never having met `e₁`, and the outer dispatch and right lockstep finish. -/
theorem seamCompTM₂_run_ofCfg {Symbol : Type*} {S₀ : Type*} {x : List Symbol}
    [DecidableEq S₀] [DecidableEq S₁]
    (M₀ : MultiTapeTM k Symbol S₀) (e₁ e₂ : S₀) (he : e₁ ≠ e₂)
    (M₁ : MultiTapeTM k Symbol S₁) (entry₁ : S₁) (M₂ : MultiTapeTM k Symbol S₂) (entry₂ : S₂)
    {c₀ c₁ : Cfg k Symbol S₀ x} {T₀ : ℕ}
    (h₀ : M₀.runFrom c₀ T₀ = c₁)
    (hcut : ∀ t < T₀, (M₀.runFrom c₀ t).state ≠ some e₁ ∧ (M₀.runFrom c₀ t).state ≠ some e₂) :
    (c₁.state = some e₁ → ∀ t : ℕ,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom
          ((c₀.mapState Sum.inl).mapState Sum.inl) (T₀ + 1 + t) =
        ((M₁.runFrom (c₁.mapState fun _ => entry₁) t).mapState Sum.inr).mapState Sum.inl) ∧
    (c₁.state = some e₂ → ∀ t : ℕ,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom
          ((c₀.mapState Sum.inl).mapState Sum.inl) (T₀ + 1 + t) =
        (M₂.runFrom (c₁.mapState fun _ => entry₂) t).mapState Sum.inr) := by
  constructor
  · intro h1 t
    have hcut₁ : ∀ s < T₀, (M₀.runFrom c₀ s).state ≠ some e₁ := fun s hs => (hcut s hs).1
    have hinner : ∀ s, (seamCompTM M₀ e₁ M₁ entry₁).runFrom (c₀.mapState Sum.inl)
        (T₀ + 1 + s) = (M₁.runFrom (c₁.mapState fun _ => entry₁) s).mapState Sum.inr :=
      fun s => seamCompTM_run_ofCfg M₀ e₁ M₁ entry₁ h₀ h1 hcut₁ rfl
    have hcutO : ∀ s < T₀ + 1 + t, ((seamCompTM M₀ e₁ M₁ entry₁).runFrom
        (c₀.mapState Sum.inl) s).state ≠ some (Sum.inl e₂) := by
      intro s hs h
      by_cases hle : s ≤ T₀
      · rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ s hle] at h
        rcases Nat.lt_or_ge s T₀ with hlt | hge
        · exact (hcut s hlt).2 (by simpa [Cfg.mapState] using h)
        · obtain rfl : s = T₀ := by omega
          rw [h₀] at h
          exact he (by simpa [Cfg.mapState, h1] using h)
      · obtain ⟨r, rfl⟩ : ∃ r, s = T₀ + 1 + r := ⟨s - (T₀ + 1), by omega⟩
        rw [hinner r] at h
        simp [Cfg.mapState] at h
    have h := seamCompTM_runFrom_left (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂
      hcutO (T₀ + 1 + t) le_rfl
    rw [hinner t] at h
    exact h
  · intro h2 t
    have hcut₁ : ∀ s < T₀, (M₀.runFrom c₀ s).state ≠ some e₁ := fun s hs => (hcut s hs).1
    have hin : (seamCompTM M₀ e₁ M₁ entry₁).runFrom (c₀.mapState Sum.inl) T₀ =
        c₁.mapState Sum.inl := by
      rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ T₀ le_rfl, h₀]
    have hcutO : ∀ s < T₀, ((seamCompTM M₀ e₁ M₁ entry₁).runFrom
        (c₀.mapState Sum.inl) s).state ≠ some (Sum.inl e₂) := by
      intro s hs h
      rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ s hs.le] at h
      exact (hcut s hs).2 (by simpa [Cfg.mapState] using h)
    have hmap : ((c₁.mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState (fun _ => entry₂) :
        Cfg k Symbol S₂ x) = c₁.mapState (fun _ => entry₂) := by
      apply Cfg.ext <;> simp [Cfg.mapState, h2]
    have h := seamCompTM_run_ofCfg (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂ hin
      (by simp [Cfg.mapState, h2]) hcutO
      (rfl : M₂.runFrom ((c₁.mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState fun _ => entry₂) t = _)
    rw [hmap] at h
    exact h

variable {S : Type*}

/-- **R3′, the fresh-entry/release adapter** (round-1 repair R3). The seam
combinator dispatches at its exit anchor **before** that state's action, so
a positive call that starts and ends at one anchor cannot be cut
(`seamCompTM_firstReturn`'s cut is contradictory at zero — the round-1
finding, witnessed by `exists_installCallTM`/`exists_emitCallTM`'s
strictly-positive interior promises and `emitterP2_call_segment`'s
execute-first discipline). The adapter runs `M` on states `Unit ⊕ S` with a
fresh start `Sum.inl ()` that executes the anchor's action
**unconditionally**, after which control lives in the `Sum.inr` copy — so
the *first re-arrival* at `Sum.inr anchor` is a genuine positive-time
event a seam can consume as its left exit. -/
def seamReleaseTM {Symbol : Type*} (M : MultiTapeTM k Symbol S) (anchor : S) :
    MultiTapeTM k Symbol (Unit ⊕ S) where
  q₀ := Sum.inl ()
  tr := fun q inp w =>
    match q with
    | Sum.inl _ =>
      let a := M.tr anchor inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩
    | Sum.inr s =>
      let a := M.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- **The release's fresh step** (promoted from the private `seamRelease_fresh_step` at MIG-0b):
from a configuration at the anchor, the release adapter's fresh state applies the anchor's action,
and the resulting state is right-tagged. There is no dispatch step. -/
theorem seamReleaseTM_step_fresh {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) (hc : c.state = some anchor) :
    (seamReleaseTM M anchor).step (c.mapState fun _ => Sum.inl ()) =
      (M.step c).mapState Sum.inr := by
  simp only [MultiTapeTM.step, Cfg.mapState, hc, Option.map_some]
  rfl

/-- **The release's right-tagged steps** (promoted from the private `seamRelease_step_right` at
MIG-0b): on a right-tagged configuration, a step of the release adapter is the source step,
right-tagged; a halted configuration stays halted. -/
theorem seamReleaseTM_step_inr {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) :
    (seamReleaseTM M anchor).step (c.mapState Sum.inr) =
      (M.step c).mapState Sum.inr := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- **The pointwise release lockstep** (design §16a item 5; promoted from the private
`seamRelease_run_pos` at MIG-0b, with its universes and its proof): started at its fresh state
over a configuration at the anchor, the release adapter is, at every positive time, the source
run with its states right-tagged. This also covers a source that halts or never returns.

**Proof sketch.** Execute the fresh step once (`Turing.seamReleaseTM_step_fresh`), then iterate
the right-step identity (`Turing.seamReleaseTM_step_inr`). -/
theorem seamReleaseTM_runFrom_pos {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) (c : Cfg k Symbol S x) (hc : c.state = some anchor) (t : ℕ) (ht : 0 < t) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) t =
      (M.runFrom c t).mapState Sum.inr := by
  cases t with
  | zero => omega
  | succ t =>
    rw [MultiTapeTM.runFrom_succ_eq_step, seamReleaseTM_step_fresh M anchor c hc,
      MultiTapeTM.runFrom_succ_eq_step]
    exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
      (seamReleaseTM_step_inr M anchor) _ t

/-- **R3′, the positive first return through the adapter** (spec, fill
pending — round-1 repair R3): if `M`, started at its anchor, first
re-visits the anchor at a strictly positive time `T`, then the adapter,
started at its fresh state over the same configuration, reaches
`Sum.inr anchor` first at exactly `T`, over the `Sum.inr`-transported run.
The audit's S7 check is the smallest case: a two-step write-then-return
call executes both source actions before any seam dispatch can fire.

**Proof sketch.** The fresh step applies the anchor's action verbatim
(`Cfg.mapState_apply` at the constant relabeling), after which every step
is `Sum.inr`-lockstep with `M`'s run; the first-visit clause is the
transported cut, with time zero excluded by the fresh constructor
(`Sum.inl ≠ Sum.inr`). Fill obligations, named: the fresh-step equation,
the lockstep induction, and the cut transport. -/
theorem seamReleaseTM_firstReturn {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S) (anchor : S)
    {c c' : Cfg k Symbol S x} {T : ℕ}
    (hc : c.state = some anchor) (hT : 0 < T) (h : M.runFrom c T = c')
    (hc' : c'.state = some anchor)
    (hcut : ∀ t, 0 < t → t < T → (M.runFrom c t).state ≠ some anchor) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) T =
        c'.mapState Sum.inr ∧
      ∀ t < T,
        ((seamReleaseTM M anchor).runFrom
            (c.mapState fun _ => Sum.inl ()) t).state ≠
          some (Sum.inr anchor) := by
  constructor
  · rw [seamReleaseTM_runFrom_pos M anchor c hc T hT, h]
  · intro t ht
    by_cases htpos : 0 < t
    · rw [seamReleaseTM_runFrom_pos M anchor c hc t htpos]
      intro heq
      apply hcut t htpos ht
      change Option.map Sum.inr (M.runFrom c t).state =
        some (Sum.inr anchor) at heq
      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
      exact hq.trans (congrArg some (Sum.inr.inj heq))
    · have htzero : t = 0 := by omega
      simp [htzero, Cfg.mapState, hc]

/-- **R3′ space** (round-1 repair R3): the adapter's
visited sets equal `M`'s at every time and on every tape — the trajectories
coincide step for step.

**Proof sketch.** Every adapter step applies the very action `M` applies at
the corresponding state (the fresh step at the anchor, `Sum.inr` steps at
their carried state), so the head trajectories agree; project
`seamReleaseTM_firstReturn`'s lockstep. -/
theorem seamReleaseTM_visitedByTapeHead {Symbol : Type*} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (anchor : S) {c : Cfg k Symbol S x} (hc : c.state = some anchor)
    (t : ℕ) (i : Fin k) :
    (seamReleaseTM M anchor).visitedByTapeHead
        (c.mapState fun _ => Sum.inl ()) t i =
      M.visitedByTapeHead c t i := by
  unfold MultiTapeTM.visitedByTapeHead
  apply Finset.image_congr
  intro s _
  dsimp only
  by_cases hs : s = 0
  · subst s
    rfl
  · rw [seamReleaseTM_runFrom_pos M anchor c hc s (Nat.pos_of_ne_zero hs)]
    rfl

/-! ### The phase host: finite dispatch over many phases (§12.8 fill)

`Turing.seamCompTM` dispatches one exit and `Turing.seamCompTM₂` two. A module that branches
on finite data, or repeats a row a data-dependent but bounded number of times, needs one host
over a finite family of phases with a redirect table. -/

/-- **The phase host** (design §12.8a, record rows; §12.8 fill). Phase `i` runs `M i`. A
state that `red` maps to `some q` takes one stationary, silent dispatch step to `q`; every
other state follows its phase's table. With two phases and one redirect it is the seam
discipline of `Turing.seamCompTM`. -/
def phaseHostTM {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) : MultiTapeTM k Γ (Σ i, Ph i) where
  q₀ := q0
  tr := fun q inp w =>
    match red q.1 q.2 with
    | some q' => ⟨0, fun _ => (none, 0), none, some q'⟩
    | none => ((M q.1).tr q.2 inp w).mapState (Sigma.mk q.1)

/-- **The phase host's table off the redirects**: at a state `s` of phase `i` that `red` does
not redirect, the host takes phase `i`'s action, with the successor state tagged by `i`. -/
theorem phaseHostTM_tr_of_red_none {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) (s : Ph i) (hs : red i s = none)
    (inp : Option Γ) (w : Fin k → Option Γ) :
    (phaseHostTM M q0 red).tr ⟨i, s⟩ inp w = ((M i).tr s inp w).mapState (Sigma.mk i) := by
  simp only [phaseHostTM, hs]

/-- **The phase host's start state** is the given `q0`. -/
theorem phaseHostTM_q₀ {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) : (phaseHostTM M q0 red).q₀ = q0 :=
  rfl

/-- **The phase host's table at a redirect**: at a state `s` of phase `i` that `red` redirects to
`q'`, the host takes one silent step to `q'`, moving no head and writing nothing. -/
theorem phaseHostTM_tr_of_red_some {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) (s : Ph i) {q' : Σ i, Ph i}
    (hs : red i s = some q') (inp : Option Γ) (w : Fin k → Option Γ) :
    (phaseHostTM M q0 red).tr ⟨i, s⟩ inp w = ⟨0, fun _ => (none, 0), none, some q'⟩ := by
  simp only [phaseHostTM, hs]

/-- **The phase lemma for a last phase.** Run phase `i` from `c` for `T` steps, with no
redirect strictly before `T`. Then, up to and including `T`, the host is the phase run with
states tagged by `i`. Unlike `Turing.phaseHostTM_run`, nothing is assumed of the state at `T`:
it may be a live exit that `red` does not redirect, so this serves a host's last phase.

**Proof sketch.** On every state reached before `T` the host's table is the tagged phase table
(`Turing.phaseHostTM_tr_of_red_none`), so the agreement transfer
`Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` gives the run up to `T`. -/
theorem phaseHostTM_run_le {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) {x : List Γ}
    (c : Cfg k Γ (Ph i) x) (T : ℕ)
    (hguard : ∀ u < T, ∀ s, ((M i).runFrom c u).state = some s → red i s = none) :
    ∀ u ≤ T, (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) u =
        ((M i).runFrom c u).mapState (Sigma.mk i) := by
  intro u hu
  exact MultiTapeTM.runFrom_mapState_of_agreeOn (M i) (phaseHostTM M q0 red)
    ⟨Sigma.mk i, sigma_mk_injective⟩ (fun s => red i s = none)
    (fun s hs inp work => phaseHostTM_tr_of_red_none M q0 red i s hs inp work)
    c u (fun v hv s hs => hguard v (by omega) s hs)

/-- **The phase lemma** (§12.8 fill). Run phase `i` from `c` for `T` steps to `c'`, ending in
a state that `red` redirects to `q'`, with no redirect earlier. Then, up to `T`, the host is
the phase run with states tagged by `i`; one dispatch step later it is `c'` with only its
control replaced by `q'`.

**Proof sketch.** The prefix up to `T` is `Turing.phaseHostTM_run_le`. The dispatch is one step,
read through `Turing.MultiTapeTM.step_of_some`, the host's table at the redirected exit, and the
field equations of `Turing.Action.apply` and `Turing.Cfg.mapState`. No seam induction is
repeated. -/
theorem phaseHostTM_run {k : ℕ} {Γ : Type} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (i : I) {x : List Γ}
    (c c' : Cfg k Γ (Ph i) x) (T : ℕ) (h : (M i).runFrom c T = c') (s' : Ph i)
    (hs' : c'.state = some s') (q' : Σ i, Ph i) (hred : red i s' = some q')
    (hguard : ∀ u < T, ∀ s, ((M i).runFrom c u).state = some s → red i s = none) :
    (∀ u ≤ T, (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) u =
        ((M i).runFrom c u).mapState (Sigma.mk i)) ∧
      (phaseHostTM M q0 red).runFrom (c.mapState (Sigma.mk i)) (T + 1) =
        c'.mapState (fun _ => q') := by
  have hpre := phaseHostTM_run_le M q0 red i c T hguard
  refine ⟨hpre, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', hpre T le_rfl, h]
  have hst : (c'.mapState (Sigma.mk i)).state = some ⟨i, s'⟩ := by
    rw [Cfg.mapState_state, hs']
    rfl
  have htr : (phaseHostTM M q0 red).tr ⟨i, s'⟩ (c'.mapState (Sigma.mk i)).inputSymbol
      (c'.mapState (Sigma.mk i)).workTapeSymbols = ⟨0, fun _ => (none, 0), none, some q'⟩ := by
    simp only [phaseHostTM, hred]
  rw [MultiTapeTM.step_of_some hst, htr]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [Action.apply_state, Cfg.mapState_state, hs']
    rfl
  · rw [Action.apply_inputPos, moveInputPos_zero, Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j q
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    show Function.update ((c'.mapState (Sigma.mk i)).workTapes j)
      ((c'.mapState (Sigma.mk i)).workTapePos j)
      ((c'.mapState (Sigma.mk i)).workTapes j ((c'.mapState (Sigma.mk i)).workTapePos j)) q = _
    rw [Function.update_eq_self, Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j
    rw [Action.apply_workTapePos, Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
    exact add_zero _
  · rw [Action.apply_output, Cfg.mapState_output, Cfg.mapState_output]
    exact List.append_nil _


end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/Embed.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Build.Convention

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: bank embedding (R1)

The general tape-embedding layer of the machine-construction library
(`machine-library-design.md` §12, R1): a verified routine on its own
`m`-tape set runs on any injectively selected subset of a `k`-tape host's
work tapes, cost unchanged, everything else framed. This is the §5
deferral promoted — the design deferred the general form "until a third
site needs it", and the third, fourth, and fifth sites have arrived (the
chapter-1/2 retrofit families, the Hennie–Stearns conversion, the
two-work-tape universal machine). **Scope, stated precisely** (round-1
note R9): `ι` selects whole distinct physical tapes with coordinates
intact — it does not multiplex several virtual tapes onto zones of one
physical tape, shrink the tape count, or alter the source input word; the
Hennie–Stearns and universal-machine consumers get their zone/virtual-input
representation layers separately, with this module supplying only the
fixed-physical-bank routine relocation. It is the generic form of the private
`emitterBank*`/`emitterP2*` relocation families of
`TCSlib.Complexity.TuringMachine.Build.Primitives`, of the 4A chain's
`clBank*`/`clSlot*` families, and of the retained-tape disciplines that
`Build/Loop.lean` and `Build/Wrappers.lean` carry internally.

**Status: proved.** The transformers and configuration transports below
are real definitions, and every contract is proved: the §12 fill epochs
(gates closed 2026-10-09) and the later additive exports, the last of them
the guarded state transport (retrofit RB5, 2026-10-10).

## Design

Per frozen decision 12.4 there are **two named transformers over one
shared private core** (`embedActionCore`), so each spec stays crisp and a
consumer cites whichever fits:

* `Turing.embedSilentTM` — the W1/capture flavor: the embedded routine's
  emissions are recorded on a designated host work tape `cap` outside the
  selected bank, and the host's physical output stays silent.
* `Turing.embedEmitTM` — the E2/forwarding flavor: emissions pass to the
  host's physical output verbatim.

The two **closed** transformers preserve the source state type and map
the source halt to the host halt; their lockstep is unguarded, holding at
every time with the step count preserved exactly. The round-1 audit
(finding R1) refuted the earlier claim that live-return dispatch could be
left to the seam combinator: a source whose final transition emits and
halts loses that emission either way — the closed embedding is halted
after it, and a seam exit at the sole live state dispatches *before* it.
The **returning** flavors below repair this with an explicit halt-to-live
adapter built into the action core: `Turing.embedSilentRetTM` and
`Turing.embedEmitRetTM` run the source on states `S ⊕ Unit`, execute every
source action **through the halting transition** — the final emission
included — and land in the live return anchor `Sum.inr ()`, which a seam
then consumes as its left exit (`Turing.captureAction`'s and
`Turing.emitterRightTM`'s halt-to-live discipline, now exported).
`Turing.captureAction`/`Turing.capture_run` and
`Turing.emitAction`/`Turing.emit_run` are the fixed-shape precursors
(last-tape capture, identity selection); their statements are untouched.

## Main definitions

* `Turing.embedSilentCfg`, `Turing.embedEmitCfg` — a source configuration
  transported along `ι : Fin m ↪ Fin k`, with the unselected host tapes
  carried as frame parameters.
* `Turing.embedSilentTM`, `Turing.embedEmitTM` — the two closed machine
  transformers.
* `Turing.Cfg.select` — the selected bank of a host configuration, with empty output
  (moved from `Build/Contract.lean` at MIG-0b's layering split).
* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning
  transformers (round-1 repair R1): source halts land in the live return
  anchor `Sum.inr ()`, with the halting transition executed in full.

## Main results

* `Turing.embedEmitCfg_unselected`, `Turing.embedEmitCfg_select` — the frame export and
  the selection identity (moved from `Build/Contract.lean` at MIG-0b's layering split).
* `Turing.embedEmitCfg_eq`, `Turing.embedEmitCfg_mapState_eq`,
  `Turing.embedEmitCfg_ofWords_eq` — the R1 reconstruction lemma and its corollaries
  (MIG-0b; the wave-1 fill gate's major F1). `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`
  moved to `StateRenaming` at MIG-0b.
* `Turing.embedEmitTM_tr` — the forwarding transformer's transition at the action level:
  the source action on each selected tape, `(none, 0)` on every other tape, and the input
  move, output and successor state unchanged (12.2c item 6's export).
* `Turing.embedSilentCfg_cap` — the silent transport's capture tape and head, off the
  selection (the C1-A assembly gate's export, 2026-10-14).
* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:
  the transported run is the transport of the source run, same step count.
* `Turing.embedSilentTM_frame`, `Turing.embedEmitTM_frame` — tapes outside
  `Set.range ι` byte-identical with heads unmoved, input position tracking
  the source, output per flavor.
* `Turing.embedSilentTM_visitedByTapeHead`,
  `Turing.embedEmitTM_visitedByTapeHead` (and `_frame` companions),
  `Turing.embedSilentTM_spaceUsedByTape_cap` — per-tape space: host tape
  `ι i` visits exactly the source's tape-`i` cells, unselected tapes visit
  nothing new, and the capture tape is bounded by the recorded output.
* `Turing.embedSilentRetTM_run`, `Turing.embedEmitRetTM_run` — the
  through-halt contracts: live lockstep, then the handover at the source's
  first halt, final emission and source residue preserved, with the return
  anchor reached first exactly there.
* `Turing.embedSilentRetTM_visitedByTapeHead`,
  `Turing.embedEmitRetTM_visitedByTapeHead` — the returning flavors visit
  exactly what the closed flavors visit, at every time.
* `Turing.embedSilentCfg_unselected`, `Turing.embedSilentCfg_state`, `_inputPos`, `_output`,
  `Turing.embedEmitCfg_state`, `_inputPos`, `_output` — the transports' remaining fields, the
  specification API (user, 2026-10-16).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; tape-subset simulations are the
  folklore of the §1.3/§1.7 robustness and simulation arguments.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the bank-embedding shape is `StackRename`'s
  `rename_executes`.
-/

namespace Turing

variable {m k : ℕ} {S : Type*} {Symbol : Type*} {x : List Symbol}

/-- The partial inverse of the tape selection: the source index that `ι`
sends to host tape `j`, or `none` when `j` is unselected. Injectivity of
`ι` makes the first `List.find?` hit the unique preimage. -/
private def embedSlot (ι : Fin m ↪ Fin k) (j : Fin k) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (ι i = j)

/-- Searching at a selected tape returns its unique source index. -/
private lemma embedSlot_selected (ι : Fin m ↪ Fin k) (i : Fin m) :
    embedSlot ι (ι i) = some i := by
  unfold embedSlot
  cases hs : (List.finRange m).find? (fun j => decide (ι j = ι i)) with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp)
    simp at hn
  | some j =>
    have hj := List.find?_some hs
    have hji : j = i := ι.injective (of_decide_eq_true hj)
    subst j
    rfl

/-- Searching outside the selected bank returns no source index. -/
private lemma embedSlot_unselected (ι : Fin m ↪ Fin k) (j : Fin k)
    (hj : j ∉ Set.range ι) : embedSlot ι j = none := by
  unfold embedSlot
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq]
  exact fun hij => hj ⟨i, hij⟩

/-- The shared private core of the two embedding transformers (frozen
decision 12.4): transport one source action along `ι`, keeping the input
move and the successor state, performing the source's tape-`i` action on
host tape `ι i`, and leaving every unselected tape stationary and
unwritten — except that an emission is handled per the mode `sink`:
`sink = some cap` records it on host tape `cap` with a right move (the
capture discipline of `Turing.captureAction`) and keeps the host output
silent, while `sink = none` forwards it as the host's physical emission
(the discipline of `Turing.emitAction`). -/
private def embedActionCore (ι : Fin m ↪ Fin k) (sink : Option (Fin k))
    (a : Action m Symbol S) : Action k Symbol S where
  inputTape := a.inputTape
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => a.workTapes i
    | none =>
      match sink with
      | some cap =>
        if j = cap then
          match a.output with
          | some b => (some (some b), SignType.pos)
          | none => (none, 0)
        else (none, 0)
      | none => (none, 0)
  output :=
    match sink with
    | some _ => none
    | none => a.output
  state := a.state

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, suppressing flavor: same control state and input position,
source tape `i` sitting on host tape `ι i` (content and head), the
designated capture tape `cap` holding `pre ++ c.output` — the emissions
recorded so far after a pre-existing prefix — with its head one past that
word, every other unselected tape holding the ambient frame `tapes j` with
its head at `heads j`, and the host's physical output the untouched
`out₀`. Generic form of the `emitterBank*`/`clBank*` configuration
correspondences; for a source of `m` tapes in a host of `m + 1` with the
last tape selected as capture, it degenerates to `Turing.captureCfg` up to
the state embedding (round-1 restatement note: the specialization enlarges
the tape count by one — it is not `m = k`). [Bon26] -/
def embedSilentCfg (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) : Cfg k Symbol S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none =>
      if j = cap then FinTM.bufferTape (pre ++ c.output) else tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none =>
      if j = cap then ((pre ++ c.output).length : ℤ) else heads j
  output := out₀

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, forwarding flavor: same control state and input position,
source tape `i` on host tape `ι i`, every unselected tape holding the
ambient frame, and the host's physical output equal to the host's prior
output `pre` followed by everything the source has emitted. Generic form
of the `emitterP2*` relocation correspondences; at `ι = id` it is
`Turing.emitCfg` up to the state embedding. [Bon26] -/
def embedEmitCfg (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) : Cfg k Symbol S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none => tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none => heads j
  output := pre ++ c.output

/-- **R1, the suppressing embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, recording every emission on the designated host work tape `cap`
(intended outside `Set.range ι`) and emitting nothing physically — the
W1/capture flavor. States are preserved and the source halt is the host
halt; live return dispatch is the seam combinator's job. -/
def embedSilentTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S) : MultiTapeTM k Symbol S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι (some cap) (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, with every emission passed to the host's physical output verbatim —
the E2 flavor. States are preserved and the source halt is the host
halt. -/
def embedEmitTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) :
    MultiTapeTM k Symbol S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι none (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding transformer's transition** (12.2c item 6's prerequisite export;
user, 2026-10-10, from the RB5 review). One host transition of `embedEmitTM ι M` is the
source transition, read through `ι` and transported along it. Each selected host tape
`ι i` performs the source's tape-`i` action. Every unselected tape is stationary and
unwritten, `(none, 0)`. The input move, the output and the successor state are the
source's. Consumers cite this rather than unfolding the private slot search. [Bon26]

**Proof sketch.** `embedEmitTM` is `embedActionCore ι none` of the source action. The
selected and unselected tapes are the slot inverse's two equations, `embedSlot ι (ι i) =
some i` and `embedSlot ι j = none` off `Set.range ι`. The other three fields are copied
verbatim. -/
theorem embedEmitTM_tr (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) (q : S)
    (inp : Option Symbol) (w : Fin k → Option Symbol) :
    ((embedEmitTM ι M).tr q inp w).inputTape = (M.tr q inp fun i => w (ι i)).inputTape ∧
      (∀ i, ((embedEmitTM ι M).tr q inp w).workTapes (ι i) =
        (M.tr q inp fun i => w (ι i)).workTapes i) ∧
      (∀ j, j ∉ Set.range ι → ((embedEmitTM ι M).tr q inp w).workTapes j = (none, 0)) ∧
      ((embedEmitTM ι M).tr q inp w).output = (M.tr q inp fun i => w (ι i)).output ∧
      ((embedEmitTM ι M).tr q inp w).state = (M.tr q inp fun i => w (ι i)).state := by
  refine ⟨rfl, fun i => ?_, fun j hj => ?_, rfl, rfl⟩
  · simp [embedEmitTM, embedActionCore, embedSlot_selected]
  · simp [embedEmitTM, embedActionCore, embedSlot_unselected ι j hj]

/-- Applying the silent core commutes with configuration transport.
**Proof sketch.** Selected tapes perform the source action. Off-bank tapes
are stationary, except that capture appends the emitted symbol at the old
word length. Input movement and successor control are copied verbatim. -/
private lemma embedSilent_apply (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (a : Action m Symbol S) :
    (embedActionCore ι (some cap) a).apply
        (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            ← List.append_assoc, FinTM.bufferTape_append]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            Nat.cast_add, add_assoc]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · simp [embedActionCore, embedSilentCfg, Action.apply]

/-- The silent host reads the source action and executes all its effects
in one step; halted configurations remain fixed on both sides. -/
private lemma embedSilent_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) :
    (embedSilentTM ι cap M).step (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedSilentCfg, hs]
  | some q =>
    rw [show (embedSilentCfg ι cap tapes heads pre out₀ c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedSilentCfg ι cap tapes heads pre out₀ c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedSilentCfg, embedSlot_selected]
    change (embedActionCore ι (some cap) (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedSilent_apply ι cap tapes heads pre out₀ c _

/-- **R1 lockstep, suppressing flavor** (design §12;
[Bon26], `rename_executes`). The transported run *is* the transport of the
source run, at every time and with the step count preserved exactly: `t`
host steps simulate `t` source steps. No liveness guard is needed — the
transformer preserves states, so a halted source transports to a halted
host and both runs stall together.

**Proof sketch.** One-step commutation plus
`Turing.MultiTapeTM.runFrom_comm_of_step`. For the step: a halted source
makes both sides the identity. For a live source state, the host reads the
source symbols through `ι` (the transport puts source tape `i` at `ι i`),
so the host applies `embedActionCore` of the very action the source
applies; componentwise, selected tapes update as the source's
(`Turing.Action.apply` through the `embedSlot` inverse, whose two
equations `embedSlot ι (ι i) = some i` and `embedSlot ι j = none` off the
range are the `List.find?` glue obligations), unselected tapes receive the
stationary no-write action, the capture tape appends the optional emission
at head `|pre ++ c.output|` (`Turing.FinTM.bufferTape_append`, exactly as
in `capture_apply`), silence keeps the output at `out₀`, and the states
agree. -/
theorem embedSilentTM_runFrom (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t =
      embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step
    (embedSilentCfg ι cap tapes heads pre out₀)
    (embedSilent_step ι cap M tapes heads pre out₀) c t

/-- **R1 frame, suppressing flavor** (design §12).
Along the whole transported run, every host tape outside the selected bank
and distinct from the capture tape is byte-identical to its ambient frame
with its head unmoved; the input position tracks the source's; and the
host's physical output stays `out₀` (output silence).

**Proof sketch.** Project the lockstep equation
`embedSilentTM_runFrom` componentwise: the transport's `workTapes`/
`workTapePos` at an unselected `j ≠ cap` are the frame parameters by the
`embedSlot` off-range equation, its `inputPos` is the source's, and its
`output` is `out₀` by definition. -/
theorem embedSilentTM_frame (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι → j ≠ cap →
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapes j
        = tapes j ∧
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapePos j
        = heads j) ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).output = out₀ := by
  rw [embedSilentTM_runFrom ι cap hcap]
  refine ⟨?_, rfl, rfl⟩
  intro j hj hjc
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]

/-- **R1 space, suppressing flavor, selected tapes**
(design §12: "cells visited on host tape `ι i` equal cells visited on
source tape `i`"). The visited set of host tape `ι i` up to time `t` is
exactly the source's visited set of tape `i`, so the per-tape space
agrees on the nose.

**Proof sketch.** Both visited sets are images of `Finset.range (t + 1)`
under the respective head trajectories
(`Turing.MultiTapeTM.visitedByTapeHead`), and the lockstep equation
`embedSilentTM_runFrom` makes the trajectories pointwise equal at `ι i`
via the transport's `workTapePos` clause and `embedSlot ι (ι i) = some i`.
The cardinality clause is `congrArg Finset.card`. -/
theorem embedSilentTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (i : Fin m) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, suppressing flavor, unselected tapes** (spec, fill
pending — design §12: "unselected tapes visit nothing new"). A host tape
outside the selected bank and distinct from the capture tape visits
exactly the singleton of its initial head position, so its space usage is
one cell.

**Proof sketch.** By `embedSilentTM_frame` the head of such a tape never
moves, so the trajectory image collapses to `{heads j}`; the cardinality
clause is `Finset.card_singleton`. -/
theorem embedSilentTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) (hjc : j ≠ cap) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = 1 := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1 space, suppressing flavor, the capture tape** (spec, fill
pending — design §12; every unselected tape is accounted for, the capture
tape included). The capture tape's space usage up to time `t` is bounded
by the number of emissions recorded in that window plus one: the head
starts one past `pre ++ c.output` and advances right exactly once per
recorded emission.

**Proof sketch.** By lockstep the capture head position at time `t'` is
`|pre| + |(M.runFrom c t').output|`, which is nondecreasing in `t'` with
increments bounded by one emission per step; the visited set is therefore
the integer interval from the initial head to the final one, of
cardinality the output growth plus one
(`Turing.MultiTapeTM.output_prefix` gives the monotone growth).

**Fill appendix.** For the stated upper bound, the formal proof only
needs containment in this interval, followed by its cardinality. -/
theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t cap
      ≤ (M.runFrom c t).output.length - c.output.length + 1 := by
  have hgrowth : c.output.length ≤ (M.runFrom c t).output.length := by
    simpa using (M.output_prefix c (Nat.zero_le t)).length_le
  have hsub : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t cap ⊆
      Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    have hut : u ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
    have hlo : c.output.length ≤ (M.runFrom c u).output.length := by
      simpa using (M.output_prefix c (Nat.zero_le u)).length_le
    have hhi := (M.output_prefix c hut).length_le
    rw [embedSilentTM_runFrom ι cap hcap]
    simp only [embedSilentCfg, embedSlot_unselected ι cap hcap, ↓reduceIte,
      Finset.mem_Icc, List.length_append, Nat.cast_add]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ)).card :=
      Finset.card_le_card hsub
    _ = (M.runFrom c t).output.length - c.output.length + 1 := by
      rw [Int.card_Icc]
      simp only [List.length_append, Nat.cast_add]
      omega

/-- Applying the forwarding core commutes with configuration transport:
selected tapes update identically, the frame stays fixed, and appending
the optional emission associates with the existing output prefix. -/
private lemma embedEmit_apply (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (a : Action m Symbol S) :
    (embedActionCore ι none a).apply (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · simp [embedActionCore, embedEmitCfg, Action.apply, List.append_assoc]

/-- The forwarding host reads the same source action and executes it
completely in one step, including an emission on a halting transition. -/
private lemma embedEmit_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) :
    (embedEmitTM ι M).step (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedEmitCfg, hs]
  | some q =>
    rw [show (embedEmitCfg ι tapes heads pre c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedEmitCfg ι tapes heads pre c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedEmitCfg, embedSlot_selected]
    change (embedActionCore ι none (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedEmit_apply ι tapes heads pre c _

/-- **R1 lockstep, forwarding flavor** (design §12;
[Bon26], `rename_executes`). The transported run is the transport of the
source run, at every time and with the step count preserved exactly;
emissions are forwarded, so the host's output is `pre` followed by the
source's output at every instant (through the transport).

**Proof sketch.** As `embedSilentTM_runFrom`, with the capture clause
replaced by the output clause: the one-step commutation appends the
optional emission after `pre` (associativity of `++`, exactly as in
`emit_apply`), and `Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem embedEmitTM_runFrom (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre c) t =
      embedEmitCfg ι tapes heads pre (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step (embedEmitCfg ι tapes heads pre)
    (embedEmit_step ι M tapes heads pre) c t

/-- **R1 frame, forwarding flavor** (design §12).
Along the whole transported run, every host tape outside the selected
bank is byte-identical to its ambient frame with its head unmoved, the
input position tracks the source's, and the host's physical output is
`pre` followed by the source's output so far.

**Proof sketch.** Project `embedEmitTM_runFrom` componentwise, as in the
suppressing flavor; the output clause is the transport's definition. -/
theorem embedEmitTM_frame (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι →
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapes j = tapes j ∧
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapePos j = heads j) ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).output
      = pre ++ (M.runFrom c t).output := by
  rw [embedEmitTM_runFrom]
  refine ⟨?_, rfl, rfl⟩
  intro j hj
  simp [embedEmitCfg, embedSlot_unselected ι j hj]

/-- **R1 space, forwarding flavor, selected tapes**
(design §12). The visited set of host tape `ι i` up to time `t` is exactly
the source's visited set of tape `i`; per-tape space agrees on the nose.

**Proof sketch.** As `embedSilentTM_visitedByTapeHead`: pointwise equal
head trajectories from `embedEmitTM_runFrom`, then image and
cardinality. -/
theorem embedEmitTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (i : Fin m) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedEmitTM_runFrom]
    simp [embedEmitCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, forwarding flavor, unselected tapes** (spec, fill
pending — design §12). A host tape outside the selected bank visits
exactly the singleton of its initial head position; its space usage is
one cell.

**Proof sketch.** By `embedEmitTM_frame` the head never moves; collapse
the trajectory image to `{heads j}` and take cardinalities. -/
theorem embedEmitTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j = {heads j} ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t j = 1 := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedEmitTM_runFrom]
    simp only [embedEmitCfg, embedSlot_unselected ι j hj]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1′, the returning suppressing embedding** (round-1 repair R1). As
`Turing.embedSilentTM`, on states `S ⊕ Unit`: live source states run the
capture-flavored core, but a source action whose successor is `none` lands
in the **live return anchor** `Sum.inr ()` — the halting transition is
executed in full, its emission recorded on `cap`, before control arrives at
the anchor (the `Turing.captureAction`/`Turing.emitterRightTM` halt-to-live
discipline, exported). The anchor itself idles (stationary, silent, live),
which is exactly what a seam combinator overrides as its left exit. -/
def embedSilentRetTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S) : MultiTapeTM k Symbol (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι (some cap) a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- **R1′, the returning forwarding embedding** (round-1 repair R1). As
`Turing.embedEmitTM`, on states `S ⊕ Unit`, with source halts landing in
the live return anchor `Sum.inr ()` after the halting transition — its
forwarded emission included — has executed in full. -/
def embedEmitRetTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S) :
    MultiTapeTM k Symbol (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι none a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- Replace an action's optional successor by the live return encoding,
without changing any input, work-tape, or output effect. -/
private def embedReturnAction (a : Action k Symbol S) : Action k Symbol (S ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, a.output, some (a.state.elim (Sum.inr ()) Sum.inl)⟩

/-- Encode a closed host configuration with live left states and a live
right return anchor, preserving all four non-control fields. -/
private def embedReturnCfg (c : Cfg k Symbol S x) : Cfg k Symbol (S ⊕ Unit) x :=
  { c with state := some (c.state.elim (Sum.inr ()) Sum.inl) }

/-- At a live configuration, the return encoding is ordinary left state
mapping; at a halt it instead uses the live right anchor. -/
private lemma embedReturnCfg_live (c : Cfg k Symbol S x) (hc : c.state ≠ none) :
    embedReturnCfg c = c.mapState Sum.inl := by
  cases hs : c.state with
  | none => exact (hc hs).elim
  | some q => simp [embedReturnCfg, Cfg.mapState, hs]

/-- Direct comparison of a closed host step with a returning host step.
**Proof sketch.** At a live left state, both hosts execute the same action
and only the successor encoding differs. At a closed halt, the returning
anchor's idle action preserves every non-control field, just as absorption
does on the closed side. No property of a source embedding is needed. -/
private lemma embedReturn_step (N : MultiTapeTM k Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Symbol S x) :
    R.step (embedReturnCfg c) = embedReturnCfg (N.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedReturnCfg, hs, hidle, Action.apply]
  | some q =>
    rw [show (embedReturnCfg c).state = some (Sum.inl q) by
      simp [embedReturnCfg, hs]]
    dsimp only
    have hin : (embedReturnCfg c).inputSymbol = c.inputSymbol := rfl
    have hw : (embedReturnCfg c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [hin, hw, hleft]
    rfl

/-- The silent returning step executes the entire transported source
action, then encodes its successor as a live left state or return anchor. -/
private lemma embedSilentRet_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (hc : c.state ≠ none) :
    (embedSilentRetTM ι cap M).step
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) =
      embedReturnCfg (embedSilentCfg ι cap tapes heads pre out₀ (M.step c)) := by
  have h := embedReturn_step (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c)
  rw [embedReturnCfg_live (embedSilentCfg ι cap tapes heads pre out₀ c) hc,
    embedSilent_step] at h
  exact h

/-- A live-step transport reaches the return anchor exactly at a positive
first halt, with all transported data intact.
**Proof sketch.** The initially live state and terminal halt imply positive
time. Induct over the strict live prefix, where the successor encoding is
ordinary left mapping. Execute the step from the last live configuration
separately; its halted successor encodes the return anchor. Earlier states
are left constructors, so none is the right anchor. -/
private lemma embedThroughHalt (M : MultiTapeTM m Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (E : Cfg m Symbol S x → Cfg k Symbol S x)
    (hstate : ∀ d, (E d).state = d.state)
    (hstep : ∀ d, d.state ≠ none →
      R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d)))
    (c : Cfg m Symbol S x) (T : ℕ) (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl) ∧
    R.runFrom ((E c).mapState Sum.inl) T =
      { E (M.runFrom c T) with state := some (Sum.inr ()) } ∧
    ∀ t < T, (R.runFrom ((E c).mapState Sum.inl) t).state ≠
      some (Sum.inr ()) := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    subst T
    exact hc (by simpa using hhalt)
  have hrun : ∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        hstep _ (hlive t (by omega)), ← MultiTapeTM.runFrom_succ_eq_step']
      apply embedReturnCfg_live
      rw [hstate]
      exact hlive _ ht
  refine ⟨hrun, ?_, ?_⟩
  · have hlast : T - 1 + 1 = T := by omega
    calc
      R.runFrom ((E c).mapState Sum.inl) T =
          R.step (R.runFrom ((E c).mapState Sum.inl) (T - 1)) :=
        (congrArg (R.runFrom ((E c).mapState Sum.inl)) hlast).symm.trans
          MultiTapeTM.runFrom_succ_eq_step'
      _ = embedReturnCfg (E (M.runFrom c T)) := by
        rw [hrun _ (by omega), hstep _ (hlive _ (by omega)),
          ← MultiTapeTM.runFrom_succ_eq_step', hlast]
      _ = _ := by simp [embedReturnCfg, hstate, hhalt]
  · intro t ht
    rw [hrun t ht]
    simp only [Cfg.mapState, hstate]
    cases (M.runFrom c t).state <;> simp

/-- **R1′ through-halt contract, suppressing flavor**
(round-1 repair R1): if the source first halts at time `T`, the returning
embedding runs in `Sum.inl`-lockstep through every live time and, at `T`,
sits at the **live return anchor** over the completed transport — the
halting transition's emission recorded on `cap`, the source tape residue
preserved on the selected bank, the frame untouched — having visited the
anchor first exactly there. The start must be **live** (`hc` — round-2
blocker: an initially halted `c` at `T = 0` satisfies the other hypotheses
vacuously while the handover state projection would demand
`none = some (Sum.inr ())`; under `hlive` **and** `hhalt` together, `hc` is
equivalent to `0 < T` — the forward direction uses `hhalt`, the reverse
`hlive 0` (round-3 finding 1 sharpened the earlier `hhalt`-only phrasing).
The smallest case is the round-1 counterexample cured: a one-state source
that emits and halts on its first transition lands at time `1` in
`Sum.inr ()` with `pre ++ [b]` on the capture tape (the audit's S8 check).

**Proof sketch.** Live times: the `Sum.inl` branch applies the very core of
`Turing.embedSilentTM`, so `embedSilentTM_runFrom`'s one-step commutation
transports verbatim under `Cfg.mapState Sum.inl` (`Cfg.mapState_apply`).
At the halting step, the source action's tape and capture effects are those
of the closed flavor — `Turing.FinTM.bufferTape_append` records the final
emission — while the successor `Option.elim` lands in `Sum.inr ()` instead
of `none`; the anchor cannot occur earlier because live source states map
into `Sum.inl`. Fill obligations, named: the two `Option.elim` successor
equations; the through-halt step case; the first-visit projection. -/
theorem embedSilentRetTM_run (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t =
        (embedSilentCfg ι cap tapes heads pre out₀
          (M.runFrom c t)).mapState Sum.inl) ∧
    (embedSilentRetTM ι cap M).runFrom
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) T =
      { embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl)
          t).state ≠ some (Sum.inr ()) := by
  exact embedThroughHalt M (embedSilentRetTM ι cap M)
    (embedSilentCfg ι cap tapes heads pre out₀) (fun _ => rfl)
    (embedSilentRet_step ι cap M tapes heads pre out₀) c T hc hlive hhalt

/-- The forwarding returning step preserves the complete source action,
including its final emission, and changes only the successor encoding. -/
private lemma embedEmitRet_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (hc : c.state ≠ none) :
    (embedEmitRetTM ι M).step ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) =
      embedReturnCfg (embedEmitCfg ι tapes heads pre (M.step c)) := by
  have h := embedReturn_step (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c)
  rw [embedReturnCfg_live (embedEmitCfg ι tapes heads pre c) hc, embedEmit_step] at h
  exact h

/-- **R1′ through-halt contract, forwarding flavor**
(round-1 repair R1): as `Turing.embedSilentRetTM_run` with the final
emission forwarded to the physical output (`pre ++ (M.runFrom c T).output`
at the anchor).

**Proof sketch.** As `embedSilentRetTM_run`, with the forwarding core: live
times transport under `Cfg.mapState Sum.inl` by `embedEmitTM_runFrom`'s
one-step commutation, the halting step applies the closed forwarding core's
tape and output effects (the final emission appended to the physical
output) with the successor `Option.elim` landing in `Sum.inr ()`, and the
first-visit clause projects from the `Sum.inl` lockstep. Fill obligations,
named: the successor equations; the through-halt step case; the
first-visit projection. -/
theorem embedEmitRetTM_run (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t =
        (embedEmitCfg ι tapes heads pre (M.runFrom c t)).mapState Sum.inl) ∧
    (embedEmitRetTM ι M).runFrom
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) T =
      { embedEmitCfg ι tapes heads pre (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t).state ≠
        some (Sum.inr ()) := by
  exact embedThroughHalt M (embedEmitRetTM ι M)
    (embedEmitCfg ι tapes heads pre) (fun _ => rfl)
    (embedEmitRet_step ι M tapes heads pre) c T hc hlive hhalt

/-- Direct host comparison preserves every visited-head set, from any
initial configuration and for every finite horizon.
**Proof sketch.** Initially halted configurations stay halted on both
sides. From a live start, iterate the direct step comparison under the
return encoding, whose head positions are unchanged. Equality of the
head trajectories gives equality of their finite images. This uses no
termination hypothesis, source simulation, or capture-tape separation. -/
private lemma embedReturn_visited (N : MultiTapeTM k Symbol S)
    (R : MultiTapeTM k Symbol (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Symbol S x) (t : ℕ) (j : Fin k) :
    R.visitedByTapeHead (c.mapState Sum.inl) t j = N.visitedByTapeHead c t j := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  by_cases hc : c.state = none
  · rw [R.runFrom_of_halt _ (by simp [Cfg.mapState, hc]), N.runFrom_of_halt _ hc]
    rfl
  · have hrun := MultiTapeTM.runFrom_comm_of_step embedReturnCfg
      (embedReturn_step N R hleft hidle) c u
    rw [embedReturnCfg_live c hc] at hrun
    exact congrArg (fun d => d.workTapePos j) hrun

/-- **R1′ space, suppressing flavor** (round-1 repair
R1): at every time and on every tape, the returning embedding's visited set
from the `Sum.inl`-mapped seam equals the closed embedding's from the plain
seam — the trajectories coincide through the halt, and afterwards one idles
at the live anchor while the other sits halted, both stationary.

**Proof sketch.** For `t` up to the first source halt, both machines apply
identical tape actions (`embedSilentRetTM_run`'s lockstep and the halting
step's shared core); beyond it, the anchor's idle action and the halted
absorption are both stationary, freezing both visited sets.

**Fill appendix.** The direct host comparison `embedReturn_visited`
handles initially halted and live starts separately. It uses neither
through-halt contract nor a capture-separation hypothesis. -/
theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (j : Fin k) :
    (embedSilentRetTM ι cap M).visitedByTapeHead
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t j =
      (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j := by
  exact embedReturn_visited (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c) t j

/-- **R1′ space, forwarding flavor** (round-1 repair
R1): the forwarding analogue of
`Turing.embedSilentRetTM_visitedByTapeHead`.

**Proof sketch.** As the suppressing flavor: identical tape actions through
the first source halt, then the live idle and the halted absorption are
both stationary, freezing both visited sets — the trajectories coincide at
every time. -/
theorem embedEmitRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Symbol S)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (t : ℕ) (j : Fin k) :
    (embedEmitRetTM ι M).visitedByTapeHead
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t j =
      (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j := by
  exact embedReturn_visited (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c) t j


/-! ### Selected-tape exports (§13 Z1 rider, decision D-R1)

The retrofit inventories (`audits/retrofit-inventory/`) found, three times
independently, that no old-code R1 consumer can be proved from this file's
public surface: the frame lemmas cover only unselected tapes, and
`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports; `Turing.embedSilentCfg_cap`, after
them, exports the silent transport's capture field (the C1-A assembly gate, finding M1). They are
skeleton-time proofs (statement-phase additions flagged for the A-S1
audit): each is definitional at `embedSlot_selected`. -/

/-- The silent transport holds the source's tape `i` on host tape `ι i`. -/
theorem embedSilentCfg_selected_tape (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes (ι i) =
      c.workTapes i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The silent transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedSilentCfg_selected_pos (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =
      c.workTapePos i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape `i` on host tape
`ι i`. -/
theorem embedEmitCfg_selected_tape (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapes (ι i) = c.workTapes i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedEmitCfg_selected_pos (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre : List Symbol) (c : Cfg m Symbol S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapePos (ι i) = c.workTapePos i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- **The silent transport's capture tape.** If the capture tape `cap` lies outside the selection
`ι`, the transported configuration `Turing.embedSilentCfg ι cap tapes heads pre out₀ c` holds the
recorded word `pre ++ c.output` on `cap`, and that tape's head sits just after it, at
`|pre ++ c.output|`, for every frame, prefix, physical output and source configuration. It is the
capture-field companion of the selected-tape exports, so that consumers need not unfold the
transport's private slot search (the C1-A assembly gate, finding M1). (Technical glue.)

**Proof sketch.** Off the selection the slot search finds no source tape
(`embedSlot_unselected`), so both fields are the capture branch of the transport's
definition. -/
theorem embedSilentCfg_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes cap =
        FinTM.bufferTape (pre ++ c.output) ∧
      (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos cap =
        ((pre ++ c.output).length : ℤ) := by
  simp [embedSilentCfg, embedSlot_unselected ι cap hcap]

/-- **The silent transport's frame** (the specification API, user 2026-10-16): a host tape
outside the selection `ι`, other than the capture tape, holds the ambient frame `tapes j` with
its head at `heads j`. The frame companion of `Turing.embedSilentCfg_cap`.

**Proof sketch.** Off the selection the slot search finds no source tape
(`embedSlot_unselected`), and `j ≠ cap` selects the frame branch. -/
theorem embedSilentCfg_unselected (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Symbol) (heads : Fin k → ℤ)
    (pre out₀ : List Symbol) (c : Cfg m Symbol S x) (j : Fin k) (hj : j ∉ Set.range ι)
    (hcap : j ≠ cap) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes j = tapes j ∧
      (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos j = heads j := by
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hcap]

/-! The specification API (user, 2026-10-16): the two transports' state, input position and
output as equations, without the `simp` attribute. -/
attribute [simps (config := { isSimp := false }) state inputPos output] embedSilentCfg embedEmitCfg


end Turing

namespace Turing

variable {k : ℕ} {Γ : Type*}

/-! ## Reconstruction of embedded configurations (MIG-0b)

The frame export missing beside `Turing.embedEmitCfg_selected_tape` and `_pos`, the selection of
a host configuration, and the **R1 reconstruction lemma** (the wave-1 fill gate's major F1,
acknowledged by the user; backlog F6-1(i), F7-1(b)), with its relabelling and word-layout
corollaries. The first three moved here from `Build/Contract.lean` at MIG-0b's layering split.
All are stated over any universes, like the rest of `Build/Embed`: MIG-0a stated its three over
`Type`, which are instances (the generalization changes nothing else in their statements), so
that the lemma can replace every member of the family at its own signature (`RecordTable`'s
`rt_embed_matches` is stated over `Type*`). -/

/-- The forwarding embedding keeps an unselected tape and head as its frame: the export missing
from `Build/Embed.lean` beside `Turing.embedEmitCfg_selected_tape` and `_pos`. It moved to
`Build/Embed` from `Build/Contract.lean` at MIG-0b's layering split.

**Proof sketch.** At time `0`, `Turing.embedEmitTM_frame` for a one-state machine says exactly
this; the transport's tape fields do not depend on the state type. -/
theorem embedEmitCfg_unselected {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ) (c : Cfg m Γ S x)
    (j : Fin k) (hj : j ∉ Set.range σ) :
    (embedEmitCfg σ tapes heads pre c).workTapes j = tapes j ∧
      (embedEmitCfg σ tapes heads pre c).workTapePos j = heads j := by
  let M0 : MultiTapeTM m Γ Unit := ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩
  let c0 : Cfg m Γ Unit x := ⟨none, c.inputPos, c.workTapes, c.workTapePos, c.output⟩
  have h := (embedEmitTM_frame σ M0 tapes heads pre c0 0).1 j hj
  simp only [MultiTapeTM.runFrom_zero] at h
  exact h

/-- The source configuration seen through an R1 selection: selected tapes and heads, the same
state and input position, and an **empty output**. The selection empties the source output, so
a source precondition is always tested on the output `[]`: `Turing.Contract.embed` transports
output-normalized preconditions only. -/
def Cfg.select {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (d : Cfg k Γ S x) : Cfg m Γ S x :=
  ⟨d.state, d.inputPos, fun i => d.workTapes (σ i), fun i => d.workTapePos (σ i), []⟩

/-- **The R1 reconstruction lemma** (MIG-0b; backlog F6-1(i), F7-1(b)): an embedded
configuration is determined by its selected bank and its ambient frame. If `d` has the state,
input position and selected tapes and heads of `c`, its output is `pre` followed by `c`'s, and
off the selection it holds the frame `tapes`, `heads`, then `d` is the forwarding embedding of `c`
into that frame. At their migrations it replaces `OracleSim.oracleBankCfg_eq`,
`CodeSimulator.canonEmbedEq`, `Primitives.emitterP2_frame` and the local `hframe` of
`Loop.emCall_exit_fixed` (the MIG-0b fit tests derive each in one term).

**Proof sketch.** Compare field by field. A selected tape or head is the source's
(`Turing.embedEmitCfg_selected_tape`, `_pos`), which is `d`'s by hypothesis; an unselected one is
the frame (`Turing.embedEmitCfg_unselected`), which is `d`'s by hypothesis. The state, the input
position and the output are the hypotheses. -/
theorem embedEmitCfg_eq {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ) (c : Cfg m Γ S x)
    (d : Cfg k Γ S x) (hs : c.state = d.state) (hin : c.inputPos = d.inputPos)
    (hout : pre ++ c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (σ i) ∧ c.workTapePos i = d.workTapePos (σ i))
    (outside : ∀ j, j ∉ Set.range σ → tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    embedEmitCfg σ tapes heads pre c = d := by
  have fields (j : Fin k) :
      (embedEmitCfg σ tapes heads pre c).workTapes j = d.workTapes j ∧
        (embedEmitCfg σ tapes heads pre c).workTapePos j = d.workTapePos j := by
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨i, rfl⟩ := hj
      rw [embedEmitCfg_selected_tape, embedEmitCfg_selected_pos]
      exact selected i
    · obtain ⟨ht, hp⟩ := embedEmitCfg_unselected σ tapes heads pre c j hj
      exact ⟨ht.trans (outside j hj).1, hp.trans (outside j hj).2⟩
  exact Cfg.ext hs hin (funext fun j => (fields j).1) (funext fun j => (fields j).2) hout

/-- **R1 reconstruction with state relabelling**: as `Turing.embedEmitCfg_eq`, for a host whose
control is the source's relabelled by `f` (the phase-host and call-controller tags). This is the
shape of `Primitives.emitterP2_frame` and of `Loop.emCall_exit_fixed`'s `hframe`.

**Proof sketch.** Relabelling the embedded configuration is embedding the relabelled source, by
definition; apply `Turing.embedEmitCfg_eq` to it. -/
theorem embedEmitCfg_mapState_eq {m : ℕ} {S H : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (f : S → H) (tapes : Fin k → ℤ → Option Γ) (heads : Fin k → ℤ) (pre : List Γ)
    (c : Cfg m Γ S x) (d : Cfg k Γ H x) (hs : c.state.map f = d.state)
    (hin : c.inputPos = d.inputPos) (hout : pre ++ c.output = d.output)
    (selected : ∀ i, c.workTapes i = d.workTapes (σ i) ∧ c.workTapePos i = d.workTapePos (σ i))
    (outside : ∀ j, j ∉ Set.range σ → tapes j = d.workTapes j ∧ heads j = d.workTapePos j) :
    (embedEmitCfg σ tapes heads pre c).mapState f = d :=
  embedEmitCfg_eq σ tapes heads pre (c.mapState f) d hs hin hout selected outside

/-- **R1 reconstruction, word layout**: embedding a word seam into a word frame gives the word
seam of the combined layout, when the target's selected words are the source's and its other words
the frame's. This is the shape of `CodeSimulator.canonEmbedWords` and `CertShell.cert_embed_words`
(`Build/Embed` imports `Build/Convention`, where `Turing.Cfg.ofWords` lives, for it).

**Proof sketch.** `Turing.embedEmitCfg_eq`: the selected tapes are the source buffers, the other
tapes the frame buffers, and every head is at the origin. -/
theorem embedEmitCfg_ofWords_eq {m : ℕ} {S : Type*} {x : List Bool} (σ : Fin m ↪ Fin k) (q : S)
    (v : Fin m → List Bool) (frame target : Fin k → List Bool)
    (selected : ∀ i, target (σ i) = v i)
    (outside : ∀ j, j ∉ Set.range σ → frame j = target j) :
    embedEmitCfg σ (fun j => FinTM.bufferTape (frame j)) (fun _ => 0) []
        (Cfg.ofWords (input := x) q v) = Cfg.ofWords q target :=
  embedEmitCfg_eq σ _ _ [] _ _ rfl rfl rfl
    (fun i => ⟨congrArg FinTM.bufferTape (selected i).symm, rfl⟩)
    (fun j hj => ⟨congrArg FinTM.bufferTape (outside j hj), rfl⟩)

/-- Every host configuration is the forwarding embedding of its selection, framed by itself:
embedding the selection of `d` into `d`'s own tapes, heads and output gives back `d`.

**Proof sketch.** The R1 reconstruction lemma (`Turing.embedEmitCfg_eq`) at `d`'s own tapes,
heads and output: the selection keeps the state, the input position and the selected tapes and
heads, its empty output follows `d`'s, and off the selection the frame is `d`'s own. -/
theorem embedEmitCfg_select {m : ℕ} {S : Type*} {x : List Γ} (σ : Fin m ↪ Fin k)
    (d : Cfg k Γ S x) :
    embedEmitCfg σ d.workTapes d.workTapePos d.output (d.select σ) = d :=
  embedEmitCfg_eq σ _ _ _ _ d rfl rfl (List.append_nil _) (fun _ => ⟨rfl, rfl⟩)
    (fun _ _ => ⟨rfl, rfl⟩)

end Turing
```

## ===== TCSlib/Complexity/SpaceComplexity/Constructible.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Build.InputLength
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.SpaceComplexity.Machines.Bin
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.TuringMachine.Build.WordTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-constructible functions

[AB09, §4.1, p. 79]: `S : ℕ → ℕ` is space-constructible when some machine
computes `S(|x|)` from `x` within `O(S(|x|))` space, and the book's standing
convention is `S(n) > log n`. The definition mirrors
`Complexity.TimeConstructible` — output in binary (`Nat.bits`), constant slack
`c · S n`, which implements the book's own asymptotic space convention
([AB09, p. 79]: "computes `S(|x|)` in `O(S(|x|))` space"); an exact-space
variant is not posed here (the exact-**time** refutation of chapter 1 does not
transfer: a space deadline forces no premature halt) — and carries the book's
convention as the conjunct `∀ n, logSpace n ≤ S n`, so that downstream
statements (the space hierarchy, Savitch) can draw on it without restating it;
results needing only weaker hypotheses must say so.

## Main definitions

* `Complexity.SpaceConstructible` — the binary-output, constant-slack,
  above-log form. [AB09, §4.1, p. 79]

## Main results (proved)

* `Complexity.spaceConstructible_iff` — the definition as an equivalence.
* `Complexity.spaceConstructible_logSpace` — `log` is space-constructible.
* `Complexity.spaceConstructible_linear` — `n + 1` is space-constructible.
* `Complexity.spaceConstructible_poly` — `n ^ c + 1` is space-constructible for `c ≥ 1`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, p. 79.)
-/

namespace Complexity

open Turing

/-- A function `S` is **space-constructible** when it dominates the logarithm
(`Complexity.logSpace`, the book's standing `S(n) > log n` convention carried as
data) and some machine computes the binary representation of `S (|x|)` from `x`
within `c · S (|x|)` visited work-tape cells. Mirrors
`Complexity.TimeConstructible` (binary output via `Nat.bits`, constant slack).
[AB09, §4.1, p. 79] -/
def SpaceConstructible (S : ℕ → ℕ) : Prop :=
  (∀ n, logSpace n ≤ S n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
    M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n

/-- **Space constructibility, unfolded**: `S` is space constructible exactly when
`logSpace n ≤ S n` for every `n` and, for some constant `c > 0`, some machine computes
`x ↦ (S |x|).bits` in space `c · S` (`Turing.FinTM.ComputesInSpace`). -/
theorem spaceConstructible_iff (S : ℕ → ℕ) :
    SpaceConstructible S ↔
      (∀ n, logSpace n ≤ S n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
        M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n :=
  Iff.rfl

/-- Positive binary words have exactly the normalized logarithmic width. -/
private lemma b3a_bits_length {n : ℕ} (hn : n ≠ 0) :
    n.bits.length = logSpace n :=
  (LogProg.length_bits_eq_log hn).trans (logSpace_eq n).symm

/-- The counter word with its first cell overwritten by `true`. -/
private def b3a_word (n : ℕ) : List Bool := true :: n.bits.tail

/-- The overwrite handles zero while preserving every positive counter width. -/
private lemma b3a_word_length (n : ℕ) : (b3a_word n).length = logSpace n := by
  by_cases hn : n = 0
  · subst n
    simp [b3a_word, logSpace, Nat.bits]
  · simp only [b3a_word, List.length_cons, List.length_tail, b3a_bits_length hn]
    unfold logSpace
    omega

/-- Restricting a buffer to its occupied nonnegative interval does not change it. -/
private lemma b3a_buffer_restrict (w : List Bool) (z : ℤ) :
    (if 0 ≤ z ∧ z < (w.length : ℤ) then FinTM.bufferTape w z else none) =
      FinTM.bufferTape w z := by
  by_cases hzero : 0 ≤ z
  · by_cases hlast : z < (w.length : ℤ)
    · simp [hzero, hlast]
    · have out : w.length ≤ z.toNat := by omega
      simp [hzero, hlast, FinTM.bufferTape]
  · simp [hzero, FinTM.bufferTape]

/-- Setting the first buffered cell yields `true :: tail`, including an empty buffer. -/
private lemma b3a_buffer_overwrite (w : List Bool) (z : ℤ) :
    (if z = 0 then some true else FinTM.bufferTape w z) =
      FinTM.bufferTape (true :: w.tail) z := by
  by_cases hz : z = 0
  · subst z
    simp [FinTM.bufferTape]
  · by_cases hp : 0 ≤ z
    · have ht : z.toNat ≠ 0 := by omega
      simp only [if_neg hz, FinTM.bufferTape, if_pos hp, List.getElem?_cons,
        if_neg ht, List.getElem?_tail]
      congr 1
      omega
    · simp [hz, FinTM.bufferTape, hp]

/-- A live phase seam: its word is on tape zero and all heads are at the origin. -/
private def b3a_cfg {k : ℕ} [NeZero k] {S : Type} (s : S)
    (x w : List Bool) : Cfg k Bool S x :=
  { Cfg.init s x with
    workTapes := fun j => if j = 0 then FinTM.bufferTape w else fun _ => none }

/-- Map only the control field of a canonical phase seam. -/
private lemma b3a_cfg_map {k : ℕ} [NeZero k] {S T : Type} (f : S → T)
    (s : S) (x w : List Bool) :
    (b3a_cfg (k := k) s x w).mapState f = b3a_cfg (f s) x w := rfl

/-- Relocate a single-buffer seam along a selection preserving tape zero.
**Proof sketch.** Selected tapes use the public configuration projections;
other tapes use the frame theorem at time zero. All unused cells and heads are blank. -/
private lemma b3a_embed_cfg {m k : ℕ} [NeZero m] [NeZero k] {S : Type}
    (R : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k) (hzero : ι 0 = 0)
    (s : S) (x w : List Bool) :
    embedEmitCfg ι (fun _ _ => none) (fun _ => 0) [] (b3a_cfg s x w) =
      b3a_cfg (k := k) s x w := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases chosen : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := chosen
      rw [embedEmitCfg_selected_tape]
      have hz : ι i = 0 ↔ i = 0 := by rw [← hzero, ι.injective.eq_iff]
      simp only [b3a_cfg, hz]
    · have frame := (embedEmitTM_frame ι R (fun _ _ => none) (fun _ => 0)
        [] (b3a_cfg s x w) 0).1 j chosen
      have hj : j ≠ 0 := fun eq => chosen ⟨0, hzero.trans eq.symm⟩
      simpa [b3a_cfg, hj] using frame.1
  · funext j
    by_cases chosen : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := chosen
      rw [embedEmitCfg_selected_pos]
      rfl
    · exact (embedEmitTM_frame ι R (fun _ _ => none) (fun _ => 0)
        [] (b3a_cfg s x w) 0).1 j chosen |>.2
  · rfl

/-- A coarse constant-factor space bound for tape relocation.
**Proof sketch.** Every selected tape is bounded by the source's total space;
each unused tape contributes one cell. Sum this common bound over the host bank. -/
private lemma b3a_embed_space {m k : ℕ} {S : Type} {x : List Bool}
    (R : MultiTapeTM m Bool S) (ι : Fin m ↪ Fin k)
    (d : Cfg m Bool S x) (t : ℕ) :
    (embedEmitTM ι R).spaceUsed
        (embedEmitCfg ι (fun _ _ => none) (fun _ => 0) [] d) t ≤
      k * (R.spaceUsed d t + 1) := by
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _j : Fin k, (R.spaceUsed d t + 1) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases chosen : j ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := chosen
        rw [(embedEmitTM_visitedByTapeHead ι R (fun _ _ => none) (fun _ => 0) [] d t i).2]
        exact (R.spaceUsedByTape_le_spaceUsed d t i).trans (Nat.le_succ _)
      · rw [(embedEmitTM_visitedByTapeHead_frame ι R (fun _ _ => none)
          (fun _ => 0) [] d t j chosen).2]
        omega
    _ = _ := by simp [MultiTapeTM.spaceUsed]

/-- The additive space ledger for an arbitrary live-exit seam: the general seam space lemma
`Turing.seamCompTM_spaceUsed_le_add_ofCfg`, with this file's argument names. -/
private lemma b3a_seam_space {k : ℕ} {S T : Type} [DecidableEq S] {x : List Bool}
    (R : MultiTapeTM k Bool S) (exit : S) (Q : MultiTapeTM k Bool T) (entry : T)
    {d e : Cfg k Bool S x} {a b : ℕ} (run : R.runFrom d a = e)
    (live : e.state = some exit) (cut : ∀ u < a, (R.runFrom d u).state ≠ some exit) :
    (seamCompTM R exit Q entry).spaceUsed (d.mapState Sum.inl) (a + 1 + b) ≤
      R.spaceUsed d a + Q.spaceUsed (e.mapState fun _ => entry) b :=
  seamCompTM_spaceUsed_le_add_ofCfg R exit Q entry run live cut

/-- The public native counter, specialized to blank origin tapes with a cardinality ledger.
**Proof sketch.** Instantiate R8.5c at its entry, identify the globally blank frame
with the buffer layout, and enclose each head's visited set in the promised interval.
The first-exit clause is retained for the subsequent dispatch. -/
private theorem b3a_counter :
    ∃ (K : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (R : MultiTapeTM (K + 1) Bool S) (entry exit : S) (B : ℕ),
      ∀ x : List Bool, ∃ t,
        R.runFrom (b3a_cfg entry x []) t = b3a_cfg exit x x.length.bits ∧
        (∀ u < t, (R.runFrom (b3a_cfg entry x []) u).state ≠ some exit) ∧
        R.spaceUsed (b3a_cfg entry x []) t ≤ B * (x.length.bits.length + 1) := by
  obtain ⟨K, S, fs, ds, R, entry, exit, C, contract⟩ := exists_inputLengthTM
  letI := fs
  letI := ds
  refine ⟨K, S, fs, ds, R, entry, exit, (K + 1) * (2 * C + 1), ?_⟩
  intro x
  obtain ⟨t, _, cut, heads, finished⟩ := contract (b3a_cfg entry x []) rfl rfl
    (by intros; simp [b3a_cfg]) (by intros; simp [b3a_cfg])
  refine ⟨t, ?_, cut, ?_⟩
  · rw [finished]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      by_cases hj : j = 0
      · simp [b3a_cfg, hj, b3a_buffer_restrict]
      · simp [b3a_cfg, hj]
    · rfl
    · rfl
  · have perTape (j : Fin (K + 1)) : R.spaceUsedByTape (b3a_cfg entry x []) t j ≤
        2 * (C * (x.length.bits.length + 1)) + 1 := by
      calc
        _ ≤ (Finset.Icc (-((C * (x.length.bits.length + 1) : ℕ) : ℤ))
            ((C * (x.length.bits.length + 1) : ℕ) : ℤ)).card := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
          have bound := heads u (Nat.le_of_lt_succ (Finset.mem_range.mp hu)) j
          simpa [b3a_cfg, Finset.mem_Icc, abs_le] using bound
        _ = _ := by rw [Int.card_Icc]; omega
    calc
      _ ≤ ∑ _j : Fin (K + 1), (2 * (C * (x.length.bits.length + 1)) + 1) :=
        Finset.sum_le_sum fun j _ => perTape j
      _ = (K + 1) * (2 * (C * (x.length.bits.length + 1)) + 1) := by simp
      _ ≤ (K + 1) * ((2 * C + 1) * (x.length.bits.length + 1)) := by
        apply Nat.mul_le_mul_left
        ring_nf; omega
      _ = _ := by ring

/-- The public constant writer overwrites cell zero and returns to its origin.
**Proof sketch.** Use R8.4 with `[true]`. Its four-step trace supplies the exact
exit cut and two-cell head interval; the buffer update is the tail identity above. -/
private theorem b3a_overwrite (x w : List Bool) :
    (writeConstTM 1 0 [true]).runFrom (b3a_cfg (.wr 0) x w) 4 =
        b3a_cfg .done x (true :: w.tail) ∧
      (∀ u < 4, ((writeConstTM 1 0 [true]).runFrom
        (b3a_cfg (.wr 0) x w) u).state ≠ some .done) ∧
      (writeConstTM 1 0 [true]).spaceUsed (b3a_cfg (.wr 0) x w) 4 ≤ 2 := by
  obtain ⟨run, cut, heads⟩ := writeConstTM_run_ofCfg (0 : Fin 1) [true]
    (b3a_cfg (.wr 0) x w) rfl
  norm_num only [List.length_singleton] at run
  refine ⟨?_, cut, ?_⟩
  · rw [run]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      have hj : j = 0 := Subsingleton.elim _ _
      simp only [b3a_cfg, Cfg.init, hj, if_pos, List.length_singleton,
        zero_add, sub_zero]
      simp only [true_and, show (0 ≤ z ∧ z < 1) ↔ z = 0 by omega]
      by_cases hz : z = 0
      · simp [hz, FinTM.bufferTape]
      · simpa [hz] using b3a_buffer_overwrite w z
    · rfl
    · rfl
  · change ∑ j : Fin 1, _ ≤ 2
    rw [Fintype.sum_subsingleton _ (0 : Fin 1)]
    calc
      _ ≤ (Finset.Icc (0 : ℤ) 1).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        simpa [b3a_cfg] using heads 0 u (Nat.le_of_lt_succ (Finset.mem_range.mp hu))
      _ = 2 := by decide

/-- The emitting phase shares tape zero and places its bank after the native counter bank. -/
private def b3a_virtualSelect (K m : ℕ) : Fin (1 + m) ↪ Fin (K + 1 + m) where
  toFun i := ⟨if i.val = 0 then 0 else K + i.val, by split_ifs <;> omega⟩
  inj' := by
    intro i j eq
    apply Fin.ext
    have vals := congrArg Fin.val eq
    dsimp at vals
    split_ifs at vals <;> omega

/-- The initial virtual-input layout is the single-buffer phase seam.
**Proof sketch.** Split the host tapes into its buffer and source bank. The source
starts at input position one, with blank work tapes and all heads at zero. -/
private lemma b3a_virtual_cfg (L : FinTM Bool) (x y : List Bool) :
    vhostCfg (L.tm.initCfg y) true (1 : Fin (x.length + 2)) [] =
      b3a_cfg (L.tm.q₀, true) x y := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have zero : Fin.castAdd L.k (0 : Fin 1) = 0 := rfl
      change FinTM.bufferTape y z =
        (if Fin.castAdd L.k (0 : Fin 1) = 0 then FinTM.bufferTape y else fun _ => none) z
      rw [if_pos zero]
    · have nonzero : Fin.natAdd 1 i ≠ (0 : Fin (1 + L.k)) := by
        intro eq
        have vals := congrArg Fin.val eq
        simp only [Fin.coe_natAdd, Fin.val_zero] at vals
        omega
      simp only [vhostCfg, Fin.addCases_right, b3a_cfg, if_neg nonzero,
        MultiTapeTM.initCfg, Cfg.init]
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [vhostCfg, b3a_cfg, MultiTapeTM.initCfg, Cfg.init]
    · simp [vhostCfg, b3a_cfg, MultiTapeTM.initCfg, Cfg.init]
  · rfl

/-- Assemble the three public phases with an explicit boundary-inclusive space allowance.
**Proof sketch.** Count on a native bank, overwrite its first cell, then host the
length counter on that word. Both seams dispatch at their first exits. The public
relocation and seam ledgers bound total space by a fixed multiple of the normalized
logarithm plus one; the final virtual-input halt emits the full binary answer. -/
private theorem b3a_log_machine :
    ∃ (A : ℕ), 0 < A ∧ ∃ M : FinTM Bool,
      M.ComputesInSpace (fun x => (logSpace x.length).bits)
        (fun n => A * (logSpace n + 1)) := by
  obtain ⟨K, S, fs, ds, R, entry, exit, B, counter⟩ := b3a_counter
  letI := fs
  letI := ds
  obtain ⟨L, b, computes, space⟩ := FinTM.computesFunInTime_lengthBits_spaceUsed
  let k := K + 1 + L.k
  let ic : Fin (K + 1) ↪ Fin k := Fin.castAddEmb L.k
  let iw : Fin 1 ↪ Fin k := Fin.castLEEmb (by dsimp [k]; omega)
  let iv := b3a_virtualSelect K L.k
  have ic0 : ic 0 = 0 := rfl
  have iw0 : iw 0 = 0 := rfl
  have iv0 : iv 0 = 0 := by apply Fin.ext; simp [iv, b3a_virtualSelect]
  let C := embedEmitTM ic R
  let W := embedEmitTM iw (writeConstTM 1 0 [true])
  let E := embedEmitTM iv (vhostEmitTM L.tm)
  let CW := seamCompTM C exit W (.wr 0)
  let H := seamCompTM CW (Sum.inr .done) E (L.tm.q₀, true)
  let M : FinTM Bool :=
    { k := k
      State := (S ⊕ WritePhase 1) ⊕ (L.State × Bool)
      tm := {H with q₀ := Sum.inl (Sum.inl entry)} }
  refine ⟨k * (B + b + 8) + 1, by omega, M, ?_⟩
  intro x
  let y := b3a_word x.length
  obtain ⟨t, counted, countCut, countSpace⟩ := counter x
  obtain ⟨written, writeCut, writeSpace⟩ := b3a_overwrite x x.length.bits
  -- Count and overwrite share the buffer; their first-exit cuts justify both dispatches.
  have countRun : C.runFrom (b3a_cfg entry x []) t =
      b3a_cfg exit x x.length.bits := by
    rw [← b3a_embed_cfg R ic ic0 entry x [], embedEmitTM_runFrom, counted,
      b3a_embed_cfg R ic ic0]
  have countFirst : ∀ u < t, (C.runFrom (b3a_cfg entry x []) u).state ≠ some exit := by
    intro u hu
    rw [← b3a_embed_cfg R ic ic0 entry x [], embedEmitTM_runFrom]
    exact countCut u hu
  have writeRun : W.runFrom (b3a_cfg (.wr 0) x x.length.bits) 4 =
      b3a_cfg .done x y := by
    rw [← b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0 (.wr 0) x x.length.bits,
      embedEmitTM_runFrom, written, b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0]
    rfl
  have writeFirst : ∀ u < 4,
      (W.runFrom (b3a_cfg (.wr 0) x x.length.bits) u).state ≠ some .done := by
    intro u hu
    rw [← b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0 (.wr 0) x x.length.bits,
      embedEmitTM_runFrom]
    exact writeCut u hu
  have cwRun : CW.runFrom (b3a_cfg (Sum.inl entry) x []) (t + 1 + 4) =
      b3a_cfg (Sum.inr .done) x y := by
    simpa only [b3a_cfg_map] using seamCompTM_run_ofCfg C exit W (.wr 0)
      countRun rfl countFirst (by simpa only [b3a_cfg_map] using writeRun)
  have cwFirst : ∀ u < t + 1 + 4,
      (CW.runFrom (b3a_cfg (Sum.inl entry) x []) u).state ≠ some (Sum.inr .done) := by
    simpa only [b3a_cfg_map] using seamCompTM_firstReturn_ofCfg C exit W (.wr 0) .done
      countRun rfl countFirst (by simpa only [b3a_cfg_map] using writeRun) rfl
      (by simpa only [b3a_cfg_map] using writeFirst)
  -- The last phase forwards the hosted counter's full output, including its halting step.
  let u := b * (y.length + 1)
  have tag : FinTM.VirtualTag (L.tm.initCfg y).inputPos true := by
    simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]
  obtain ⟨tagEnd, _, hosted⟩ := vhostEmitTM_runFrom L.tm (L.tm.initCfg y) true tag
    (1 : Fin (x.length + 2)) [] u
  have emitted : E.runFrom (b3a_cfg (L.tm.q₀, true) x y) u =
      embedEmitCfg iv (fun _ _ => none) (fun _ => 0) []
        (vhostCfg (L.tm.runFrom (L.tm.initCfg y) u) tagEnd (1 : Fin (x.length + 2)) []) := by
    rw [← b3a_embed_cfg (vhostEmitTM L.tm) iv iv0 (L.tm.q₀, true) x y,
      ← b3a_virtual_cfg, embedEmitTM_runFrom, hosted]
  have fullRun := seamCompTM_run_ofCfg CW (Sum.inr .done) E (L.tm.q₀, true)
    cwRun rfl cwFirst (by simpa only [b3a_cfg_map] using emitted)
  have start : M.tm.initCfg x = b3a_cfg (Sum.inl (Sum.inl entry)) x [] := by
    apply Cfg.ext <;> simp [M, MultiTapeTM.initCfg, b3a_cfg, Cfg.init]
  refine ⟨(t + 1 + 4) + 1 + u, ?_, ?_⟩
  · apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [start]
    change (H.runFrom _ _).state = none ∧ (H.runFrom _ _).output = _
    rw [show b3a_cfg (Sum.inl (Sum.inl entry)) x [] =
      (b3a_cfg (Sum.inl entry) x []).mapState Sum.inl from rfl, fullRun]
    obtain ⟨halted, output⟩ := (FinTM.computesInTime_iff L y _ u).mp (computes y)
    simp only [Cfg.mapState, embedEmitCfg, vhostCfg, List.nil_append,
      halted, output, Option.map_none, y, b3a_word_length, and_self]
  · rw [start]
    change H.spaceUsed _ _ ≤ _
    -- Add the three boundary-inclusive ledgers before absorbing the constant slack.
    have firstLedger := b3a_seam_space C exit W (.wr 0) (b := 4)
      countRun rfl countFirst
    have lastLedger := b3a_seam_space CW (Sum.inr .done) E (L.tm.q₀, true) (b := u)
      cwRun rfl cwFirst
    simp only [b3a_cfg_map] at firstLedger lastLedger
    have cSpace := b3a_embed_space R ic (b3a_cfg entry x []) t
    rw [b3a_embed_cfg R ic ic0] at cSpace
    have wSpace := b3a_embed_space (writeConstTM 1 0 [true]) iw
      (b3a_cfg (.wr 0) x x.length.bits) 4
    rw [b3a_embed_cfg (writeConstTM 1 0 [true]) iw iw0] at wSpace
    have eSpace := b3a_embed_space (vhostEmitTM L.tm) iv
      (vhostCfg (L.tm.initCfg y) true (1 : Fin (x.length + 2)) []) u
    rw [b3a_virtual_cfg, b3a_embed_cfg (vhostEmitTM L.tm) iv iv0] at eSpace
    have eSource := vhostEmitTM_spaceUsed_le L.tm (L.tm.initCfg y) true tag
      (1 : Fin (x.length + 2)) [] u
    rw [b3a_virtual_cfg] at eSource
    have sizeBound : Nat.size y.length ≤ y.length := by
      rw [← Nat.size_eq_bits_len]
      exact length_bits_le_self _
    have width := LogProg.length_bits_le_log x.length
    have yLength : y.length = logSpace x.length := b3a_word_length _
    have nativeBound : C.spaceUsed (b3a_cfg entry x []) t ≤
        k * (B * (logSpace x.length + 1) + 1) := by
      apply cSpace.trans
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add_right
      exact countSpace.trans (Nat.mul_le_mul_left B (Nat.add_le_add_right width 1))
    have writerBound : W.spaceUsed (b3a_cfg (.wr 0) x x.length.bits) 4 ≤ k * 3 := by
      exact wSpace.trans (Nat.mul_le_mul_left _ (by omega))
    have emitterBound : E.spaceUsed (b3a_cfg (L.tm.q₀, true) x y) u ≤
        k * (b * (logSpace x.length + 1) + logSpace x.length + 3) := by
      apply eSpace.trans
      apply Nat.mul_le_mul_left
      have ls := space y u
      have bound := (Nat.mul_le_mul_left b (Nat.add_le_add_right sizeBound 1))
      rw [yLength] at bound eSource ls
      omega
    calc
      _ ≤ C.spaceUsed (b3a_cfg entry x []) t +
          W.spaceUsed (b3a_cfg (.wr 0) x x.length.bits) 4 +
          E.spaceUsed (b3a_cfg (L.tm.q₀, true) x y) u :=
        lastLedger.trans (Nat.add_le_add_right firstLedger _)
      _ ≤ k * (B * (logSpace x.length + 1) + 1) + k * 3 +
          k * (b * (logSpace x.length + 1) + logSpace x.length + 3) := by
        exact Nat.add_le_add (Nat.add_le_add nativeBound writerBound) emitterBound
      _ ≤ (k * (B + b + 8) + 1) * (logSpace x.length + 1) := by
        ring_nf; omega

/-- **The logarithm is space-constructible.** [AB09, p. 79: "all functions of
interest, including `log n`, …, are space-constructible"]

**Proof sketch.** Fill obligations: a machine that (i) counts the input length
in binary on a work tape by one left-to-right input scan with a binary
increment at each step (the `Turing.counterTM`/`incrementTM` idiom — P11 of
`machine-library-design.md` §4, space-annotated per §12 R3) — the counter word
has `|Nat.bits n| = logSpace n` cells **for `n > 0` only** (`Nat.bits 0 = []`
has length `0 ≠ logSpace 0 = 1`), so (ii) the empty
input is special-cased to emit `(logSpace 0).bits = [true]` directly, and
otherwise the machine computes the counter word's bit-length by a second count
and emits its bits. Space: the counters and markers fit in
`A·(logSpace n + 1) ≤ 2A·logSpace n` visited cells (boundary cells included
before absorbing, since `logSpace n ≥ 1`); the dominance conjunct is `le_refl`
at `S = logSpace`.

**Fill appendix.** The empty-input special case is realized uniformly: after
R8.5c counts the native input, the constant writer sets the first buffered cell
to `true`. The resulting word has length `logSpace n`, including at zero. A
Z1-hosted Catalog length counter emits its binary length and genuinely halts.
Both live exits are intercepted at their first visits. The space ledger includes
the native head intervals, the overwrite boundary, the virtual-input boundary
cells and the fresh bank, giving `A * (logSpace n + 1)` before absorption. -/
theorem spaceConstructible_logSpace : SpaceConstructible logSpace := by
  obtain ⟨A, hA, M, hM⟩ := b3a_log_machine
  refine ⟨fun _ => le_rfl, 2 * A, by omega, M, ?_⟩
  intro x
  obtain ⟨t, ht, hs⟩ := hM x
  refine ⟨t, ht, hs.trans ?_⟩
  have hlog : logSpace x.length + 1 ≤ 2 * logSpace x.length := by
    unfold logSpace
    omega
  calc
    A * (logSpace x.length + 1) ≤ A * (2 * logSpace x.length) :=
      Nat.mul_le_mul_left _ hlog
    _ = (2 * A) * logSpace x.length := by ring

/-- **Linear space is constructible**: `n ↦ n + 1` is space-constructible (the
`+ 1` prevents the inherited zero-bound collapse at `n = 0` — the zero-bound
convention, `SpaceComplexity/ZeroSpace.lean` — and satisfies the dominance
conjunct; zero-space classes are nonempty, so this is about collapse, not
vacuity).

**Proof sketch.** The input-scan counter of
`Complexity.spaceConstructible_logSpace`, **initialized at `1`** so that after
`n` consumed symbols it holds `n + 1` (an uncorrected length counter holds `n`
and emits the wrong word); emit its bits. Space:
the counter's binary width plus fixed administrative cells fit in
`A·(n + 2) ≤ 2A·(n + 1)` visited cells; dominance is `logSpace n ≤ n + 1`
(`1 ≤ 1` at `n = 0`; a small arithmetic lemma otherwise).

**Fill appendix.** The counter initialized at `1` is realized by the Catalog
length counter on `true :: x`, using the proved prepend and buffered-composition
rows. Its linear running time bounds all visited work-tape cells, including
the counter width and boundary cells. -/
theorem spaceConstructible_linear : SpaceConstructible fun n => n + 1 := by
  refine ⟨logSpace_le_succ, ?_⟩
  obtain ⟨P, a, hp, _⟩ := FinTM.computesFunInTime_prepend_spaceUsed [true]
  obtain ⟨L, b, hl, _⟩ := FinTM.computesFunInTime_lengthBits_spaceUsed
  let M := FinTM.bufferedCompTM P L
  refine ⟨M.k * (a + 2 * b + 4) + 1, by omega, M, ?_⟩
  intro x
  let t := a * (x.length + 1) + (x.length + 1) + 2 + b * (x.length + 2)
  refine ⟨t, ?_, ?_⟩
  · simpa [M, t] using FinTM.bufferedCompTM_computesInTime P L (hp x) (hl ([true] ++ x))
  · have ht : t + 1 ≤ (a + 2 * b + 4) * (x.length + 1) := by
      dsimp [t]
      ring_nf; omega
    calc
      M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (t + 1) :=
        M.tm.spaceUsed_le_mul_succ _ _
      _ ≤ M.k * ((a + 2 * b + 4) * (x.length + 1)) := Nat.mul_le_mul_left _ ht
      _ ≤ (M.k * (a + 2 * b + 4) + 1) * (x.length + 1) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- The tail transducer's transition: one bit of state, "the first bit has been read". -/
private def scp_tailδ : Bool → Bool → Bool := fun _ _ => true

/-- The tail transducer's emission: nothing on the first bit, the bit itself afterwards. -/
private def scp_tailO : Bool → Bool → Option Bool := fun q b => if q then some b else none

/-- After the first bit the tail transducer copies its input. -/
private theorem scp_transduce_copy (l : List Bool) : transduce scp_tailδ scp_tailO true l = l :=
  transduce_of_copy _ _ true (fun _ => rfl) (fun _ => rfl) l

/-- From its start state the tail transducer computes `List.tail`. -/
private theorem scp_transduce_tail (x : List Bool) :
    transduce scp_tailδ scp_tailO false x = x.tail := by
  cases x with
  | nil => exact transduce_nil _ _ _
  | cons b l =>
    rw [transduce_cons]
    simp only [scp_tailO, scp_tailδ, Bool.false_eq_true, if_false, Option.toList_none,
      List.nil_append, scp_transduce_copy, List.tail_cons]

/-- The unary intermediate is short: `(|x.tail| + 1) ^ c ≤ |x| ^ c + 1`. -/
private theorem scp_tail_pow_le (c : ℕ) (x : List Bool) :
    (x.tail.length + 1) ^ c ≤ x.length ^ c + 1 := by
  cases x with
  | nil => simp
  | cons b l => simp

/-- The conditional's value: for `1 ≤ c`, the branch function is `x ↦ (|x| ^ c + 1).bits`
(`0 ^ c + 1 = 1` on the empty input; otherwise the count of `true :: 1ᴾ` with
`P = (|x.tail| + 1) ^ c = |x| ^ c`). -/
private theorem scp_value (c : ℕ) (hc : 1 ≤ c) (x : List Bool) :
    (if decide (x = []) then Nat.bits 1
      else Nat.bits (true :: List.replicate (1 * (x.tail.length + 1) ^ c) true).length) =
      Nat.bits (x.length ^ c + 1) := by
  cases x with
  | nil =>
    simp only [decide_true, if_true, List.length_nil]
    rw [zero_pow (by omega), Nat.zero_add]
  | cons b l =>
    simp only [reduceCtorEq, decide_false, Bool.false_eq_true, if_false, List.length_cons,
      List.length_replicate, Nat.one_mul, List.tail_cons]

/-- The main branch's time, as arithmetic: with `P = (|x.tail| + 1) ^ c ≤ N + 1`, `N = |x| ^ c`,
and `|x.tail| ≤ |x|`, the four phases' exact times sum to at most
`(5c + 20 + 3c_L)(N + |x| + 1)`. -/
private theorem scp_time_arith (c cL t n P N : ℕ) (hP : P ≤ N + 1) (ht : t ≤ n) :
    n + 1 + t + 2 + (1 + 5 * c + 4) * P + P + 2 + (0 + 1 + P + 1) + (0 + 1 + P) + 2 +
      cL * (0 + 1 + P + 1) ≤ (5 * c + 20 + 3 * cL) * (N + n + 1) := by
  have h1 := Nat.mul_le_mul_left (1 + 5 * c + 4) hP
  have h2 := Nat.mul_le_mul_left cL hP
  nlinarith [h1, h2, Nat.zero_le (c * n), Nat.zero_le (cL * n), Nat.zero_le (cL * N),
    Nat.zero_le (c * N)]

/-- The conditional's time, as arithmetic: with `n ≤ N`, the bound
`c_M (c_D (n + 1) + max (c₁ (n + 1)) (K (N + n + 1)) + 1) + 1` is at most `A (N + 1)` for
`A = c_M (c_D + c₁ + 2K + 2) + 1`. -/
private theorem scp_space_arith (cM cD c₁ K n N : ℕ) (hn : n ≤ N) :
    cM * (cD * (n + 1) + max (c₁ * (n + 1)) (K * (N + n + 1)) + 1) + 1 ≤
      (cM * (cD + c₁ + 2 * K + 2) + 1) * (N + 1) := by
  have hmax : max (c₁ * (n + 1)) (K * (N + n + 1)) ≤ c₁ * (n + 1) + K * (N + n + 1) :=
    max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _)
  have e1 := Nat.mul_le_mul_left cD hn
  have e2 := Nat.mul_le_mul_left c₁ hn
  have e3 := Nat.mul_le_mul_left K hn
  have hin : cD * (n + 1) + max (c₁ * (n + 1)) (K * (N + n + 1)) + 1 ≤
      (cD + c₁ + 2 * K + 2) * (N + 1) := by
    nlinarith [hmax, e1, e2, e3]
  have h4 := Nat.mul_le_mul_left cM hin
  nlinarith [h4, Nat.zero_le (cM * (cD + c₁ + 2 * K + 2))]

/-- **Polynomial bounds are space-constructible** [AB09, p. 79]: for `1 ≤ c`, the normal-form
bound `n ^ c + 1` is `Complexity.SpaceConstructible`. (Degree zero is excluded: `n ^ 0 + 1 = 2`
fails the bundled `logSpace n ≤ S n` at large `n`; consumers route degree
zero through monotonicity into degree one.)

**Proof sketch.** Dominance: `logSpace n ≤ n + 1 ≤ n ^ c + 1` (`Complexity.logSpace_le_succ`,
and `n ≤ n ^ c` for `1 ≤ c`). The witness machine computes
`x ↦ (|x| ^ c + 1).bits` as a timed conditional on `x = []`
(`Turing.FinTM.computesFunInTime_cond`, with the decider
`Turing.FinTM.computesFunInTime_decideEq []`). On the empty input the constant
writer emits `(1).bits`, which is the value since `0 ^ c + 1 = 1`. Otherwise four phases run by
buffered composition (`Turing.FinTM.bufferedCompTM_computesInTime`), each at its exact time:
1. a two-state transducer drops the first bit (`Complexity.transducerTM_computes`; from its
   second state it copies, `Complexity.transduce_of_copy`);
2. the unary generator `polyUnaryTM 1 c` writes `(|x| - 1 + 1) ^ c = |x| ^ c` ones;
3. `prependTM [true]` adds one more;
4. the length counter emits the binary length `|x| ^ c + 1`.
The four times sum to `O(|x| ^ c + |x| + 1)`, because the unary word has length at most
`|x| ^ c + 1`, so the conditional halts within `A (|x| ^ c + 1)` steps for a constant `A`
(`|x| ≤ |x| ^ c`). Space follows from time: a `k`-tape machine visits at most `k (t + 1)`
work-tape cells in `t` steps (`Turing.MultiTapeTM.spaceUsed_le_mul_succ`), which gives the
space constant `k A + 1`. -/
theorem spaceConstructible_poly (c : ℕ) (hc : 1 ≤ c) :
    SpaceConstructible fun n => n ^ c + 1 := by
  -- the published rows
  obtain ⟨L, cL, hL⟩ := FinTM.computesFunInTime_lengthBits
  obtain ⟨D, cD, hD'⟩ := FinTM.computesFunInTime_decideEq []
  obtain ⟨K₁, c₁, hK₁⟩ := FinTM.computesFunInTime_const (Nat.bits 1)
  let T := transducerTM scp_tailδ scp_tailO false
  let U := FinTM.polyUnaryTM 1 c
  let P := FinTM.prependTM [true]
  let N := FinTM.bufferedCompTM (FinTM.bufferedCompTM (FinTM.bufferedCompTM T U) P) L
  let f₂ : List Bool → List Bool := fun x =>
    Nat.bits (true :: List.replicate (1 * (x.tail.length + 1) ^ c) true).length
  -- the main branch, input by input: exact times of the four phases, composed
  have hN : N.ComputesFunInTime f₂ fun n => (5 * c + 20 + 3 * cL) * (n ^ c + n + 1) := by
    apply (FinTM.computesFunInTime_iff _ _ _).mpr
    intro x
    have hT : T.ComputesInTime x x.tail (x.length + 1) := by
      have h := (FinTM.computesFunInTime_iff _ _ _).mp
        (transducerTM_computes scp_tailδ scp_tailO false) x
      rwa [scp_transduce_tail] at h
    have hU := (FinTM.computesFunInTime_iff _ _ _).mp (FinTM.polyUnaryTM_computes 1 c) x.tail
    have hP := (FinTM.computesFunInTime_iff _ _ _).mp (FinTM.prependTM_computes [true])
      (List.replicate (1 * (x.tail.length + 1) ^ c) true)
    have hL' := (FinTM.computesFunInTime_iff _ _ _).mp hL
      ([true] ++ List.replicate (1 * (x.tail.length + 1) ^ c) true)
    have h₁ := FinTM.bufferedCompTM_computesInTime T U hT hU
    have h₂ := FinTM.bufferedCompTM_computesInTime _ P h₁ hP
    have h₃ := FinTM.bufferedCompTM_computesInTime _ L h₂ hL'
    apply h₃.mono
    have hp := scp_tail_pow_le c x
    have htl : x.tail.length ≤ x.length := by simp
    simp only [List.length_replicate, Nat.one_mul, List.length_append, List.length_cons,
      List.length_nil]
    exact scp_time_arith c cL x.tail.length x.length _ _ hp htl
  obtain ⟨M, cM, hM⟩ := FinTM.computesFunInTime_cond hD' hK₁ hN
  -- the value
  have hval : (fun x : List Bool => if decide (x = []) then Nat.bits 1 else f₂ x) =
      fun x => Nat.bits (x.length ^ c + 1) := by
    funext x
    exact scp_value c hc x
  rw [hval] at hM
  -- time, then space from time
  refine (spaceConstructible_iff _).mpr ⟨fun n => ?_,
    M.k * (cM * (cD + c₁ + 2 * (5 * c + 20 + 3 * cL) + 2) + 1) + 1, by omega, M, ?_⟩
  · have h1 := logSpace_le_succ n
    have h2 : n ≤ n ^ c := Nat.le_self_pow (by omega) n
    omega
  · apply (FinTM.computesInSpace_iff _ _ _).mpr
    intro x
    refine ⟨_, (FinTM.computesFunInTime_iff _ _ _).mp hM x, ?_⟩
    apply (MultiTapeTM.spaceUsed_le_mul_succ _ _ _).trans
    have hB := scp_space_arith cM cD c₁ (5 * c + 20 + 3 * cL) x.length (x.length ^ c)
      (Nat.le_self_pow (by omega) x.length)
    calc M.k * (cM * (cD * (x.length + 1) + max (c₁ * (x.length + 1))
            ((5 * c + 20 + 3 * cL) * (x.length ^ c + x.length + 1)) + 1) + 1)
        ≤ M.k * ((cM * (cD + c₁ + 2 * (5 * c + 20 + 3 * cL) + 2) + 1) * (x.length ^ c + 1)) :=
          Nat.mul_le_mul_left _ hB
      _ ≤ (M.k * (cM * (cD + c₁ + 2 * (5 * c + 20 + 3 * cL) + 2) + 1) + 1) *
            (x.length ^ c + 1) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _)

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Basic.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-bounded computation, `SPACE`, `L`, and implicitly logspace computable functions

[AB09, Def 4.1]: a language is in `SPACE(s(n))` when some machine decides it while
visiting at most `c · s(n)` work-tape cells on every input of length `n`; `L = SPACE(log n)`
[AB09, Def 4.5]. [AB09, Def 4.16]: a function `f` is *implicitly logspace computable* when it
is polynomially bounded and the two languages "the `i`-th bit of `f(x)` is `1`" and
"`i` is a position of `f(x)`" are in `L`.

## The machine model

We reuse the campaign's machines (`Turing.FinTM Bool`) unchanged. They already have the
shape of [AB09, Fig. 4.1]:

* **the input tape is read-only**: a transition (`Turing.Action`) has no write component
  for the input tape, only a head move, clamped to the input and its two boundary blanks;
* **the output tape is write-once, append-only**: a step appends at most one symbol;
* **space is the number of work-tape cells visited** (`Turing.MultiTapeTM.spaceUsed`, the
  sum over the work tapes of the visited cells), exactly the measure of [AB09, Def 4.1]
  ("at most `c · s(n)` locations on M's work tapes (excluding the input tape) are ever
  visited by M's head").

## Main definitions

* `Turing.FinTM.ComputesInSpace` — `M` computes `f`, halting on every input, visiting at most
  `s(|x|)` work cells.
* `Turing.FinTM.DecidesInSpace` — `M` decides `L` within space `s`. [AB09, Def 4.1]
* `Complexity.SPACE` — the class of languages decidable in space `c · s(n)`. [AB09, Def 4.1]
* `Complexity.logSpace` — the logarithmic space bound `⌊log₂ n⌋ + 1`.
* `Complexity.LOGSPACE` — the class `L = SPACE(log n)`. [AB09, Def 4.5]
* `Complexity.indexLang` — the language `{⟨x, i⟩ | p x i}` with `i` in binary.
* `Complexity.ImplicitlyLogspaceComputable` — [AB09, Def 4.16].

## Main results

* `Turing.FinTM.computesInSpace_iff`, `Complexity.logSpace_eq` — the definitions of
  `ComputesInSpace` and `logSpace` as an equivalence and an equation.
* `Turing.FinTM.decidesInSpace_iff`, `Complexity.mem_SPACE_iff`, `Complexity.LOGSPACE_eq` —
  the definitions of `DecidesInSpace`, `SPACE` and `LOGSPACE`, unfolded.
* `Complexity.SPACE.mono` — `SPACE` is monotone in the space bound.
* `Complexity.logSpace_le_succ`, `Complexity.logSpace_le_of_le_mul_two_pow` — the logarithmic
  bound is at most linear, and at most `(A + 1) s` below `A · 2^s`.
* `Complexity.logSpace_le_size_succ` — the logarithmic bound is at most one more than the
  binary length.
* `Complexity.SPACE.mono_const` — `SPACE` absorbs constant factors (added 2026-10-10).
* `Turing.FinTM.computesInSpace_zero_of_k_eq_zero` — no work tapes, zero space (added
  2026-10-10).

## Divergences from [AB09]

* **The logarithm.** [AB09] writes `SPACE(log n)` and requires `s(n) ≥ log n` (p. 79). We use
  `logSpace n = ⌊log₂ n⌋ + 1`, which is at least `1` (so short inputs get constant space, the
  standard reading of the convention) and is `Θ(log n)` for `n ≥ 2`.
* **Pairs and indices** (Def 4.16). The pair `⟨x, i⟩` is `Turing.pairEncode x (Nat.bits i)`:
  the campaign's self-delimiting pairing with the index in little-endian binary without
  redundant zeros (`Nat.bits 0 = []`). Indices are **`0`-based**: the bit language is
  `{⟨x, i⟩ | f(x)ᵢ = 1}` with `f(x)ᵢ` the `i`-th bit from `0`, and the length language is
  `{⟨x, i⟩ | i < |f(x)|}` where [AB09] writes `i ≤ |f(x)|` for `1`-based `i`.
* **Polynomial bound** (Def 4.16). [AB09] asks `|f(x)| ≤ |x|^c`; at `x = ε` that forces
  `f(ε) = ε` for `c ≥ 1`. We use the campaign normal form `|f(x)| ≤ C · (|x| + 1)^c`
  (`Complexity.PolyBound` shape).
* **Halting.** Deciding (resp. computing) includes halting on every input, as in [AB09]
  ("a TM M deciding L"); the space bound is checked at the halting time, and since space is
  monotone in time and frozen after halting this is the space of the whole computation.
* **One measure for both classes.** [AB09, Def 4.1]'s own wording splits: *visited*
  work-tape locations for `SPACE` (the clause quoted above) but *nonblank* locations for
  `NSPACE`. The campaign convention is the visited-cells measure for both; the planned
  `NSPACE` (`AroraBarakChapters3-4Plan.md`, phase P4.1) counts visited cells along every
  choice word, with all branches halting.
* **Zero bounds collapse the class** (P0 reception audit, round 1, finding 1): every
  work tape's visited set contains its origin, so every machine satisfies
  `M.k ≤ spaceUsed` on every input at every time. A single length with `s n = 0`
  therefore forces a deciding machine to have **no work tapes at all** — and then it
  has zero space on *every* input — so `SPACE s = SPACE (fun _ => 0)` (semantically
  the two-way-finite-automaton class) whenever `s` has a zero; multiplicative
  absorption cannot repair this, since `c * 0 = 0`. In particular the literal
  `SPACE (fun n => n)` is **not** linear space: `n = 0` collapses it. **Campaign
  convention:** every asymptotic chapter statement uses an everywhere-positive bound —
  `fun n => n + 1`, `fun n => n ^ c + 1`, `Complexity.logSpace` — never a bound with a
  zero. The characterization and the harmless-normalization identities are the sanity
  layer `TCSlib.Complexity.SpaceComplexity.ZeroSpace`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definitions 4.1 and 4.5; §4.3, Definition 4.16.)
-/

namespace Turing.FinTM

/-- The machine `M` computes `f` in space `s`: on every input `x` it halts with output `f x`,
and up to that time it has visited at most `s |x|` work-tape cells (summed over its work
tapes). The input tape (read-only) and the output tape (append-only) do not count.
[AB09, Def 4.1, for functions] -/
def ComputesInSpace (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length

/-- **Computing in space, unfolded**: `M` computes `f` in space `s` exactly when on every input
`x` there is a time `t` at which `M` has halted with output `f x`
(`Turing.FinTM.ComputesInTime`), having visited at most `s |x|` work-tape cells by then. -/
theorem computesInSpace_iff (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) :
    M.ComputesInSpace f s ↔
      ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length :=
  Iff.rfl

/-- The machine `M` decides `L` in space `s`: it computes the indicator `[x ∈ L]` (a
one-bit output) in space `s`. [AB09, Def 4.1] -/
def DecidesInSpace (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s

/-- **Deciding in space, unfolded**: `M` decides `L` in space `s` exactly when it computes the
one-bit indicator `x ↦ [x ∈ L]` in space `s`. -/
theorem decidesInSpace_iff (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) :
    M.DecidesInSpace L s ↔
      M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s :=
  Iff.rfl

/-- A space bound can be weakened. -/
theorem ComputesInSpace.mono {M : FinTM Bool} {f : List Bool → List Bool} {s s' : ℕ → ℕ}
    (h : M.ComputesInSpace f s) (hs : ∀ n, s n ≤ s' n) : M.ComputesInSpace f s' := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  exact ⟨t, ht, hsp.trans (hs _)⟩

/-- A machine with no work tapes computes in zero space whatever it computes at all: the
space measure counts only work-tape cells. (Shared by the zero-space layer; added
2026-10-10.)

**Proof sketch.** With `M.k = 0` the space measure is an empty sum
(`Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`), at every halting time. -/
theorem computesInSpace_zero_of_k_eq_zero {M : FinTM Bool} {f : List Bool → List Bool}
    (hk : M.k = 0) (h : ∀ x, ∃ t, M.ComputesInTime x (f x) t) :
    M.ComputesInSpace f fun _ => 0 := by
  intro x
  obtain ⟨t, ht⟩ := h x
  exact ⟨t, ht, (MultiTapeTM.spaceUsed_zero_tapes_eq_zero (tm := M.tm) _ t hk).le⟩

end Turing.FinTM

namespace Complexity

open Turing

/-- **`SPACE(s)`** [AB09, Def 4.1]: the languages decided by some finite binary-alphabet
machine visiting at most `c · s(n)` work-tape cells on inputs of length `n`, for some
constant `c`. -/
def SPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n}

/-- **Membership in `SPACE`, unfolded**: `L ∈ SPACE s` exactly when some machine decides `L` in
space `c · s` for some constant `c`. -/
theorem mem_SPACE_iff {s : ℕ → ℕ} {L : Language Bool} :
    L ∈ SPACE s ↔ ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n :=
  Iff.rfl

/-- `SPACE` is monotone in the space bound. -/
theorem SPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : SPACE s₁ ⊆ SPACE s₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, hM.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- `SPACE` absorbs constant factors: if `s₁ ≤ a · s₂` pointwise, then
`SPACE s₁ ⊆ SPACE s₂`. [AB09, Def 4.1: the constant `c` absorbs `a`] (Shared by the
zero-space layer and the hierarchy arguments; added 2026-10-10.)

**Proof sketch.** A witness at constant `c` for `s₁` is a witness at constant `c · a`
for `s₂`, since `c · s₁ n ≤ c · (a · s₂ n) = (c · a) · s₂ n`
(`Turing.FinTM.ComputesInSpace.mono`). -/
theorem SPACE.mono_const {s₁ s₂ : ℕ → ℕ} {a : ℕ} (h : ∀ n, s₁ n ≤ a * s₂ n) :
    SPACE s₁ ⊆ SPACE s₂ := by
  rintro L ⟨c, M, hM⟩
  refine ⟨c * a, M, hM.mono fun n => ?_⟩
  calc c * s₁ n ≤ c * (a * s₂ n) := Nat.mul_le_mul_left c (h n)
    _ = c * a * s₂ n := (Nat.mul_assoc c a (s₂ n)).symm

/-- The logarithmic space bound `⌊log₂ n⌋ + 1`: `Θ(log n)`, and at least `1`, following the
convention `s(n) ≥ log n` of [AB09, p. 79]. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The logarithmic bound's formula: `logSpace n = Nat.log 2 n + 1`. -/
theorem logSpace_eq (n : ℕ) : logSpace n = Nat.log 2 n + 1 := rfl

/-- The logarithmic bound is at most linear: `logSpace n ≤ n + 1`.

**Proof sketch.** `Nat.log 2 n ≤ n` (`Nat.log_le_self`), then `Complexity.logSpace_eq`. -/
theorem logSpace_le_succ (n : ℕ) : logSpace n ≤ n + 1 := by
  have := Nat.log_le_self 2 n
  rw [logSpace_eq]
  omega

/-- The logarithmic width is at most one more than the binary length:
`logSpace n ≤ Nat.size n + 1`.

**Proof sketch.** At `n = 0` both sides are `1`. Otherwise `2 ^ Nat.log 2 n ≤ n < 2 ^ Nat.size n`
(`Nat.pow_log_le_self`, `Nat.lt_size_self`), so `Nat.log 2 n < Nat.size n`. -/
lemma logSpace_le_size_succ (n : ℕ) : logSpace n ≤ Nat.size n + 1 := by
  unfold logSpace
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h2 : n < 2 ^ Nat.size n := Nat.lt_size_self n
    have : Nat.log 2 n < Nat.size n :=
      (Nat.pow_lt_pow_iff_right (show 1 < 2 by norm_num)).mp (lt_of_le_of_lt h1 h2)
    omega

/-- A number at most `A · 2^s` (with `s ≥ 1`) has `logSpace` at most `(A + 1) s`. -/
theorem logSpace_le_of_le_mul_two_pow {v A s : ℕ} (h : v ≤ A * 2 ^ s) (hs : 1 ≤ s) :
    logSpace v ≤ (A + 1) * s := by
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hlt : v < 2 ^ (A + s) := by
    rw [pow_add]
    exact lt_of_le_of_lt h (Nat.mul_lt_mul_of_pos_right hA (Nat.two_pow_pos s))
  have hle : A + s ≤ (A + 1) * s := by
    have := Nat.le_mul_of_pos_right A (show 0 < s by omega)
    rw [Nat.add_mul, Nat.one_mul]; omega
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp only [logSpace, Nat.log_zero_right]; omega
  · have := Nat.log_lt_of_lt_pow (by omega) hlt
    simp only [logSpace]; omega

/-- **The class `L`** [AB09, Def 4.5]: `L = SPACE(log n)`, the languages decidable by a
machine visiting `O(log n)` work-tape cells. (Named `LOGSPACE` to keep the letter `L` free
for language variables.) -/
def LOGSPACE : Set (Language Bool) := SPACE logSpace

/-- `LOGSPACE` is `SPACE logSpace`. -/
theorem LOGSPACE_eq : LOGSPACE = SPACE logSpace := rfl

/-- The language `{⟨x, i⟩ | p x i}`, the pair encoded as `Turing.pairEncode x (Nat.bits i)`
(index in little-endian binary). The shape of the two languages of [AB09, Def 4.16]. -/
def indexLang (p : List Bool → ℕ → Prop) : Language Bool :=
  {w | ∃ x i, w = pairEncode x (Nat.bits i) ∧ p x i}

/-- **Implicitly logspace computable functions** [AB09, Def 4.16]: `f` is polynomially
bounded, `|f(x)| ≤ C · (|x| + 1)^c`, and both the bit language
`{⟨x, i⟩ | f(x)ᵢ = 1}` and the length language `{⟨x, i⟩ | i < |f(x)|}` are in `L`.
Indices are `0`-based and written in binary (`Nat.bits`); see the module docstring for the
divergences (`0`-based `i < |f(x)|` for the book's `1`-based `i ≤ |f(x)|`, and the `+ 1`
in the polynomial bound). -/
def ImplicitlyLogspaceComputable (f : List Bool → List Bool) : Prop :=
  (∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c) ∧
  indexLang (fun x i => (f x).getD i false = true) ∈ LOGSPACE ∧
  indexLang (fun x i => i < (f x).length) ∈ LOGSPACE

/-- `logSpace` is monotone. -/
lemma logSpace_mono {a b : ℕ} (h : a ≤ b) : logSpace a ≤ logSpace b := by
  unfold logSpace
  have := Nat.log_mono_right (b := 2) h
  omega

end Complexity
```

## ===== TCSlib/Complexity/ClassP/TimeConstructible.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time-constructible functions

A function `T : ℕ → ℕ` is *time constructible* if `T n ≥ n` and some machine computes,
on every input `x`, the binary representation of `T |x|` within at most
`c · (T |x| + 1)` steps for a positive constant `c`. [AB09, §1.3, with the audit-mandated
budget repair below.] Time constructibility rules out pathological time bounds. It is
needed when a machine must *generate* a step budget from its input length, as in the
hierarchy theorems; note that the timed universal machine of [AB09, p. 21] receives its
budget as an explicit extra input and needs no constructibility hypothesis.

## Design and deviations from [AB09]

* Binary representation is `Nat.bits` (least-significant-bit first, with no redundant
  most-significant zeros; `Nat.bits 0 = []`), where [AB09] writes `⌞T(|x|)⌟` without
  fixing endianness. Nothing in Chapter 1 depends on the choice.
* **Deviation (audit-mandated).** [AB09] demands the computation run within exactly
  `T n` steps and then asserts that `n`, `n log n`, `n²`, `2ⁿ` are time constructible.
  The phase-1 external audit (`audits/phase1-findings.md`, finding 1, adversarial cases
  5-6) *proved the literal reading false in this model*: under the exact bound, the
  identity function — [AB09]'s own first example — is not time constructible (on the
  budget `T n = n`, the first transition on `[false]` and `[false, false]` is the same
  function call, and the length-1 budget forces it to halt with output `[true]`, which
  absorption then freezes at length 2), and even `T n = n + 1` fails by an append-only
  prefix argument. We therefore allow a positive constant factor on `T n + 1`, which
  suffices for every downstream use and restores the book's examples *after small-input
  normalization*: the literal `n · ⌈log₂ n⌉`, for instance, still violates `T n ≥ n` at
  `n = 1`, so such examples are stated with a `max`-with-`n` or `+ 1` normalization.
  Exact constants in downstream results must be derived from this form, not inherited
  from the strict reading.

## Main definitions

* `Complexity.TimeConstructible` — [AB09, §1.3], with the constant-slack repair above.
* `Turing.FinTM.lengthBitsTM` — the binary length counter `x ↦ Nat.bits |x|` (MIG-1),
  declared under its `Turing.FinTM` name.

## Main results

* `Complexity.timeConstructible_iff` — the definition as an equivalence.
* `Complexity.timeConstructible_id` — the identity function is time constructible,
  restoring [AB09]'s example under the repaired definition.
* `Turing.FinTM.lengthBitsTM_computes`, `Turing.FinTM.lengthBitsTM_spaceUsed` — the
  counter's time `5 · (n + 1)` and space `5 · (Nat.size |x| + 1)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, "Time-constructible functions".)
-/

namespace Complexity

open Turing

/-- `T` is time constructible: `T n ≥ n`, and some finite binary machine computes
`x ↦ ⌞T |x|⌟` (binary via `Nat.bits`) within `c · (T |x| + 1)` steps for a positive
constant `c`. [AB09, §1.3], with the constant-slack deviation documented in the module
docstring (the literal exact-`T n` bound is refuted in this model by
`audits/phase1-findings.md`, finding 1). -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
    M.ComputesInTime x (T x.length).bits (c * (T x.length + 1))

/-- **Time constructibility, unfolded**: `T` is time constructible exactly when `n ≤ T n` for
every `n` and, for some constant `c > 0`, some machine computes `(T |x|).bits` on every input `x`
within `c · (T |x| + 1)` steps. -/
theorem timeConstructible_iff (T : ℕ → ℕ) :
    TimeConstructible T ↔
      (∀ n, n ≤ T n) ∧ ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
        M.ComputesInTime x (T x.length).bits (c * (T x.length + 1)) :=
  Iff.rfl

/-- Increment a little-endian binary word, extending it on overflow. -/
private def counterInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: counterInc bs

/-- The number of initial true bits cleared by an increment. -/
private def counterCarry : List Bool → ℕ
  | true :: bs => counterCarry bs + 1
  | _ => 0

/-- Each cleared true bit decreases the potential by one; the final write adds one.
This is the local accounting identity behind the amortized bound. -/
private lemma counterInc_potential (bs : List Bool) :
    (counterInc bs).count true + counterCarry bs = bs.count true + 1 := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b with
    | false => simp [counterInc, counterCarry]
    | true => simp [counterInc, counterCarry]; omega

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma counterInc_bits (n : ℕ) : counterInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [counterInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [counterInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma counterInc_length (bs : List Bool) :
    (counterInc bs).length ≤ bs.length + 1 ∧
      counterCarry bs ≤ (counterInc bs).length := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b <;> simp only [counterInc, counterCarry, List.length_cons] <;> omega

/-- One carry transition, with the first transition also advancing the input. -/
private def counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- **The binary length counter**. A one-work-tape machine with four states (count `0`, carry `1`,
rewind `2`, emit `3`) that keeps a little-endian binary counter on its work tape, increments it once
per input symbol, and on the blank after the input emits the counter's bits and halts, so that it
computes `x ↦ Nat.bits |x|`. [AB09, §1.3, the examples of time-constructible functions] It is
declared under its `Turing.FinTM` name so that MIG-9 can move it into `Build/` without a rename. -/
def _root_.Turing.FinTM.lengthBitsTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), none, some 3⟩
          | some _ => counterBump .pos (work 0)
        else if q = 1 then counterBump .zero (work 0)
        else if q = 2 then
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .pos), none, some 0⟩
          | some _ => ⟨.zero, fun _ => (none, .neg), none, some 2⟩
        else
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .zero), none, none⟩
          | some b => ⟨.zero, fun _ => (none, .pos), some b, some 3⟩ }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def counterTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, count, and emission invariants. -/
private def counterCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => counterTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma counterTape_read (pre bs : List Bool) :
    counterTape (pre ++ bs) pre.length = bs.head? := by
  simp only [counterTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma counterTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (counterTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      counterTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [counterTape_read]
  · rw [Function.update_of_ne hz]
    unfold counterTape
    by_cases hn : z < 0
    · simp only [if_pos hn]
    · simp only [if_neg hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_cons, if_neg (by omega), List.getElem?_tail]
        congr 1
        omega

/-- One carry transition updates exactly the currently scanned cell. -/
private lemma counter_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    FinTM.lengthBitsTM.tm.step (counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (FinTM.lengthBitsTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [FinTM.lengthBitsTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .zero (counterTape (pre ++ bs) pre.length)).apply _ = _
  rw [counterTape_read]
  unfold counterBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact counterTape_write pre bs _
    · funext j; simp [Action.apply, counterCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma counter_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    FinTM.lengthBitsTM.tm.runFrom (counterCfg x 1 p pre.length (pre ++ bs) [])
        (counterCarry bs + 1) =
      counterCfg x 2 p ((pre.length : ℤ) + counterCarry bs - 1)
        (pre ++ counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [counterCarry]
    rw [MultiTapeTM.runFrom_one, counter_carry_step]
    simp [counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [counterCarry]
      rw [MultiTapeTM.runFrom_one, counter_carry_step]
      simp [counterInc]
    | true =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step, counter_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [counterInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the count state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma counter_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    FinTM.lengthBitsTM.tm.runFrom (counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_one]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, FinTM.lengthBitsTM, counterCfg, Cfg.workTapeSymbols,
        counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : FinTM.lengthBitsTM.tm.step (counterCfg x 2 p (j : ℤ) bs []) =
        counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (FinTM.lengthBitsTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [FinTM.lengthBitsTM, show (2 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, counterCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The first carry transition also consumes exactly one input symbol. -/
private lemma counter_start (x : List Bool) (i : ℕ) (hi : i < x.length) (bs : List Bool) :
    FinTM.lengthBitsTM.tm.step (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      FinTM.lengthBitsTM.tm.step (counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (FinTM.lengthBitsTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (FinTM.lengthBitsTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [FinTM.lengthBitsTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .pos (counterTape bs 0)).apply _ =
    (counterBump .zero (counterTape bs 0)).apply _
  unfold counterBump
  by_cases h : counterTape bs 0 = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val =
        (moveInputPos (⟨i + 2, by omega⟩ : Fin (x.length + 2)) 0).val
      rw [moveInputPos_zero, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rfl
    · rfl
    · rfl

/-- One complete increment takes twice the carry length plus two transitions.
**Proof sketch.** The count transition is the first carry transition, with the
input advanced once. The carry uses `r + 1` steps and leaves the head at `r - 1`;
the rewind uses another `r + 1` steps and leaves the incremented word intact. -/
private lemma counter_increment (x : List Bool) (i : ℕ) (hi : i < x.length)
    (bs : List Bool) :
    FinTM.lengthBitsTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * counterCarry bs + 2) =
      counterCfg x 0 ⟨i + 2, by omega⟩ 0 (counterInc bs) [] := by
  have hc : FinTM.lengthBitsTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
      (counterCarry bs + 1) =
      counterCfg x 2 ⟨i + 2, by omega⟩ ((counterCarry bs : ℤ) - 1) (counterInc bs) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step, counter_start x i hi,
      ← MultiTapeTM.runFrom_succ_eq_step]
    simpa only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] using
      counter_carry x ⟨i + 2, by omega⟩ bs []
  rw [show 2 * counterCarry bs + 2 = (counterCarry bs + 1) + (counterCarry bs + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact counter_rewind x ⟨i + 2, by omega⟩ (counterInc bs) (counterCarry bs)
    (counterInc_length bs).2

/-- The counting invariant carries a nonnegative potential of twice the popcount, and every
head position of the elapsed run lies within twice one plus the final input length's binary
width of the origin.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions.
Each increment starts at the origin and lasts `2r + 2 ≤ 2 · (Nat.size |x| + 1)` steps, since the
carry length is at most the counter's binary width, which is monotone in the count; the
time-derived head envelope (`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`) bounds the head
during the current increment. -/
private lemma counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) t =
        counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] ∧
      ∀ u ≤ t, ∀ j : Fin 1,
        (FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) u).workTapePos j ∈
          Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ)) (2 * (Nat.size x.length + 1) : ℤ) := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq]
      apply Cfg.ext
      · rw [Cfg.init_state]
        rfl
      · rw [Cfg.init_inputPos]
        rfl
      · funext j z
        rw [Cfg.init_workTapes]
        simp only [counterCfg, counterTape, Nat.zero_bits, List.getElem?_nil, ite_self]
      · funext j
        rw [Cfg.init_workTapePos]
        rfl
      · rw [Cfg.init_output]
        rfl
    · intro u hu j
      rw [show u = 0 by omega, MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq,
        Cfg.init_workTapePos, Finset.mem_Icc]
      omega
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc, hb⟩ := ih (by omega)
    refine ⟨t + (2 * counterCarry i.bits + 2), ?_, ?_, ?_⟩
    · have hp := counterInc_potential i.bits
      rw [counterInc_bits] at hp
      omega
    · rw [MultiTapeTM.runFrom_add, hc, counter_increment x i (by omega), counterInc_bits]
    · intro u hu j
      by_cases hut : u ≤ t
      · exact hb u hut j
      · rw [show u = t + (u - t) by omega, MultiTapeTM.runFrom_add, hc]
        have hp := Finset.mem_Icc.mp (MultiTapeTM.workTapePos_runFrom_mem_Icc
          FinTM.lengthBitsTM.tm (counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits []) (u - t) j)
        have hcarry := (counterInc_length i.bits).2
        rw [counterInc_bits, Nat.size_eq_bits_len] at hcarry
        have hwidth := Nat.size_le_size hi
        change 0 - ((u - t : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((u - t : ℕ) : ℤ) at hp
        rw [Finset.mem_Icc]
        constructor <;> omega

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    FinTM.lengthBitsTM.tm.runFrom (counterCfg x 3 p 0 bs []) i =
      counterCfg x 3 p i bs (bs.take i) := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (counterCfg x 3 p i bs (bs.take i)).workTapeSymbols 0 = some bs[i] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(i : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    unfold MultiTapeTM.step
    change (FinTM.lengthBitsTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [FinTM.lengthBitsTM, show (3 : Fin 4) ≠ 0 from by decide,
      show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      ↓reduceIte, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · rfl
    · funext j; simp [Action.apply, counterCfg]
    · simp only [Action.apply, counterCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- At the first blank after the stored word, emission halts without extra output. -/
private lemma counter_emit (x : List Bool) (p : Fin (x.length + 2)) (bs : List Bool) :
    let c := FinTM.lengthBitsTM.tm.runFrom (counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((FinTM.lengthBitsTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [FinTM.lengthBitsTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, counterCfg]

/-- Reading the blank after the input, the count state enters emission without moving.

**Proof sketch.** The input head is at `|x| + 1`, so the input symbol is the right blank; the count
state's transition on a blank changes only the state. -/
private lemma counter_emit_start (x : List Bool) :
    FinTM.lengthBitsTM.tm.step (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
  have hin : (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol = none :=
    Cfg.inputSymbol_of_end rfl
  rw [MultiTapeTM.step_of_some rfl, hin]
  apply Cfg.ext
  · rw [Action.apply_state]
    rfl
  · rw [Action.apply_inputPos]
    exact moveInputPos_zero _
  · funext j
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    exact Function.update_eq_self _ _
  · funext j
    rw [Action.apply_workTapePos]
    rfl
  · rw [Action.apply_output]
    rfl

/-- After counting, entering emission and emitting the stored word, the counter is halted with
output `Nat.bits |x|` at time `t + 1 + (|Nat.bits |x|| + 1)`, where `t` is the counting time. -/
private lemma counter_halt (x : List Bool) (t : ℕ)
    (hc : FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) t =
      counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) :
    FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) (t + 1) =
        counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] ∧
      FinTM.lengthBitsTM.ComputesInTime x x.length.bits
        ((t + 1) + (x.length.bits.length + 1)) := by
  have hstart : FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) (t + 1) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, counter_emit_start]
  have he := counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  refine ⟨hstart, (FinTM.computesInTime_iff _ _ _ _).mpr ⟨?_, ?_⟩⟩
  · rw [MultiTapeTM.runFrom_add, hstart]
    exact he.1
  · rw [MultiTapeTM.runFrom_add, hstart]
    exact he.2

/-- **The length counter's time**. The counter computes `x ↦ Nat.bits |x|` within `5·(n + 1)` steps.
[AB09, §1.3]

**Proof sketch.** With twice the number of `true` counter bits as potential, elapsed time plus
potential is at most `4n` after `n` increments (`counter_count`); entering emission and the final
halt add two steps, and the emitted word, of length at most `n`, costs one step per bit
(`counter_halt`). -/
theorem _root_.Turing.FinTM.lengthBitsTM_computes : FinTM.lengthBitsTM.ComputesFunInTime
    (fun x => Nat.bits x.length) (fun n => 5 * (n + 1)) := by
  refine (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_
  obtain ⟨t, ht, hc, -⟩ := counter_count x x.length (le_refl _)
  apply (counter_halt x t hc).2.mono
  have hl := Turing.length_bits_le_self x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

/-- **The length counter's space**. At every time, the counter's work tape has visited at most
`5·(Nat.size |x| + 1)` cells: logarithmic space.

**Proof sketch.** Every counting round returns the head to the origin and a carry walks at most
the counter's binary width, which never exceeds `Nat.size |x|` (`counter_count`); emission walks
the stored word once, and after the halt nothing moves. So at every time the head stays in the
interval `[-2·(Nat.size |x| + 1), 2·(Nat.size |x| + 1)]`, which has at most
`5·(Nat.size |x| + 1)` cells. -/
theorem _root_.Turing.FinTM.lengthBitsTM_spaceUsed (x : List Bool) (t : ℕ) :
    FinTM.lengthBitsTM.tm.spaceUsed (FinTM.lengthBitsTM.tm.initCfg x) t ≤
      5 * (Nat.size x.length + 1) := by
  obtain ⟨t₀, -, hc, hb⟩ := counter_count x x.length (le_refl _)
  obtain ⟨hstart, hdone⟩ := counter_halt x t₀ hc
  let T := t₀ + 1 + (x.length.bits.length + 1)
  have hhalt : (FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) T).state =
      none := ((FinTM.computesInTime_iff _ _ _ _).mp hdone).1
  -- Before the halt: the counting ledger, then the emission walk from the origin.
  have hpre (v : ℕ) (hv : v ≤ T) (j : Fin 1) :
      (FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) v).workTapePos j ∈
        Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ)) (2 * (Nat.size x.length + 1) : ℤ) := by
    by_cases hvt : v ≤ t₀
    · exact hb v hvt j
    · rw [show v = (t₀ + 1) + (v - (t₀ + 1)) by omega, MultiTapeTM.runFrom_add, hstart]
      have hp := Finset.mem_Icc.mp (MultiTapeTM.workTapePos_runFrom_mem_Icc
        FinTM.lengthBitsTM.tm (counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [])
        (v - (t₀ + 1)) j)
      change 0 - ((v - (t₀ + 1) : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((v - (t₀ + 1) : ℕ) : ℤ) at hp
      have hlen := Nat.size_eq_bits_len x.length
      dsimp only [T] at hv
      rw [Finset.mem_Icc]
      constructor <;> omega
  -- After the halt the configuration is frozen.
  have hall (u : ℕ) (j : Fin 1) :
      (FinTM.lengthBitsTM.tm.runFrom (FinTM.lengthBitsTM.tm.initCfg x) u).workTapePos j ∈
        Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ)) (2 * (Nat.size x.length + 1) : ℤ) := by
    by_cases hu : u ≤ T
    · exact hpre u hu j
    · rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
        MultiTapeTM.runFrom_of_halt _ hhalt]
      exact hpre T (le_refl _) j
  rw [MultiTapeTM.spaceUsed_eq_sum]
  change (∑ i : Fin 1, _) ≤ _
  rw [Fin.sum_univ_one]
  exact (MultiTapeTM.spaceUsedByTape_le_card_Icc _ _ t (0 : Fin 1) _ _
    fun u _ => hall u 0).trans (by omega)

/-- The identity function is time constructible. [AB09, §1.3 examples]

**Proof sketch.** A one-work-tape machine maintains a little-endian binary counter on
its work tape while scanning the input left to right: for each input symbol it
increments the counter (walking right over `true` cells turning them `false` until the
first `false`/blank cell, which becomes `true`, then returning to cell 0). Incrementing
`n` times costs amortized `O(1)` per increment, `O(n)` in total. When the input head
reads the blank past the input, the machine walks the counter left to right emitting
each bit to the output tape (`O(log n)` steps) and halts. The total is at most
`c · (n + 1)` steps for an absolute constant `c`, and the emitted string is `n.bits`
(for `n = 0` the counter region is empty and nothing is emitted, matching
`Nat.bits 0 = []`). The formal proof uses twice the number of true counter bits as
potential: elapsed time plus potential is at most `4n` after `n` increments.
Entering emission and its final halting transition add two steps; the output length
is at most `n`, so `c = 5` suffices. -/
theorem timeConstructible_id : TimeConstructible id :=
  ⟨fun n => le_refl n, 5, by decide, FinTM.lengthBitsTM,
    (FinTM.computesFunInTime_iff _ _ _).mp FinTM.lengthBitsTM_computes⟩

end Complexity
```
