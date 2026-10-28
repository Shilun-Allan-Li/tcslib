# Ch3–4 fill campaign — B6's H, the space hierarchy (`Complexity.space_hierarchy`, with `LOGSPACE_ssubset_PSPACE` and `SPACE_linear_ne_NP`; `SpaceComplexity/Hierarchy.lean`)

> **DRAFT** (maintainer, 2026-10-27). Issues after PR #175 merges (`spaceConstructible_poly` in
> `Constructible`), with the pre-ship re-taken at the issue commit. ⟨…⟩ marks what the pre-ship
> fills in. **Agent: Codex** (user, 2026-10-27).

> **A single fill** (addendum v2.6, Parts 1 and 2; Part 3, the megafill, does not apply, except
> its one-Lean rule and its no-stop rule, items 5 and 7, which "Environment and verification"
> restates). Deliver a checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your targets as gated statements**: the P4.3 statement gate (`campaign/gates/ch4-p43/`),
    the space hierarchy's statement re-gated on the window route (2026-10-13);
  - **every host the route names, proved** on the standard axioms or fewer (17 axiom prints,
    `campaign/status/2026-10-27-headlines/HHosts.*`): the universal machine
    `Turing.exists_selfUniversal` (`TuringMachine/SelfUniversal`); the record rows
    `Turing.exists_recordInitTM` (`Build/RecordTable`); the configuration-count runner
    `Turing.exists_configWindowRunnerTM` (`SpaceComplexity/WindowClock`, **its clock inside it**);
    the window run's facts; the normal forms; the space facts and readings;
  - **`Complexity.spaceConstructible_poly` in `SpaceComplexity/Constructible`** (PR #175, gate 86),
    which your file already imports; `SPACE_linear_ne_NP` needs it at degree two;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**), and the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/b6/inputs/b6-fill-hierarchy/`): the import probe
    (`HImportProbe.lean.txt`), the route probe (`HRouteProbe.lean.txt`) with its seal controls, the
    semantic-duplication probe, the import overlay (`HierarchyOverlay.lean.txt`) and the screen
    population; the order list `campaign/fills/b6/orders/b6-fill-hierarchy.txt`, the base sorry
    set, the screen base and the pre-ship log (`campaign/fills/b6/logs/b6-fill-hierarchy-*`). The
    route's design note is `campaign/items/b6hosts/H/H-route-design.md`.
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule
  (E-RES). Fetch the cache for your roots only (⟨roots⟩); never run the unfiltered
  `lake exe cache get`. If Lean cannot start, follow Part 2 exactly. **If Lean never runs, do not
  draft proofs blind**: deliver the environment report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/b6-hierarchy @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
  # must print 287acce8326a1de271dfa6be2cc3776f3a2caa32
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-b6-hierarchy.zip`, with
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle whose only prerequisite is your base, the environment logs (`evidence/logs/`), the
  bootstrap and final sweep logs with **each module's time and maximum memory**, the axiom log, the
  seal test's source, its controls and both outputs, both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-b6-hierarchy-cp<N>.zip` (`N` 1 to 8) with the same contents as of that commit. Deliver the
  latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign's tree after PR #175.** Lines in this brief are those
  of your base's tree, where `Hierarchy.lean` is 317 lines (4 public declarations, no private).
- **The overlay is your first edit** (region (a)): add, after line 10, exactly
  `import TCSlib.Complexity.TuringMachine.SelfUniversal`,
  `import TCSlib.Complexity.TuringMachine.Build.WindowRun` and
  `import TCSlib.Complexity.SpaceComplexity.WindowClock`
  (`HierarchyOverlay.lean.txt` is the file after it). The pre-ship elaborated it: exactly the four
  sorry warnings (lines 161, 271, 285, 315 of the base), nothing else.
- **In flight:** ⟨none touching your order list, at the issue commit⟩.

## Parallel batches this round

None in `Hierarchy.lean`: **F6** (`Complexity.space_universal`, line 150, the same file) is out of
scope and waits for a later round; leave its statement, docstring and body untouched.

## What this is

**The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through [AB09]). For
space-constructible `f` and `g` with `∀ A, ∃ N, ∀ n ≥ N, A · f n ≤ g n`: `SPACE f ⊂ SPACE g`. Then
two corollaries in the same file:
- `LOGSPACE_ssubset_PSPACE` ([AB09, §4.3.2]): `space_hierarchy` at `logSpace` and `n + 1`;
- `SPACE_linear_ne_NP` ([AB09, Exercise 3.2], at the normalization `n + 1`).

**Where it stands.** The three bodies are `sorry`. Every host is proved; the route probe proves the
inclusion half and `LOGSPACE ⊂ PSPACE` from the hierarchy's statement. **Proved modulo, exactly:**
none. **A complete delivery has no `sorryAx` in the three targets.**

**Read first:** the route note `campaign/items/b6hosts/H/H-route-design.md` (it maps the
docstring's sketch onto the published hosts and says where this brief supersedes the sketch); the
three targets' docstrings (lines 162–315); `exists_configWindowRunnerTM`'s statement
(`WindowClock.lean:1506`); `exists_selfUniversal` (`SelfUniversal.lean:143`).

**Pre-ship check** (the maintainer, against the replay snapshot of your base's tree; log
`campaign/fills/b6/logs/b6-fill-hierarchy-preship.log`): the overlay as above; the import probe
⟨N⟩ checks of ⟨N⟩ names, 0 errors; the route probe's three lemmas on the standard axioms, through
published readings only, sealed ⟨with ⟨N⟩ controls⟩; the order list ⟨modules, roots, base
sorries⟩; the screen base ⟨…⟩; lint ⟨…⟩.

## Owned regions and targets (modify these and nothing else)

`TCSlib/Complexity/SpaceComplexity/Hierarchy.lean`:
- **(a)** the imports, lines 6–10: add exactly the overlay's three;
- **(b)** new private declarations after `space_universal`'s body (line 161) and before
  `space_hierarchy`'s docstring (line 162), in sections of your own if you like;
- **(c)** the three bodies: lines 271 (`space_hierarchy`), 285 (`LOGSPACE_ssubset_PSPACE`) and 315
  (`SPACE_linear_ne_NP`);
- **(d)** the status text: the module docstring's "(all sorried; phase-P4.3 statements)" (line 67);
  in the three targets' docstrings, the status phrases ("spec, fill pending …", lines 163–165, 279
  and 289) and the audit labels ("(recorded here, seeded to the audit)", "(round-1 finding 5)",
  "(round-2 finding 5)"). Rewrite them as public-facing text: no phase, gate, round, finding or
  fill names, no `audits/` or `campaign/` paths, no dated rulings. Propose an
  `**Implementation.**` paragraph for each target's docstring in `REPORT.md` (the clock is the
  runner's, not the sketch's step (iii)); the maintainer lands them.

**Targets:** `Complexity.space_hierarchy` (line 267), `Complexity.LOGSPACE_ssubset_PSPACE` (line
284), `Complexity.SPACE_linear_ne_NP` (line 314); statements frozen.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The universal machine** is `Turing.exists_selfUniversal`: one `U₀` for the scheme
  `Complexity.TimeHierarchy.code`, with, per code `α`, a `C > 0` such that a halting run of
  `decode α` on `pairEncode α w` within space `s` is reproduced by `U₀` with the same output within
  space `C · (s + 1)`. Never build a second universal machine.
- **The run** is `Turing.exists_configWindowRunnerTM` at `U₀`, with the summary update
  (`upd τ b :=` the summary of `τ` followed by `b`; `upd τ none = τ`): from a radius-`r` record of a
  configuration in its window, the other tapes blank, it reaches an exit `out` within
  `C · 2^(C (L + 1))` steps in space `(K + 1)(2C(L + 1) + 1)`, silently, with `out` the window run's
  verdict at every round count up to `configBound + 1`. **The clock is inside it: build no clock,
  counter loop or round driver of your own.**
- **The initial record** is `Turing.exists_recordInitTM` (`Build/RecordTable`) at radius `r = g n`,
  given `bits r` on tape 1, with the empty-output tag.
- **The radius** is `g`'s constructibility witness, lifted to the record alphabet
  (`MultiTapeTM.liftSymbols`, `liftSymbols_runFrom`, `liftSymbols_initCfg`) under the capture
  wrapper (`Turing.capture_run`, `capture_visitedByTapeHead`), writing `bits (g n)` on tape 1 in
  `O(g n)` cells (`counterValue_bits` reads it).
- **The input validation** is `Turing.inputFoldTM` (`inputFoldTM_run_ofCfg`): reject at once a rich
  input that is not an embedded word, so `D`'s space is bounded on every input of the rich alphabet.
- **The composition** is the seam host (`Build/Seam`), whose `seamCompTM_spaceUsed_le_add`,
  `seamCompTM_spaceUsedByTape_le_add` and `_le_max` add the phases' spaces.
- **The packaging** is `Turing.FinTM.decidesInSpace_of_alphabetReduction` (`ConfigCount`): a `Bool`
  decider of `L_D` in space `c · (g n + 1)`, in `SPACE g` by `g`'s floor.
- **The normalization** (for `L_D ∉ SPACE f`): `Turing.FinTM.one_work_tape_binary_spaceUsed`,
  `Turing.exists_codeTM`, and `MultiTapeTM.relabelState_runFrom_init` for the space clause
  `exists_codeTM` does not state.
- **The window facts:** `FinTM.inWindow_of_spaceUsed_le`, `windowRun_summary_of_halts`,
  `FinTM.configBound_le_two_pow`, `outSummary_append_congr`, `outSummary_eq_accept_iff`,
  `FinTM.ComputesInTime.of_spaceUsed_le`, `MultiTapeTM.spaceUsed_mono`,
  `MultiTapeTM.abs_pos_lt_card_visited`, `mem_visited_of_ne_none`.

### The route (binding where it names a row; the rest is the recommended shape)

**The inclusion** (`SPACE f ⊆ SPACE g`): the route probe's `hr_inclusion` (`hfg` at `A = 1` from
some `N` on, `g`'s floor below `N`, `SPACE.mono_const`). Copy it as a private.

**The diagonalizer `D`**, over the record alphabet `RecSym Q₀ (Fin 3)` (`Q₀` the states of `U₀`),
on the embedded input `x.map digitEmb`, as phases composed by the seam host:
1. validate the input (`inputFoldTM`);
2. the radius: `g`'s witness, lifted and captured, writes `bits (g n)` on tape 1 (`r = g n`);
3. the initial record of `U₀`'s start on `x` at radius `r`, with the empty-output tag;
4. the run: `exists_configWindowRunnerTM` at `U₀` with the summary update;
5. the verdict: `false` if the exit is `halted` with summary `accept`, `true` otherwise.

**`D`'s space**: the witness's `O(g n)`, the record's `L = O(r + log n)`, the runner's `O(L)`, all
`O(g n)` by `g`'s floor, **uniformly in the code part of `x`**: the window, not `U₀`'s constant,
bounds the simulation.

**`L_D ∉ SPACE f`.** If `M` decides `L_D` in space `c₀ · f`, normalize it, take its code `α`, and
pad the payload, never the code: on `x = pairEncode α (List.replicate N₀ true)` with `N₀` from `hfg`
at `A := C_α (c · c₀ + c + 1)`, `U₀`'s run stays in the radius-`g n` window and halts within
`configBound` rounds, so the runner exits `halted` with the summary of `U₀`'s output, which is
`[x ∈ L_D]`; `D` answers the opposite.

**`LOGSPACE ⊂ PSPACE`**: the route probe's `hr_logspace_ssubset` applied to `space_hierarchy`, with
`hr_logSpace_dom` and `hr_sq_le_two_pow`. Copy the three as privates.

**`SPACE (n + 1) ≠ NP`**: by padding and `NP`'s closure under `≤ₚ` (the docstring's sketch). Its
obligations: ⟨the `NP` closure lemma: a decision for the user — a private here, or a public row
beside `mem_P_of_polyTimeReducible` (`ClassNP/Reductions`) by an API PR first⟩; the padded
language's space decider; the padding reduction; the strictness extraction, through
`space_hierarchy` at `n + 1` and `n ^ 2 + 1` (`spaceConstructible_linear`,
`spaceConstructible_poly 2`; `A · (n + 1) ≤ n ^ 2 + 1` eventually).

**Edge cases that must stay true:** the empty input; an input of the rich alphabet that is not an
embedded word (rejected by the fold, in bounded space); `U₀` halting with an output other than
`[true]` (`true` from `D`); the window exit and the clock's exhaustion (`true` from `D`); `n` below
`N₀` (the padding chooses `n ≥ N₀`); `f`'s floor `1 ≤ f n` (the arithmetic of `A`).

## Gate guidance (binding)

- **The P4.3 statement gate** froze the statements; the hierarchy's constant-factor hypothesis has
  no square and no logarithmic term; both constructibility hypotheses are the book's, and the proof
  uses `g`'s witness and floor but, of `f`'s, only the floor.
- **The route note's rulings:** H first, the corollaries as later checkpoints of the same fill; F6
  after U2's harvest.

## Cited infrastructure (public and proved at the issue commit; all in `HImportProbe.lean.txt`)

⟨The probe's names⟩: the targets and the space classes with their readings (`mem_SPACE_iff`,
`SPACE.mono`, `SPACE.mono_const`, `decidesInSpace_iff`, `computesInSpace_iff`,
`spaceConstructible_iff`, `LOGSPACE_eq`, `space_poly_subset_PSPACE`, the three constructible
rows); the universal machine and its code scheme; the runner and the window run with its records,
widths, alphabet and facts; the record rows; the output summary; the alphabet reduction and its
space clause; the input fold; the symbol lift; the capture wrapper; the seam's space lemmas; the
space and visited-interval facts; the normal forms; the counter value's readings; `NP`'s
bounded-certificate reading `mem_NP_iff_exists_length_le` and the reductions' `≤ₚ`.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `Hierarchy.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the three targets and `space_universal`.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. The corollaries depend on `space_hierarchy`'s statement only, so they may be proved
   before it.
5. **No touching other sorries**, `space_universal`'s among them. Cite proved material; never
   re-prove it.
6. **Imports.** Exactly the base's five and the overlay's three; add none.
7. **One proof per shared argument.** Never write a second universal machine, clock, counter loop,
   record row, window runner, seam, symbol lift or capture. Never re-walk
   `TimeHierarchy/Diagonal`'s or `TimeHierarchy/Separation`'s privates (a colleague's
   diagonalization), `WindowClock`'s or `RecordTable`'s privates: models to read, not to copy.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 317 lines; 4 public, 0 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and each target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own definitions and privates.
    - **Never unfold a definition of another file**, and no definitional closure either:
      `SPACE` through `mem_SPACE_iff`; `FinTM.DecidesInSpace` and `FinTM.ComputesInSpace` through
      `decidesInSpace_iff` and `computesInSpace_iff`; `SpaceConstructible` through
      `spaceConstructible_iff`; `logSpace` through `logSpace_eq`; `LOGSPACE` through
      `LOGSPACE_eq`; `PSPACE` only through `space_poly_subset_PSPACE`; `NP` through
      `mem_NP_iff_exists_length_le`; the window run, records and summaries through their lemmas.
    - **Scope (user, 2026-10-23):** TCSlib's own definitions. Core and Mathlib definitions may
      reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`, `rw` or `unfold`.
    - **The machine model's primitives** are read through their lemmas; unfold `step` and
      `Action.apply` only for a leaf of your own file, preferring `MultiTapeTM.step_of_some` and
      the `Action.apply_*` field equations.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate**, naming the lemma you need.
    - **Self-check by both methods:** a **seal test** (a scratch copy of your module with
      `attribute [local irreducible]` on every other-file TCSlib definition your proofs mention,
      from your first private on: at least ⟨the pre-ship's list⟩; `attribute [-simp]` on the four
      `@[simp]` TCSlib definitions `Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`,
      `NDTM.initCfg`; **with controls**: for each sealed definition, a goal that closes by `rfl`
      with nothing sealed and fails under the seal, recursive definitions with usage controls); and
      an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
      argument in your diff. **Ship the raw outputs.** A seal not run, or without controls, is a
      checklist failure.
    - List every declaration you cite outside your file; if more than the probe's, extend a copy
      of the probe and run it.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows (`copyTM_run`,
    `transferTM_run`, `clearTM_run`, `compareTM_run`, `incrementTM_run_succ`,
    `incrementTM_run_overflow`); use the framed `_ofCfg` forms. Cite no private declaration of
    another file. Keep your new privates under the `sh_` prefix (`Sh`/`sh` for types and
    definitions; ⟨check: unused in the tree⟩).

### Checkpoints (for a partial; ground rule 9)

1. **The overlay and the inclusion** (`hr_inclusion` copied).
2. **`D`'s first three phases** as contracts: the validation, the radius, the initial record.
3. **`D`'s run and verdict**: the runner at `U₀`, its exits read through the window run.
4. **`D`'s space and the packaging**: `L_D ∈ SPACE g`.
5. **The normalization and the window**: `U₀`'s run on the padded code stays in the window and
   halts within `configBound`.
6. **`space_hierarchy`.**
7. **`LOGSPACE_ssubset_PSPACE`.**
8. **`SPACE_linear_ne_NP`.**

Each may land alone. **Add no new admission.** **One checkpoint, one commit, one zip, delivered at
once.**

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**, each on a
frozen copy of its commit (`git worktree add <dir> HEAD`). **Semantic duplication (required):** for
every private lemma you add, search for a published declaration that states it or a
generalization, in the tree and on every open PR branch, by name and by statement (`git grep`), and
by an `exact?` or `apply?` probe; `REPORT.md` lists the search and result per private. **The
population** is ⟨N⟩ files (`screen-population.txt`): your file; the files the route cites; the known
hazards (`TimeHierarchy/Diagonal`, `TimeHierarchy/Separation`, `SpaceComplexity/Savitch`,
`ClassNP/Nondeterminism` for the padding precedent). **The base** is
`campaign/fills/b6/logs/b6-fill-hierarchy-screen-base.txt`: ⟨…⟩. A new cross-file pair with an
owned-file declaration on one side is listed with one disposition (idiom; re-derivation of a
published lemma: cite it instead; re-derivation of another file's private: keep yours and request
a promotion); a pair at 90% or more is a copy. `REPORT.md` carries **"new copies: none"** or lists
each pair, and ships both full outputs.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only**; **never `lake build`**, never
  the unfiltered `lake exe cache get`; `scripts/lean_check_tree.sh` for every check, one Lean
  process at a time (a screen may run beside one). The cache tool's own compilation inside
  `lake exe cache get` is outside the one-Lean rule. **A process deviation never ends the item.**
- **Bootstrap** from `campaign/fills/b6/orders/b6-fill-hierarchy.txt` (⟨N⟩ modules), right after
  branching, logging each module's time and maximum memory. **The base sorry-warning set** has
  ⟨N⟩ entries in ⟨N⟩ modules; yours are `Hierarchy`'s four. Record the base list by name first.
- **Final checks:** `Hierarchy`: zero errors, exactly one sorry warning (`space_universal`'s; for a
  partial, also the open targets'); every other module: zero errors and the base's sorry warnings;
  the import probe re-run, 0 errors; after every proof edit, the order list's tail from your module
  on.
- **Axiom prints** for the three targets and every new private: within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL
  (base ⟨…⟩), and `scripts/style_lint.py` on your file; no new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your three targets: `space_universal` (F6, your file),
`Complexity.savitch` (`SpaceComplexity/Savitch`), and the rest of the list in
`campaign/fills/b6/logs/b6-fill-hierarchy-base-sorries.txt`.

## REPORT.md checklist

- [ ] The preflight, the roots and the cache fetch (with the logs), the bootstrap with per-module
      time and memory, the base blob check.
- [ ] The overlay only; nothing outside regions (a)–(d); `space_universal` untouched.
- [ ] The checkpoints reached (1–8), one zip each; the base hash and the ancestor check.
- [ ] Every new declaration with its role; `D`'s phases and tapes; the radius; the runner's call.
- [ ] `D`'s space bound, term by term, and its uniformity in the code part of `x`; the constant
      `A` of the contradiction.
- [ ] The base sorry list by name; each edge case with the lemma that covers it.
- [ ] Promotion candidates and escalations, or "none"; the proposed `**Implementation.**`
      paragraphs.
- [ ] Rule 10: the citations outside your file (an elaborated-constant walk), the probe re-run,
      **the seal test with its controls and both raw outputs**, the inspection table. Rule 11: a
      grep of your diff for the six R3 rows and other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, the semantic search per private,
      "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **The simps field equations are pointwise**: `funext` before `rw`, or the step closes by
  unfolding and the seal rejects it.
- **`logSpace` is not `Nat.log 2`**: `logSpace n = Nat.log 2 n + 1` (`logSpace_eq`), so it is at
  least `1` everywhere; the floors come from `spaceConstructible_iff`'s first conjunct.
- **`SPACE` absorbs constants** (`SPACE.mono_const`): prove the bound `c · (g n + 1)` and absorb
  it by `g`'s floor, not by unfolding `SPACE`.
- **`PSPACE` has no reading of its own here**: reach it through `space_poly_subset_PSPACE`.
- **No core or Mathlib definition is reduced outside `rfl`, `decide` or `show`.** `omega` with
  products as atoms (`ring` first). The linter needs a literal "Proof sketch" before every
  `sorry` (partial only).
