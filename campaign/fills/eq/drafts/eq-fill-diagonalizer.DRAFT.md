# Ch3–4 fill campaign — E-D, the lazy diagonalizer (`Turing.NTimeDiag.exists_diagonalizer`, `Diagonalization/NTimeDiagonalizer.lean`)

> **DRAFT** (maintainer, 2026-11-04), drafted against PR #176's head `cecd76a0` (E-Q cont1's
> landing; gate 87 passed, 2026-11-04; it merges with the campaign merged in, after
> `replay-leqc2`). Issues after #176 merges; ⟨…⟩ marks what the pre-ship fills in at the issue
> commit (line numbers, counts, probes). **Agent: Claude** (user, 2026-11-04).
>
> **Maintainer's landing item (not the fill's):** gate 87's finding 2, ruled 2026-11-04: in E-D's
> landing PR, `qy_call_bound`'s local `hb` becomes `have hb := Turing.length_bits_le_self (f a)`
> (ledger NB-1). E-D's fill gate covers it. The brief keeps `qy_call_bound` frozen for the fill.

> **A single fill** (addendum v2.6, Parts 1 and 2; Part 3, the megafill, does not apply, except
> its one-Lean rule and its no-stop rule, items 5 and 7, which "Environment and verification"
> restates). Deliver a checkpoint zip after each checkpoint: the session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement**: the C1-E statement gate (gate 39, round 2,
    `campaign/gates/39-ntime-diag-statements/`);
  - **E-Q, landed and proved** (PR #173, gate 83; PR #176, gate 87): `exists_queryTM` and its
    private leaves in your file, among them the framed length comparison `qyCmpTM` (`qy_cmp_run`),
    the repeating emitter `qyEmitTM` (`qy_emit_run`), the writer word `qy_writer_word`, the clocked
    install call (`QyClockSpec`, `qy_clocked_call`) and the hosted-phase segments (`qy_hosted*`).
    Same-file privates are citable;
  - **the guess-then-run host** `Turing.guessRunTM` (`Build/NDHost`) with `guessRunTM_haltsWithin`
    and `guessRunTM_accepts_iff`; **the interpreter core** `Turing.exists_ndInterpreterCore`
    (`NDCodeSimulator`); **the step clock** `Turing.exists_stepClockTMVia` (`Build/StepClock`);
    **the virtual-input host** `Turing.vhostSilentTM` and **the capture wrapper**
    `Turing.embedSilentTM` (`Build/VirtualInput`, `Build/Embed`); the input call
    `Turing.FinTM.exists_inputCallTM`; `Turing.expandTM_run_ofCfg`; the pair extractors;
    `Complexity.timeConstructible_iff` (A1);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.6**), and the copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/eq/inputs/eq-fill-diagonalizer/`): ⟨the import probe,
    the route probe with its seal controls, the duplication probe, the import overlay and the screen
    population⟩; the order list `campaign/fills/eq/orders/eq-fill-diagonalizer.txt`, the base sorry
    set, the screen base and the pre-ship log (`campaign/fills/eq/logs/eq-fill-diagonalizer-*`). The
    route's design note is `campaign/items/c1/c1e/ED-route-design.md`, **with its revision of
    2026-11-04** (after E-Q cont1).
- **Before anything else, run Part 1 of the addendum**: the preflight, with its stop rule
  (E-RES). Fetch the cache for your roots only (⟨roots⟩); never run the unfiltered
  `lake exe cache get`. If Lean cannot start, follow Part 2 exactly. **If Lean never runs, do not
  draft proofs blind**: deliver the environment report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/eq-diagonalizer @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
  # must print ⟨the blob at the issue commit⟩
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-eq-diagonalizer.zip`, with
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle whose only prerequisite is your base, the environment logs (`evidence/logs/`), the
  bootstrap and final sweep logs with **each module's time and maximum memory**, the axiom log, the
  seal test's source, its controls and both outputs, both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-eq-diagonalizer-cp<N>.zip` (`N` 1 to 8). Deliver the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign's tree after #176** (E-Q cont1). Lines in this brief
  are those of your base's tree, where `NTimeDiagonalizer.lean` is ⟨5,432⟩ lines (⟨22⟩ public, ⟨214⟩
  private).
- **The overlay is your first edit** (region (a)): add, after the `Build/WordTests` import, exactly
  `import TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `import TCSlib.Complexity.TuringMachine.NDCodeSimulator` and
  `import TCSlib.Complexity.TuringMachine.Build.VirtualInput` (13 modules join the closure; no
  cycle). The pre-ship elaborated the file with them: E-Q's proofs unchanged, exactly the target's
  sorry warning (`NTimeDiagonalizerOverlay.lean.txt`).
- **In flight:** ⟨at the issue commit⟩.

## Parallel batches this round

None in `NTimeDiagonalizer.lean`. `NTimeHierarchy` imports your file and cites only the target's
statement, which is frozen; `Complexity.ntime_hierarchy` is proved from it. NF
(`ClassNP/NDNormalForm`) may be running; it never touches your file.

## What this is

**The lazy diagonalizer** ([AB09, proof of Theorem 3.2 and Figure 3.1]). For time-constructible `f`,
`g`, an effective scheme `c` and an exponential-time decider of the coded machines' bounded
acceptance (`hBF`), a nondeterministic machine `D` and a uniform `K` with: every branch of `D` on
every input halts within `K · (g |x| + 1)`; per code `α` a constant `C` such that, on `1ⁿ` with
`n ≥ 3` in a stage of `α`, in the middle `D` accepts `1ⁿ` iff (up to the stated slack) the coded
machine accepts `1^{n + 1}`, and at the top `D` accepts `1ⁿ` iff the coded machine does **not**
accept the stage's bottom `1^{ℓᵢ + 1}` within `T* = budget f ℓᵢ` (the statement, line ⟨5406⟩).

**Where it stands.** The body is `sorry`. Every host is proved, and E-Q's query is proved in your
file. **Proved modulo, exactly:** none. **A complete delivery has no `sorryAx` in the target.**

**Read first:** the route note with its revision (`ED-route-design.md`); the target's docstring
(lines ⟨5346–5405⟩), whose sketch this brief refines; `Build/NDHost.lean`'s `guessRunTM` family
(its docstrings name the setup hypotheses); E-Q's leaves named above; `exists_ndInterpreterCore`'s
statement; `Build/VirtualInput.lean`'s header.

## Owned regions and targets (modify these and nothing else)

`TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean`:
- **(a)** the imports: add exactly the overlay's three;
- **(b)** new private declarations after `exists_queryTM`'s proof (line ⟨5345⟩) and before
  `exists_diagonalizer`'s docstring (line ⟨5346⟩), in sections of your own. Every new declaration
  has a docstring, and every proof over 20 lines a literal `**Proof sketch.**` (`policy.md` §3);
  docstrings are public-facing (no campaign labels, dates or session narrative; provenance in
  `REPORT.md`); a hand-built machine's docstring says which public row it is not;
- **(c)** the target's body (line ⟨5431⟩, `sorry`);
- **(d)** the status text: the module docstring's line ⟨70⟩ ("(sorried; C1-E's second fill)"), and
  in the target's docstring the labels "(C1-E; …)", "the P3.3 gate's round 2" and "(the statement
  gate, finding 1)". Rewrite them as public-facing text; propose an `**Implementation.**` paragraph
  in `REPORT.md`; the maintainer lands it.

**Target:** `Turing.NTimeDiag.exists_diagonalizer` (line ⟨5406⟩), its statement frozen. E-Q's
declarations and every other statement are frozen too.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **`D` is `Turing.guessRunTM P pexit j Q qentry acc rej`**, bundled as a `FinNDTM`: one guessed
  block of `m = g n + L` cells (`L = |bits (g n)|`), its first `g n` bits the stream `s`, its last
  `L` the budget word `w_b`. **Halting** is `guessRunTM_haltsWithin`; **acceptance** is
  `guessRunTM_accepts_iff` (not `guessRunTM_silent_spec`: your setup is not clean, it keeps the
  query word and the counter). Never compose `phaseHostND` yourself, and never re-prove a writer,
  handoff or acceptance lemma.
- **`P`, the deterministic setup:** the query call on the native input (released; `exists_queryTM`'s
  machine through `FinTM.exists_inputCallTM`), `g`'s witness call (released; through
  `timeConstructible_iff`), the block (`expandTM` of `bits (g n)`, then a copy of `bits (g n)`), the
  clock's counter `bits (g n)` on its own tape, and rewinds. Its first exit `TP ≤ P₀ · (g n + 1)`,
  uniform.
- **`Q`, the deterministic run**, a phase host (`Turing.phaseHostTM`) over:
  1. **the flag:** read the query word's first cell: blank (`n < 3` or not unary) → `rej`; `true` →
     the top; `false` → the middle (a one-step own leaf);
  2. **the middle's preparation** (route note, revision), **from published rows and E-Q's leaves,
     with no new leaf:** copy `w_b` off the block and clear its cells (the copy and clear rows);
     expand it to `1^b` (`expandTM` with the pattern `[true]`: `expandTM_run_ofCfg` takes any
     little-endian word, top zeros included); compare `1^b` with the stream `s` (`g n` nonblank
     cells) by `qyCmpTM`: `gt` → `rej`; normalize to `bits b` by the published `lengthBits` install
     call on `1^b`; extract `α` by one hosted call of the second-component extractor on the query
     word's tail; write the core's input `⟨⟨bits b, α⟩, 1^{n + 1}⟩` onto a buffer by three
     `qyEmitTM` emissions (`bits b`, each bit four times, then `[false, false, true, true]`; `α`
     doubled, then `[false, true]`; `1^{n + 1}`) **run under the capture wrapper `embedSilentTM`**,
     which records every emission on its capture tape and emits nothing;
  3. **the middle's run:** the step clock (counter `bits (g n)`, allowance `g n`) over
     `vhostSilentTM R`, `R` the interpreter core, stopping at its `accept` or `reject`:
     `finish accept` → `acc`; `finish reject` and `timeout` → `rej`;
  4. **the top's run:** the clock over `vhostSilentTM BF` on the query word's tail
     `⟨⟨bits T*, α⟩, 1^a⟩`, stopping at `BF`'s halt; then read the captured bit: `[false]` → `acc`,
     anything else, or a `timeout`, → `rej`.

  **`Q` is silent:** both simulators are hosted silently and every other phase emits nothing, so
  the run's output is empty at its verdict, as `guessRunTM_accepts_iff` requires.

### The route (binding where it names a row; the rest is the recommended shape)

**Time, uniform.** `TP + 2m + T + 11` with `m ≤ 2 (g n + 1)` and `T` the preparation
`O(g n + 1)`, the clock's `5 g n + 2L + 2` and the dispatches; so `K` is uniform and
`guessRunTM_haltsWithin` gives `D.tm.HaltsWithin x (K · (g |x| + 1))` on **every** input (off unary
inputs the query is `[]` and `Q` rejects at once).

**The middle, per code `α`** (`C = max 1 (max C_R C_BF)`):
- **Completeness:** an acceptance of `1^{n + 1}` along `v`, `|v| = t'`, `C (t' + 1) ≤ g n`: take the
  stream `v` padded to `g n` bits and `w_b := bits t'` padded with zeros to width `L`. The test
  passes, the core runs on `⟨⟨bits t', α⟩, 1^{n + 1}⟩` and accepts at `T ≤ C_R (t' + 1) ≤ g n`,
  inside the allowance (`finish accept`); `guessRunTM_accepts_iff` gives the accepting branch at the
  budget `K (g n + 1)`.
- **Soundness:** an accepting branch has a stream `s` and `b ≤ g n` whose core run accepts inside
  the allowance, so the coded machine's branch along `s.take b` halts with `[true]` (the core's
  clause): `AcceptsWithin (1^{n + 1}) b`, then `AcceptsWithin.mono` to `g n`.

**The top:** `BF` completes within `C_BF 2^{C_BF (T* + 1)} ≤ n ≤ g n`, inside the allowance, so `D`
accepts iff `BF` answers `[false]`; every stream gives the same verdict.

**The interpreter's prefix clause is not used** (its `|x|` term carries the per-code constant, which
the uniform `K` cannot absorb when `g n = n`).

**Edge cases that must stay true:** `n ≤ 2` and non-unary inputs (the query is `[]`: `rej`); a
budget word above `g n` (`qyCmpTM`'s `gt`: `rej`); `b = 0` (`1^0` is empty: `qyCmpTM` and the
`lengthBits` call on the empty word); a stream shorter than an acceptance (the core rejects or times
out: `rej`); `BF` halting with a word other than `[false]` or `[true]` (`rej`); the clock's
`timeout` in either run (`rej`).

## Gate guidance (binding)

- **Gate 39** (the C1-E statement gate, round 2): the uniform `K`; the per-code `C`; the top's
  premise `C 2^{C (T* + 1)} ≤ n`; the middle's two directions with their slack.
- **The route note and its revision:** one guessed block through `guessRunTM` (ruled); the binary
  budget, tested and normalized (ruled); E-Q's leaves cited, never copied.

## Cited infrastructure (public and proved at the issue commit; `EDImportProbe.lean.txt`, ⟨N⟩ checks)

⟨The probe's names: the host and its three lemmas; the input call and the release adapter; the step
clock; the interpreter core; the virtual-input host and the capture wrapper with their runs and
configuration equations; `expandTM_run_ofCfg`; the copy, clear and rewind rows (`_ofCfg` forms);
the pair extractors; the `lengthBits` install call; `timeConstructible_iff`; the phase host and its
equations; `AcceptsWithin.mono`; the machine model's step and action equations.⟩

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d). List every new declaration with its role.
2. **Statement freeze** over the target, `exists_queryTM` and every landed declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. The top does not depend on the middle's preparation.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Exactly the base's and the overlay's three; add none.
7. **One proof per shared argument.** Never write a second host, writer, clock, counter, call,
   seam, embedding, capture, comparison, emitter or rewind. **E-Q's leaves are yours to cite, not
   to copy**: a second length comparison or emitter in the file is a copy. Never re-walk
   `NTimeHierarchy`'s `exists_timed_universal_NDTM`/`un_setup` (the same guess-then-run pattern
   with a clean setup: cite the host's lemmas), `ExhaustiveReplay`'s `xr_` replays, or `NDHost`'s
   `wr_`/`gr_` privates.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts.
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch") and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).** As in E-Q's briefs: never unfold
    another file's definition, and no definitional closure; read `TimeConstructible` through
    `timeConstructible_iff`, `ComputesFunInTime`/`ComputesInTime` through their `_iff` readings,
    `pairEncode` through `pairEncode_eq`, the transports and hosts through their published
    equations, and `guessRunTM` only through its lemmas. Core and Mathlib definitions may reduce in
    `rfl`, `decide` or `show`, never passed to `simp`, `rw` or `unfold`. Own leaves: unfold `step`
    and `Action.apply` by `unfold`/`rw`/`simp only` (never `show`/`change`/`rfl`), preferring
    `MultiTapeTM.step_of_some` and the `Action.apply_*` equations. **Self-check by both methods:**
    a seal test (⟨the pre-ship's list⟩, the four `@[simp]` TCSlib definitions erased) **with
    controls**, and an inspection table; ship the raw outputs.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows; use the framed `_ofCfg`
    forms. Cite no private declaration of another file. Keep your new privates under the `dz_`
    prefix (`Dz`/`dz` for types and definitions; unused in the tree).

### Checkpoints (for a partial; ground rule 9)

1. **The overlay and `P`** as a contract, with its uniform bound.
2. **The flag and `Q`'s dispatch** (the one-step leaves, the phase host's redirects).
3. **The budget's test and normalization** (`expandTM`, `qyCmpTM`, the `lengthBits` call).
4. **`α` and the rewrite** (the extractor call; the three emissions under `embedSilentTM`).
5. **The two clocked, hosted runs** and their verdict readers.
6. **`Q`, `D` and the time bound `K`** (`guessRunTM_haltsWithin`).
7. **The middle and the top** (`guessRunTM_accepts_iff`, the core's clause, `BF`).
8. **The target.**

Each may land alone. **Add no new admission. One checkpoint, one commit, one zip, delivered at
once.**

## Duplication governance (binding)

As in E-Q's briefs: both v3 screens on frozen copies, one at a time under `nice -n 10`; the
semantic search for every new private (in the tree, on every open PR branch, by name and statement,
and by an `exact?` or `apply?` probe), listed per private in `REPORT.md`. **The population** is
⟨N⟩ files (`screen-population.txt`): your file; the files the route cites; the known hazards
(`NTimeHierarchy`, `ExhaustiveReplay`, `NDCodeSimulator`, `CodeSimulator`, `Build/SeamLayout`).
**The base** is `campaign/fills/eq/logs/eq-fill-diagonalizer-screen-base.txt`: ⟨…⟩. A pair at 90%
or more is a copy; every new pair gets one disposition (idiom; re-derivation of a published lemma:
cite it instead; of another file's private: keep yours and request a promotion), and `REPORT.md`
carries "new copies: none" or lists each pair. **Known hazards:** `NTimeHierarchy`'s guess-then-run
setup; E-Q's own leaves (cite them); the one-step identity (ledger RO-1); the `Cfg.mapState` idiom.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only**; **never `lake build`**, never
  the unfiltered `lake exe cache get`; `scripts/lean_check_tree.sh` for every check, one Lean
  process at a time (a screen may run beside one). **A process deviation never ends the item.**
- **Bootstrap** from the order list (⟨N⟩ modules), logging each module's time and maximum memory.
  **The base sorry-warning set** has ⟨N⟩ entries in ⟨N⟩ modules; yours is the target's one.
- **Final checks:** your file with zero errors and no sorry warning (a partial: the target's only);
  every other module the base's; the import probe re-run; after every proof edit, the order list's
  tail from your module on.
- **Axiom prints** for the target and every new private: within `[propext, Classical.choice,
  Quot.sound]`.
- **Lint:** `campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL (base ⟨…⟩), and
  `style_lint.py` on your file.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target (the list in
`campaign/fills/eq/logs/eq-fill-diagonalizer-base-sorries.txt`).

## REPORT.md checklist

- [ ] The preflight, the roots and the cache fetch (with the logs), the bootstrap, the base blob.
- [ ] The overlay only; nothing outside regions (a)–(d); E-Q's text untouched.
- [ ] The checkpoints reached (1–8), one zip each; the base hash and the ancestor check.
- [ ] Every new declaration with its role; `P`'s and `Q`'s phases and tapes; each call's release;
      each E-Q leaf cited and where.
- [ ] `K`, term by term; the per-code `C`; each edge case with the lemma that covers it.
- [ ] Promotion candidates and escalations, or "none"; the proposed `**Implementation.**`
      paragraph.
- [ ] Rule 10 (the citations outside your file, the probe re-run, **the seal test with its controls
      and both raw outputs**, the inspection table); rule 11.
- [ ] Duplication: both v3 screens, every new pair justified, the semantic search per private,
      "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **The simps field equations are pointwise**: `funext` before `rw`.
- **A call's entry may equal its exit**: run every call released (`seamReleaseTM`), as E-Q's
  review F1 found.
- **The clock's stop state** and first-stop reasoning: E-Q's `qy_clocked_call` and `QyClockSpec` are
  the model for an install call; for a hosted machine, state the clock's clauses afresh over
  `vhostSilentTM`'s run lemma.
- **No core or Mathlib definition is reduced outside `rfl`, `decide` or `show`.** `omega` with
  products as atoms (`ring` first). The linter needs a literal "Proof sketch" before every
  `sorry` (partial only).
