# Ch3–4 fill campaign — C1, wave 1, UN continuation 1: the universal NDTM's setup (`Turing.exists_timed_universal_NDTM`, `Diagonalization/NTimeHierarchy.lean`)

> **Megafill A, item 2 of 3** (cover brief `megafill-A.md`; addendum v2.4, Part 3). The
> preflight, the toolchain, the clone and the cache are done once for the whole queue. For this
> item: create its branch from the shared base (below), make your first edit, **re-bootstrap your
> order list** (item 1 changed `NDCodeSimulator`, upstream of your file, on its own branch), then
> follow this brief. **Budget: 3 hours** from your branch's creation; then deliver this item's zip,
> partial if need be, and start item 3.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (phase P3.3's statement gate, C1's design §2.2, §2.5) and
    **the C1-A assembly gate's ruling 2**: UN's setup is your fill obligation, its hypothesis
    carried verbatim below;
  - **the first round's landing (PR #129):** BF, H′ and S proved; target 1 open on escalation UN-1;
    the review `campaign/fills/c1/reviews/universal-1/REVIEW.md`, with its verified phase-3 lemma
    and its two findings (UN-1, F2);
  - **the API PR that answers them (PR #132; gate 50, `campaign/gates/50-un-u2s-api/`, PASS):**
    `FinTM.pairExtractTM_fst_run` and `_run_budget` (the extractor's complete halting
    configuration) in `Build/Primitives`, and `FinTM.bufferedSecondCfg_workTapes_cast` /
    `_workTapePos_cast` (the buffered composite's fields at its own index type) in `Simulation`;
  - **the exhaustive replay** `FinNDTM.exists_exhaustiveDecider`, proved (PR #136), so BF depends on
    target 1 and the core only;
  - **the rewind row** (PR #138): `Turing.rewindTM` and its framed run
    `Turing.rewindTM_run_ofCfg` (`Build/Rewind`), and its API gate `campaign/gates/55-rewind-row/`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.4**: Part 1, the resources and the cache for the Mathlib roots only; **Part 3, the
    megafill**, under which this session runs), and the copy-text screen v3
    `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/c1/inputs/c1-fill-universal-cont1/`): the overlay
    (your file with the verified phase-3 lemma), the import probe and the screen population; the
    order list `campaign/fills/c1/orders/c1-fill-universal-cont1.txt`, the base sorry set, the
    screen base and the pre-ship log (`campaign/fills/c1/logs/c1-fill-universal-cont1-*`).
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of
  `campaign/standards/fill-environment-addendum.md` and its Part 3): the preflight, the
  toolchain, the clone and the cache for the whole queue's Mathlib roots. If Lean cannot start,
  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-universal-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-universal-cont1.zip`, with
  `REPORT.md` and the full modified source; a `git format-patch` series against your base and a
  git bundle whose only prerequisite is your base; the bootstrap and final sweep logs and the
  axiom log; both screen outputs; and `SHA256SUMS`.
- **Checkpoint zips.** After each phase below, commit and write
  `fill-c1-universal-cont1-cp<N>.zip` with the same contents as of that commit.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #137** (`2ff214c5`, #137's merge; #140,
  #138, #133, #134 and #136 merged before it). **In flight, merging after it and invisible to
  it:** #139 (`Build/StepClock`, upstream of `ClassNP/ExhaustiveReplay` but not of anything you
  cite), #143 (`Build/ZoneRebalance`), the seam layout's landing, MIG-12's fill
  (`Build/CfgRecord`); in this session, on their own branches, R (`NDCodeSimulator`, upstream of
  your file: you cite its target's statement) and the canonizer (`CodeSimulator`); on another
  host, U2-S, F5 and G4. Cite nothing that merges after your base. Every probe and measurement
  below was run on the overlay against the olean snapshot `oleans-lg4c2` (the tip's merged-tree
  replay).
- **Your first edit makes your file equal to the overlay** (`NTimeHierarchyOverlay.lean.txt`):
  the base file with one private lemma, `un_universal_of_setup`, inserted at your home (b) before
  target 1's docstring, and the import of `Build/Rewind` (region (a)). **Line numbers below are
  the overlay's** (485 lines: target 1 at line 277, its `sorry` at 282; `ntime_hierarchy` at
  415).
- **Your file's other stub,** `Complexity.ntime_hierarchy`, is C1-E's and stays sorried.

## What this is

**C1's universal NDTM at linear overhead** [AB09, Exercise 2.6]. One target, frozen:
**`Turing.exists_timed_universal_NDTM`**: a universal NDTM `UN` with, per code `α`, a constant
`C` such that on `⟨⟨bits t, α⟩, x⟩` every branch halts within `C·(t + 1)` and `UN` accepts within
`C·(t + 1)` iff the coded machine accepts `x` within `t`.

**Where it stands.** The derivation of the target from the setup is done:
**`un_universal_of_setup`** (the overlay; the first round's review checked it sealed, and it was
re-checked at your base) proves the target from the setup hypothesis below and the interpreter
core, with `C := C_P + C_R + 13`. **The target is then one line:
`exact un_universal_of_setup c <setup>`.** What is open is the setup `P`, which the first round
stopped on (UN-1): no published lemma described the extractor's tapes after its run. PR #132 now
publishes them.

**Proved modulo, exactly:** `Turing.exists_ndInterpreterCore` (R, through the assembly);
`Complexity.ntime_hierarchy` for H′ and S. (The writer `Turing.ndWriterTM_run_block` is proved,
PR #123.)

**Your setup obligation, verbatim** (the C1-A gate's ruling 2: its quantifier order, its first
exit, its complete cleanup, no input-length term in its bound). For the core's tape count `K` and
stream tape `jR`, build `P`:

```lean
(hsetup : ∀ (K : ℕ) (jR : Fin K), ∃ (k : ℕ) (ι : Fin K ↪ Fin k) (cap : Fin k),
  cap ∉ Set.range ι ∧ ∃ (SP : Type) (_ : Fintype SP) (_ : DecidableEq SP)
    (P : MultiTapeTM k Bool SP) (pexit : SP),
    ∀ α : List Bool, ∃ CP : ℕ, ∀ (x : List Bool) (t : ℕ),
      ∃ TP ≤ CP * (t + 1), ∃ blk : ℤ → Option Bool,
        (∀ p : ℤ, blk p ≠ none ↔ 0 ≤ p ∧ p < t) ∧
        P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) TP =
          ⟨some pexit, 1, Function.update (fun _ _ => none) (ι jR) blk, fun _ => 0, []⟩ ∧
        ∀ u < TP,
          (P.runFrom (P.initCfg (pairEncode (pairEncode (Nat.bits t) α) x)) u).state ≠
            some pexit)
```

**The published lemmas your route reads** (ground rule 10):
- **the header, completely:** `prefixCanonTM`, `prefixCanonTM_eq`, **`prefixCanon_run`** (the
  canonizer's configuration at `3|u| + 4 + τ` as `bufferedSecondCfg universalPrefixTM F (F's run) b
  ⟨2|u| + 3, _⟩ …`, `u` the input's first component), **`FinTM.pairExtractTM_fst_run`** (`F =
  pairExtractTM true false` on `u = pairEncode (bits t) α` first halts at exactly `4|bits t| + 5`
  in `⟨none, ⟨2|bits t| + 3, _⟩, fun _ => bufferTape (bits t), fun _ => |bits t|, bits t⟩`), and
  **`FinTM.bufferedSecondCfg_workTapes_cast` / `_workTapePos_cast`** with `FinTM.tapeBlocks_left`,
  `_buffer`, `_right` (the composite's tapes at its own index type: the code buffer holds
  `bufferTape u` with its head at `2|bits t| + 2`, the extractor's tape `bufferTape (bits t)` with
  its head at `|bits t|`); `length_pairEncode`, `pairEncode_eq`, `pairDecode_pairEncode`;
- **the capture:** `embedSilentRetTM`, `embedSilentRetTM_run`, `MultiTapeTM.exists_first_halt`,
  `embedSilentCfg_cap` (the output `bits t` on `cap`, head at `|bits t|`),
  `embedSilentCfg_selected_tape` / `_selected_pos`, `embedSilentCfg_unselected`,
  `embedSilentCfg_inputPos`, `embedSilentCfg_output`;
- **the block:** `expandTM`, `expandTM_run_ofCfg` (`d` copies of `pat` from `pos` on tape `i`,
  the counter left all `true`), with `counterValue_bits`, `counterLoopCfg`'s fields;
- **the cleanup:** `skipTM_run_ofCfg` (a head inside a word moves one cell past its right
  delimiter), `skipBackTM_run_ofCfg`, `clearTM_run_ofCfg` (a delimited word at the head becomes
  blank), and the input rewind `FinTM.rewind_heads` over a private leaf of yours built from
  `FinTM.controlAction` (`controlAction_apply`);
- **composition:** `seamCompTM_run_ofCfg`, `seamReleaseTM_firstReturn`, `phaseHostTM_run`, with
  `Cfg.ofWords`'s fields;
- **the model:** `MultiTapeTM.initCfg_eq`, `Cfg.init_*`, `MultiTapeTM.step_of_some`, the run
  algebra,
  `Action.apply`'s fields, `Cfg.mapState`'s fields.

**Read first:**
- the target's docstring, whose sketch is binding where this brief does not refine it;
- `un_universal_of_setup` in the overlay, and consumer probe 1 behind it;
- the first round's review, **(d)** (UN-1 and F2) and **(g)** (the continuation's route);
- gate 50's note 7: the API closes the two interface gaps; the transport through
  `prefixCanonTM_eq`, the normalization inside the capture, the cleanup, the assembly and the
  ledger are yours.

**Pre-ship check** (maintainer, at the base;
`campaign/fills/c1/logs/c1-fill-universal-cont1-preship.log`):
- **The overlay** elaborates with exactly the file's two sorry warnings (target 1, line 277, and
  `ntime_hierarchy`, line 415).
- **The seal** of `un_universal_of_setup`: with `guessRunTM`, `embedSilentTM`, `streamStartCfg`,
  `NDTM.runWith`, `NDTM.initCfg`, `FinNDTM.AcceptsWithin`, `NDTM.HaltsWithin`,
  `CodeNDTM.toFinNDTM` and `pairEncode` `local irreducible`, it elaborates; the control (`rfl` on
  `streamStartCfg`'s output) fails.
- **The import probe** (`C1UniversalCont1ImportProbe.lean.txt`, 95 `#check`s: the first round's 53,
  the 39 names above and the rewind row's three): 0 errors, 0 warnings. Re-run it after your
  delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line (overlay) | Target |
|---|---|---|
| 1 | `Diagonalization/NTimeHierarchy.lean:277` | `Turing.exists_timed_universal_NDTM` |

Your regions:
- **(a) imports:** exactly one, `import TCSlib.Complexity.TuringMachine.Build.Rewind`, after the
  existing imports (it is in the overlay).
- **(b) one home**, for your `private` declarations: in `namespace Turing`, before target 1's
  docstring, holding `un_universal_of_setup` first. `private` only, and no `section`, `open` or
  `variable` that leaks past one.
- **(c) the body**, target 1's `sorry`.
- **(d) for a partial only, a paragraph headed `**Implementation status.**` at the end of target
  1's docstring.** It is public-facing library text: what is proved and what is open, in
  mathematical terms, with no campaign labels, no dates and no session narrative. The same holds
  for your new docstrings; provenance goes in `REPORT.md`.

Frozen: the module header and docstring, BF, H′, S, `ntime_hierarchy`'s statement and `sorry`,
target 1's statement and its docstring before (d), and every other file.

### Route (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **The target** is `exact un_universal_of_setup c hsetup`: build `P` and prove `hsetup`.
- **The setup `P`**, on `k ≥ K + 1` tapes (`ι` selects the core's `K`; `cap` and the scratch tapes
  are outside or reused and cleaned). Its phases, joined by `seamCompTM_run_ofCfg` or
  `phaseHostTM_run`:
  1. **The header pass:** `prefixCanonTM (pairExtractTM true false)` on the input, **embedded
     silently with a first live return** (`embedSilentRetTM`, `embedSilentRetTM_run`,
     `exists_first_halt`), its output `bits t` captured on `cap`. **Read its complete final
     configuration** through `prefixCanonTM_eq`, `prefixCanon_run`, the cast pair and
     `pairExtractTM_fst_run`: on the canonizer's two tapes (embedded on two scratch tapes) the code
     buffer `bufferTape u` with its head at `2|bits t| + 2`, and the extractor's tape
     `bufferTape (bits t)` with its head at `|bits t|`; the native input head at `2|u| + 3`; time
     `3|u| + 4 + (4|bits t| + 5)`, independent of `x`.
  2. **The block:** `expandTM` with `pat = [true]` (or any nonblank one-symbol pattern) turns the
     counter word `bits t` into exactly `t` nonblank cells on `ι jR` from cell `0`
     (`counterValue_bits` gives the value `t`). Its counter is left all `true` at the same width.
  3. **The cleanup**, so that `P` exits exactly at the hypothesis's configuration (every tape but
     `ι jR` blank, every head at the origin, the input head at `1`, empty output), and first
     visits `pexit` there:
     - each scratch word (the code buffer `u`, the extractor's `bits t`, the capture, the
       expansion's all-`true` counter) is cleared by `clearTM_run_ofCfg` from its first cell. Bring
       a head inside or just past a word to its first cell by `skipTM_run_ofCfg` then
       `skipBackTM_run_ofCfg` (the skip ends one past the right delimiter, which is what the skip
       back needs), or by `rewindTM_run_ofCfg` (from anywhere in the word or just past it, the
       empty word included);
     - the block's head returns to `0` the same way;
     - the native input head returns to `1` by your input-rewind leaf (`FinTM.rewind_heads`; every
       work head stays);
     - the output stays empty: every phase is silent.
  4. **The ledger:** `O(|bits t| + |α| + t + 1) ≤ C_P·(t + 1)` per code, using
     `length_bits_le_self`; **no `|x|` term**: the header pass never reads past the header, and the
     input rewind costs `2|u| + 5`.
- **Edge cases that must stay true:** `t = 0` (`bits 0 = []`, the block is empty, `blk` is
  everywhere blank); `x = []` (the header is the whole input); `α = []`.
- **Promotion candidates** (notes only, in `REPORT.md`): the header's first-component pass with
  its cleanup (R's startup and B5a's H1 need it too); the first-halt capture; your input-rewind
  leaf.

## Gate guidance (binding)

- **The C1-A gate's ruling 2** fixed the setup hypothesis: keep its quantifier order (`∀ α, ∃ C_P`
  before `x` and `t`), its first exit, its complete cleanup and its bound with no `|x|` term.
- **Gate 50:** cite the extractor's run and the cast pair as stated.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d). List every new declaration with its role.
2. **Statement freeze** over every landed declaration and the target.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and **continue with every item that does not depend on
   it**. Independent phases continue.
5. **No touching other sorries** (`ntime_hierarchy`'s stays). Cite proved material; never re-prove
   it.
6. **Imports.** Exactly `Build/Rewind`, region (a).
7. **One proof per shared argument.** Never write a second assembly, phase host, seam, embedding
   or prefix parser; never transcribe the deterministic hierarchy's corollaries or
   `UniversalStartup`'s or `NDCodeSimulator`'s privates. The input-rewind leaf is allowed.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts.
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each
   with a literal "Proof sketch") and the target's axiom walk.
10. **The pinned base, and no unfolding (user, 2026-10-16).** Cite only declarations public at
    your base, and your file's own privates. **Never unfold a definition of another file**, and no
    definitional closure either; read every definition through its published lemmas. In
    particular, read `prefixCanonTM` only through `prefixCanonTM_eq`, `prefixCanon_run` and
    `prefixCanon_complete`, and the buffered composite only through the cast pair and the
    `tapeBlocks_*` projections. **Self-check:** a seal test with a control that fails under it, and
    an inspection of every `rw`/`simp`/`simpa`/`unfold` argument (a `simp` given a definition
    explicitly unfolds it even when sealed). If a fact has no published lemma, stop on that item
    and escalate, naming the lemma.
11. **MIG-1 compatibility.** Cite none of the six R3 canonical rows; cite no private declaration of
    another file; keep your new privates under `un_`.

### Phases (for a partial; ground rule 9)

1. The header pass, captured, with its complete final configuration read.
2. The block.
3. The cleanup and the exit configuration; the ledger.
4. `hsetup`, and the target by `un_universal_of_setup`.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**.
- **The population** (`campaign/fills/c1/inputs/c1-fill-universal-cont1/screen-population.txt`,
  11 files): the first round's six (your file, `Build/NDHost`, `TimeHierarchy/Diagonal`,
  `UniversalStartup`, `NDCodeSimulator`, `ClassNP/ExhaustiveReplay`) and, for this round's route,
  `Build/Primitives` (the extractor), `Simulation` (the composite), `Build/Embed`,
  `Build/CounterLoop` (the expansion) and `UniversalK` (U2-S's startup reads the same composite).
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths. **The base** is
  `campaign/fills/c1/logs/c1-fill-universal-cont1-screen-base.txt`, measured on the overlay:
  **603 declarations, 450 pairs, 123,003 characters** (MEASURED). Run the before screen after
  your first edit: it must equal the base.
- **No new cross-file pair** with an owned-file declaration on one side. **Known hazards:** the
  chapter-1 startup's cleanup (`UniversalStartup`), U2-S's startup (`UniversalK`), R's header
  capture (`NDCodeSimulator`'s `ic_header_capture`, private). Follow their pattern, never
  transcribe it. A pair at 90% or more is a copy.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for your roots only** (addendum v2.4, fetched once for
  the queue;
  33 roots at the overlay); **never `lake build`**, and never the unfiltered `lake exe cache get`.
  Use
  `scripts/lean_check_tree.sh` for every check.
- **Re-bootstrap** (addendum Part 3, item 3.2) from
  `campaign/fills/c1/orders/c1-fill-universal-cont1.txt` (75 modules), after your first edit.
  **The base sorry-warning set has 26 entries in 12 modules**
  (`campaign/fills/c1/logs/c1-fill-universal-cont1-base-sorries.txt`); yours is target 1.
- **Final checks:** your file: zero errors, exactly `ntime_hierarchy`'s sorry warning (for a
  partial, plus the open declarations'); every other module of the order list: zero errors, sorry
  warnings exactly the base's minus yours; the import probe re-run, 0 errors.
- **Axiom prints** for the target and every new private: within
  `[propext, Classical.choice, Quot.sound]` plus the `sorryAx` of the cited stubs (the core;
  `ntime_hierarchy` for H′ and S), and nothing else.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL
  (base: 0 FAIL, 1 WARN over 5 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The session's shared preflight and cache numbers (quoted from its logs), and this item's
      bootstrap.
- [ ] The target proved (or the phase reached), modulo exactly the cited stubs; the base hash and
      the ancestor check; the checkpoint zips.
- [ ] The overlay as the first edit, byte for byte; nothing else outside regions (b)–(d).
- [ ] Every new declaration with its role; the setup's tapes and phases as built.
- [ ] The setup's constant `C_P` and its ledger; target 1's `C`.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, the probe re-run, the seal test with its
      control, the inspection. Rule 11: the R3 rows and other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **`pairEncode` doubles its first component.** The header `u = pairEncode (bits t) α` is itself
  the input's first component, so `prefixCanon_run` runs the extractor on `u`, and
  `pairExtractTM_fst_run` then reads `bits t` out of it.
- **`Cfg.inputPos` is shifted by one.** The buffered composite's buffer head is the source's input
  position minus one (`tapeBlocks heads (inputPos − 1) …`): the extractor's `2|bits t| + 3` puts
  the code-buffer head at `2|bits t| + 2`.
- **The composite's index type.** Read its tapes at `i : Fin (bufferedCompTM M₁ M₂).k` through the
  cast pair; the older `bufferedSecondCfg_workTapes` at `Fin (M₁.k + (1 + M₂.k))` does not match
  there without unfolding.
- **The simps field equations are pointwise** (`Cfg.mapState_*`, `embedSilentCfg_*`, `Cfg.init_*`):
  `funext` before `simp`/`rw`, or the step closes by unfolding and the seal rejects it.
- **`prefix` is a reserved keyword**; do not name a hypothesis `prefix`.
- **The setup's exit configuration is a structure literal.** Prove it with `Cfg.ext` and the field
  equations.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
