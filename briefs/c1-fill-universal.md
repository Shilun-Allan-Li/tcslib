# Ch3–4 fill campaign — C1, wave 1, UN: the universal NDTM with its three corollaries (`Turing.exists_timed_universal_NDTM`, `Diagonalization/NTimeHierarchy.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your four targets as gated statements** (phase P3.3's statement gate,
    `audits/ch3-p33-r2-findings.md`, and C1's design, `audits/evidence/c1/C1-design.md` §2.2, §2.5);
  - **the guess-then-run assembly** (`Build/NDHost`; the C1-A assembly gate,
    `audits/c1-assembly-statements-r2-findings.md`, CLOSED, with its rulings in
    `audits/c1-assembly-statements-resolutions.md`: **ruling 2, UN's setup is your fill obligation,
    its hypothesis carried verbatim below**), and its consumer probe 1
    (`audits/evidence/c1/assembly/r2/AssemblyConsumerProbe.lean.txt`, `probe_universal_of_setup`),
    which derives your main target from that setup and the interpreter core;
  - C1's fill plan (`audits/evidence/c1/C1-fill-plan.md`; you are wave 1's UN) and the normal form's
    move to `ClassNP/NDNormalForm` (#120);
  - **the API PRs** (the user's "Everything" rule, 2026-10-16: every definition your route reads has
    a published lemma): the specification API (PR #112), the core API (PR #116), the brief-inventory
    API (PR #118) and **the ND inventory API (PR #119: `haltsWithin_iff`, `acceptsWithin_iff`,
    `decidesInTime_iff`, `mem_NTIME_iff`, `streamStartCfg`'s and `guessRunCfg`'s fields,
    `CodeNDTM.toFinNDTM`'s fields, `Cfg.ofWords`'s fields)**;
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/c1-fill-universal/`): the import overlay, the import
    probe and the screen population. Also the order list `briefs/orders/c1-fill-universal.txt`, the
    base sorry set, the screen base and the pre-ship log (`audits/logs/c1-fill-universal-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-universal @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-universal.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #120** (`75edca6f`). The inputs commit adds
  no Lean change. Lines in this brief are those of that tree, **before** your import edit.
  `Diagonalization/NTimeHierarchy.lean` has 342 lines there (the normal form moved out in #120).
  Every probe and measurement below was run there, against the olean snapshot of #120's replay
  (`oleans-lndnf`).
- **In flight, merging after your base and invisible to it:** wave 1's other four briefs (W, the
  writer your assembly passes through; WC; E, the exhaustive decider BF cites; R, the interpreter
  core you cite); the six #118 briefs; C1-E's statements (#121), and C1's follow-up API PR (gate
  37's repairs: equations in `Build/StepBlock`, `CodeFormat`, `Encoding` and `Build/VirtualInput`;
  declarations only). Cite nothing they add.
- **Your file's other stub,** `Complexity.ntime_hierarchy` (line 299), is C1-E's and stays sorried:
  H′ and S cite its statement.

## Parallel batches this round

None in `Diagonalization/NTimeHierarchy.lean`. W, WC, E and R fill statements you cite.

## What this is

**C1's universal NDTM at linear overhead** [AB09, Exercise 2.6] (decision CH34-Q8), with the file's
three small corollaries. Four targets, all frozen:
1. **`Turing.exists_timed_universal_NDTM`** (line 162): a universal NDTM `UN` with, per code `α`, a
   constant `C` such that on `⟨⟨bits t, α⟩, x⟩` every branch halts within `C·(t + 1)` and `UN`
   accepts within `C·(t + 1)` iff the coded machine accepts `x` within `t`;
2. **`Turing.exists_ndAcceptsWithin_decider`** (line 190), BF:
   `ndAcceptsWithin_decider_of_universal` (proved, `ClassNP/ExhaustiveReplay`) applied to target 1;
3. **`Complexity.ntime_hierarchy_of_pos`** (line 313), H′: the positive-bound form of the hierarchy,
   from `ntime_hierarchy` (cited, sorried);
4. **`Complexity.NTIME_linear_ssubset_square`** (line 338), S: the showcase, from H′.

**Proved modulo, exactly:**
- `Turing.exists_ndInterpreterCore` (R, this wave);
- `Turing.ndWriterTM_run_block` (W, this wave, through the assembly);
- `FinNDTM.exists_exhaustiveDecider` (E, this wave, through BF's derivation);
- `Complexity.ntime_hierarchy` (C1-E).

Cite their statements; never their bodies.

**Your setup obligation, verbatim** (the C1-A gate's ruling 2: its quantifier order, its first exit,
its complete cleanup, no input-length term in its bound). For the core's tape count `K` and stream
tape `jR`, build `P`:

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
- **the assembly** (`Build/NDHost`): `guessRunTM`, `guessRunTM_silent_spec`,
  `guessRunTM_haltsWithin`, `guessRunTM_accepts_iff`, `guessRunTM_runWith`, `guessRunCfg_clean`, and
  `streamStartCfg`'s and `guessRunCfg`'s fields (#119); `embedSilentTM`, `embedSilentTM_runFrom`,
  `embedSilentCfg_cap`;
- **the core:** `Turing.exists_ndInterpreterCore`;
- **the setup's rows:** `prefixCanonTM`, `prefixCanonTM_eq`, `prefixCanon_complete` with
  `FinTM.pairExtractTM_fst` (the header's first component, `bits t`, at a suffix-independent time);
  `expandTM` and `expandTM_run_ofCfg` (the `t`-cell block from `bits t`, `counterValue_bits`);
  `clearTM_run_ofCfg`, `skipBackTM_run_ofCfg`, `FinTM.timed_rewind` (the cleanup); the seams and the
  phase host (`seamCompTM_run_ofCfg`, `seamReleaseTM_firstReturn`, `phaseHostTM_run`), with
  `Cfg.ofWords`'s fields;
- **the semantics:** `NDTM.haltsWithin_iff`, `FinNDTM.acceptsWithin_iff`, `HaltsWithin.mono`,
  `AcceptsWithin.mono`, `CodeNDTM.toFinNDTM_tm`, `NDTM.initCfg_eq`;
- **BF:** `ndAcceptsWithin_decider_of_universal`;
- **H′ and S:** `Complexity.mem_NTIME_iff`, `FinNDTM.decidesInTime_iff`, `NTIME.mono`,
  `Complexity.timeConstructible_poly` (`ClassNP/TMSAT`; at `C = 1` and `c = 0`, `1` it gives
  `n + 1` and `(n + 1)²` up to rewriting the function);
- the model: `MultiTapeTM.step_of_some`, the run algebra, `Action.apply`'s fields, `Cfg.mapState`'s
  fields, `MultiTapeTM.initCfg_eq`.

**Read first:**
- the four docstrings, whose proof sketches are binding where this brief does not refine them;
- **consumer probe 1** (`probe_universal_of_setup`): the derivation of target 1 from the setup and
  the core, with `C := C_P + C_R + 13`. It is maintainer evidence, not library code: **follow it**;
- the deterministic hierarchy's `Complexity.time_hierarchy_of_pos`
  (`TimeHierarchy/Diagonal.lean:531`): H′'s pattern. **Never cite or transcribe it** (it is outside
  your imports).

**Pre-ship check** (maintainer, at the base, against `oleans-lndnf`;
`audits/logs/c1-fill-universal-preship.log`):
- **The import overlay** (`audits/evidence/c1-fill-universal/NTimeHierarchyOverlay.lean.txt`): your
  file with the five authorized imports added after line 9. It elaborates with the file's five sorry
  warnings and nothing else.
- **The import probe** (`C1UniversalImportProbe.lean.txt`, 53 `#check`s): every public declaration
  this brief cites resolves from the overlay's import context. 0 errors, 0 warnings. Re-run it after
  your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `Diagonalization/NTimeHierarchy.lean:162` | `Turing.exists_timed_universal_NDTM` |
| 2 | `Diagonalization/NTimeHierarchy.lean:190` | `Turing.exists_ndAcceptsWithin_decider` |
| 3 | `Diagonalization/NTimeHierarchy.lean:313` | `Complexity.ntime_hierarchy_of_pos` |
| 4 | `Diagonalization/NTimeHierarchy.lean:338` | `Complexity.NTIME_linear_ssubset_square` |

Your regions (line numbers before your import edit; add 5 after it):
- **(a) the imports**, as your first edit: exactly
  `import TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `import TCSlib.Complexity.TuringMachine.NDCodeSimulator`,
  `import TCSlib.Complexity.TuringMachine.UniversalStartup`,
  `import TCSlib.Complexity.ClassNP.ExhaustiveReplay` and
  `import TCSlib.Complexity.ClassNP.TMSAT`, after line 9. No other import.
- **(b) two homes**, for your `private` declarations: the blank line **111** (in `namespace Turing`,
  before target 1's docstring; the setup and the assembly) and the blank line **304** (in
  `namespace Complexity`, before target 3's docstring; H′'s and S's arithmetic). `private` only, and
  no `section`, `open` or `variable` that leaks past one.
- **(c) the four bodies**, the `sorry`s on lines **167**, **198**, **317** and **340**.
- **(d) a flagged "Fill appendix (C1-UN)" paragraph at the end of each target's docstring**, before
  its closing ` -/` (lines 161, 189, 312, 337). Each closer ends a text line; put it on its own line
  after your paragraph.

Frozen: the module header and docstring, **`ntime_hierarchy`'s statement and `sorry`**, the four
statements, and every other file. The maintainer updates the module's status text at integration.

### Route (binding; the host-first rule, `policy.md` §1, `workflow.md` §2)

- **Target 1 is consumer probe 1 plus the setup.** Build `P` (in your first home), prove the setup
  hypothesis above for the core's `K` and `jR`, and conclude as the probe does: `UN` is
  `guessRunTM P pexit (ι jR) (embedSilentTM ι cap R) entry acc rej`.
- **The setup `P`**, on `k ≥ K + 1` tapes (`ι` selects the core's `K`, `cap` is outside them):
  - **the counter:** `prefixCanonTM (pairExtractTM true false)` writes `bits t`, the header's first
    component, at a time independent of `x` (`prefixCanon_complete`), captured silently on a scratch
    tape;
  - **the block:** `expandTM` turns `bits t` into a nonblank block of exactly `t` cells on tape
    `ι jR` from cell `0`;
  - **the cleanup:** clear every scratch tape (`clearTM`), return every head to the origin
    (`skipBackTM`) and the native input head to `1` (`FinTM.timed_rewind`), so that `P` exits
    exactly at the hypothesis's configuration, its first visit to `pexit`;
  - **the ledger:** `O(|bits t| + |α| + t + 1) ≤ C_P·(t + 1)` for a per-code `C_P`, with no `|x|`
    term: the prefix passes never read past the header.
- **BF** is one citation: `ndAcceptsWithin_decider_of_universal c (exists_timed_universal_NDTM c)`.
- **H′:** when `g` never vanishes, `NTIME (g + 1) ⊆ NTIME g` (`c·(g n + 1) ≤ 2c·g n`), through
  `mem_NTIME_iff`, `decidesInTime_iff` and the monotonicity of acceptance and halting; with
  `NTIME.mono` the other way, conclude from `ntime_hierarchy`.
- **S:** H′ at `f := n + 1`, `g := (n + 1)²`. Positivity is immediate. Constructibility is
  `timeConstructible_poly` at `(1, 0)` and `(1, 1)`, rewritten by `funext`. Domination is
  `A·(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`.
- **Promotion candidate** (list it in `REPORT.md`; a note only): the header's first-component pass
  and cleanup, which R's startup and B5a's H1 continuation also need.

## Gate guidance (binding)

- **The C1-A gate's ruling 2** fixed the setup hypothesis. Keep its quantifier order (`∀ α, ∃ C_P`
  before `x` and `t`), its first exit, its complete cleanup (every other tape blank, every head at
  the origin, the input head at `1`, empty output) and its bound with no `|x|` term.
- **Edge cases that must stay true of your proof:**
  - `t = 0`: the block is empty, `blk` is everywhere blank, and the writer's contract at `m = 0`
    applies;
  - `x = []`: the header is the whole input;
  - S at `A = 0`, which holds vacuously (P3.3's round-1 finding 9).

## Cited infrastructure (public and proved at the issue commit; all in `C1UniversalImportProbe.lean.txt`)

The probe's 53 names (the four targets and `ntime_hierarchy` are in your file): the core and BF's
derivation; the assembly; the setup's rows; the semantics; H′'s and S's facts; the model.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `Diagonalization/NTimeHierarchy.lean`.
   List every new declaration with its role.
2. **Statement freeze** over the four targets, `ntime_hierarchy` and every landed declaration.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated: stop on that item, record the obstruction, and
   continue with the rest.
5. **No touching other sorries** (`ntime_hierarchy`'s stays). Cite proved material; never re-prove
   it.
6. **Imports.** Exactly the five in region (a).
7. **One proof per shared argument.** Never write a second assembly, phase host, seam, embedding or
   prefix parser, and never transcribe the deterministic hierarchy's corollary.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 342 lines).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each with
   a literal "Proof sketch") and each target's axiom walk. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas (the four API PRs and the landed lemmas the probe lists).
    - **The machine model's primitives** are read through their lemmas. Unfold `step` and
      `Action.apply` only for a leaf defined in your own file.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of another file.
    - Keep your new privates under the `un_` prefix.

### Phases (for a partial; ground rule 9)

1. BF (one line), then H′ and S.
2. The setup `P` and its hypothesis.
3. Target 1, by consumer probe 1's derivation.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 6 files (`audits/evidence/c1-fill-universal/screen-population.txt`): your
  file; `Build/NDHost` (the assembly); `TimeHierarchy/Diagonal` (H′'s pattern, a hazard);
  `UniversalStartup` (the prefix canonizer); `NDCodeSimulator`; `ClassNP/ExhaustiveReplay`.
- **The screen** is `audits/evidence/retrofit/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `audits/logs/c1-fill-universal-screen-base.txt`: **67 declarations, 14 pairs,
  3,174 characters** (MEASURED).

```sh
P=audits/evidence/c1-fill-universal
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is pre-disclosed.
- **Known hazards:** `time_hierarchy_of_pos` and its inclusion (`TimeHierarchy/Diagonal`), the
  chapter-1 startup's cleanup (`UniversalStartup`). Follow their pattern, never transcribe it. A
  pair at 90% or more is a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/c1-fill-universal.txt` (**72 modules**: the upstream
  closure of your owned file, with the five imports, and of every module downstream of it, without
  the root `TCSlib`).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/c1-fill-universal.txt )
  ```

  **The base sorry-warning set has 29 entries in 13 modules**
  (`audits/logs/c1-fill-universal-base-sorries.txt`). Yours are four of
  `Diagonalization/NTimeHierarchy`'s five; `ntime_hierarchy`'s stays. Record the base list by name
  first, and report any difference.
- **Final checks:**
  1. `Diagonalization/NTimeHierarchy`: zero errors, exactly `ntime_hierarchy`'s sorry warning (for a
     partial, plus the open declarations'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours.
  3. Re-run `C1UniversalImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the four targets and every new private: within
  `[propext, Classical.choice, Quot.sound]` plus the `sorryAx` of the cited stubs (the core, the
  writer, the exhaustive decider, `ntime_hierarchy`), and nothing else.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/Diagonalization`, 0 FAIL
  (base: 0 FAIL, 1 WARN over 4 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The targets proved (k/4), modulo exactly the cited stubs, or the phase reached; the base hash
      and the ancestor check.
- [ ] The five imports as the first edit, and nothing else outside regions (b)–(d).
- [ ] Every new declaration with its role; the appendices.
- [ ] The setup's constant `C_P` and its ledger; target 1's `C`.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line.

## Known pitfalls at this pin (hard-won)

- **`pairEncode` doubles its first component.** The header `pairEncode (bits t) α` is itself the
  first component of the input, so `prefixCanon_complete` extracts it whole, and `pairExtractTM`
  then takes its first component.
- **`expandTM`'s block is unary on the stream tape, from cell `0`**; the writer needs every one of
  its `t` cells nonblank and the cell after it blank.
- **The setup's exit configuration is a structure literal.** Prove it with `Cfg.ext` and the field
  equations, not by unfolding.
- **`timeConstructible_poly` states `C·(n + 1)^(c + 1)`.** At `C = 1`, `c = 0` it is
  `fun n => 1 * (n + 1) ^ (0 + 1)`; rewrite to `fun n => n + 1` by `funext` and `simp`.
- `omega` with products as atoms (`ring` first); `nlinarith` for S's square. The linter needs a
  literal "Proof sketch" before every `sorry` (partial only).
