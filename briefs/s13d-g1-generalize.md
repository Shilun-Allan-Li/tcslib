# §13d G1 — generalize the §12 library to arbitrary alphabets (in place)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Before you start, confirm that
  `git merge-base --is-ancestor 2724d6ec4ebf220487c75071651e51c3936b9eef HEAD`
  succeeds (the §13d decisions). If it fails, **stop**.
- Create your working branch off the campaign branch (suggested name
  `fill/s13d-g1`). Record the base commit hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push**: `s13d-g1.zip`, containing
  `REPORT.md`, the four full modified sources, a `git format-patch` series
  against your recorded base, a git bundle, the final sweep log, the axiom
  logs (base and after), the evidence files below, and `SHA256SUMS`.
- Integration note, no action for you: under the user's rule for this
  revision, the maintainer integrates on a side branch, opens a PR, and runs
  a **separate audit gate** before the user merges.

## What this is

The first step of design §13d (`machine-library-design.md` §13d; read it in
full, including "Decisions 13d.1–13d.7"). The Hennie–Stearns simulator will
be a machine over a rich alphabet, finished by `alphabet_reduction`. Its
building blocks must therefore work over **any** alphabet, but the §12 library
is written for `Bool`. This batch generalizes the library **in place**: a type
parameter replaces `Bool`, and every existing `Bool` use becomes an instance.
**No new mathematics.** The tables already test only for blankness or symbol
equality.

**Pre-ship check (maintainer, executed):**
`audits/evidence/s13d/G1PreShip.lean.txt`. A generic copy of `transferTM` and
of `bufferTape` was used in the patterns existing `Bool` code uses:
- a canonical `Cfg.ofWords` statement with no annotation, where the
  alphabet is inferred from the configuration;
- `simp` with the generic empty-buffer lemma;
- a large alphabet (`Fin 7`).

All elaborate. A use with **no** context fixing the alphabet needs an
annotation; see ground rule 3.

## Scope: exactly these declarations (owned)

Introduce `{Symbol : Type*}`, and `[DecidableEq Symbol]` only where a table
compares symbols. Replace `Bool` by `Symbol` **only where it denotes the tape
alphabet**, and `x : List Bool` by `x : List Symbol` for inputs.

1. **`TuringMachine/Simulation.lean`**: `FinTM.bufferTape` and its lemmas
   `bufferTape_nil`, `bufferTape_nat`, `bufferTape_left`, `bufferTape_append`.
   Nothing else in the file changes. Z5 is already generic, and
   `bufferTape_inputSymbol` stays as is; it elaborates at `Bool` unchanged.
2. **`Build/Embed.lean`**: every definition and theorem, namely
   - the transformers `embedSilentTM`, `embedEmitTM`, `embedSilentRetTM` and
     `embedEmitRetTM`;
   - the transports `embedSilentCfg` and `embedEmitCfg`;
   - all their run, frame, visited, space and through-halt theorems;
   - the selected-tape exports;
   - `MultiTapeTM.runFrom_mapState_of_agreeOn`;
   - the private core.

   The capture tape writes emitted symbols, which is already generic.
3. **`Build/Seam.lean`**:
   - **Generalize:** `seamCompTM`, `seamReleaseTM`, the general-configuration
     theorems (`seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`,
     `seamCompTM_visitedByTapeHead_ofCfg`), `seamReleaseTM_firstReturn`,
     `seamReleaseTM_visitedByTapeHead`, and the private core.
   - **Keep at `Bool`, verbatim:** the canonical `Cfg.ofWords` theorems
     `seamCompTM_run`, `seamCompTM_firstReturn`,
     `seamCompTM_visitedByTapeHead`, and the three space corollaries. Their
     proofs may change to instantiate the generic core; these body changes
     are sanctioned.
4. **`Build/Catalog.lean`, the R3 section only**:
   - **Generalize:** the definitions `transferTM`, `copyTM`, `clearTM` and
     `compareTM` (the last with `[DecidableEq Symbol]`); the three framed
     sweep contracts `transferTM_run_ofCfg`, `copyTM_run_ofCfg` and
     `clearTM_run_ofCfg`; and their private trace machinery (`catalogTape`,
     `catalog_write_take`, `catalog_write_middle`, the
     clear/copy/transfer trace records and trace lemmas, and
     `catalog_trace_run` if it mentions `Bool`).
   - **Keep at `Bool`, verbatim:** `incrementTM` and its two framed
     contracts; the five canonical run rows; the four `_spaceUsedByTape` rows;
     both compare contracts; and all of Part 2. Proof bodies may change to
     instantiate the generic traces; this is sanctioned.

The increment and compare traces stay `Bool`, consuming the generalized
helpers.

## Ground rules (binding)

1. **Statement shape.** Each generalized public statement must be its base
   statement with exactly the substitutions above, plus the new binders.
   Nothing else may change: no new hypotheses, no reordering, no renaming.
   Docstrings are unchanged, except that one flagged sentence per file may
   note alphabet-genericity.
2. **Instance attestation (evidence, mandatory):** a file
   `evidence/G1Instances.lean.txt`, checked as a module. For **every**
   generalized public theorem, it holds an `example` whose type is the **base
   `Bool` statement copied verbatim from the recorded base**, proved by the
   generalized theorem at `Bool`. Every `Bool`-only statement the brief keeps
   must still elaborate verbatim, which the replay shows. For definitions, the
   body must be the base body verbatim apart from the substituted types; show
   this with the mechanical diff of rule 6.
3. **No consumer edits.** No file outside the four may change. If a consumer
   fails to elaborate because nothing fixes the alphabet:
   - restore that one declaration's `Bool` form;
   - record it as an escalation, with the consumer and the error;
   - continue.

   Never annotate or edit a consumer.
4. **No parallel copies.** Never keep both a `Bool` and a generic version of
   the same declaration. The `Bool`-specific statements kept above remain
   because they are specializations already in the library, and they are
   proved by instantiation.
5. **Imports unchanged; net private count must not increase in any file.**
6. **Mechanical surface diff (evidence):** for each of the four files, a
   declaration-level comparison against the base. Every public declaration is
   either unchanged or differs only by the sanctioned substitutions and
   binders; list each. Every sanctioned body change is listed.

## Duplication governance (binding)

Run the text-level screen over the four files before and after:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Simulation.lean \
  TCSlib/Complexity/TuringMachine/Build/Embed.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean
```

**No new pair** may appear. Quote both outputs. "New copies: none."

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**. Use `scripts/lean_check_tree.sh` for every check.
- **Full downstream replay:** every module downstream of the four files,
  computed from the import graph (about 191 modules at the issue commit), in
  dependency order. All must have **zero errors**. Sorry warnings must be
  exactly the base's: record the base's list first, and report any
  difference. The repository root module `TCSlib` cannot be checked in the
  scratch tree and is excluded.
- **Axiom prints, base and after,** for every public declaration of the four
  files. Each must be byte-identical. A generalized theorem's print is
  compared with its own base print. No `sorryAx` may appear where the base
  has none.
- Lint: `python3 scripts/campaign_style_lint.py` on
  `TCSlib/Complexity/TuringMachine` and `TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL each.

## REPORT.md checklist

- [ ] The base hash and the ancestor check.
- [ ] Per file: every generalized declaration, every one kept at `Bool`, and
      every sanctioned body change; the private delta.
- [ ] Escalations (rule 3), or "none".
- [ ] The instance attestation file and its check result; the mechanical
      surface diff.
- [ ] The copy-text screen before and after.
- [ ] The downstream replay (module count, zero errors, the sorry-warning
      set unchanged), the axiom comparison, and the lint lines.
- [ ] Diff touches only the four owned files.

## Known pitfalls at this pin (hard-won)

- **Inference needs context.** `transferTM k src dst` with no expected type
  cannot infer `Symbol`. Lemma statements over `Cfg k Bool …` fix it; check
  any `def` or `let` that names a sweep without a type (rule 3).
- **Two separately defined copies are not `rfl`-equal**, because their
  compiled matchers are distinct constants (the pre-ship probe). Generalize
  in place, so that there is only one definition.
- **`Type*` against `Type`.** Some existing signatures use `{S : Type}`;
  give `Symbol` a universe that unifies at every existing use.
- `[DecidableEq Symbol]` belongs only where a table compares two symbols
  (`compareTM`). The sweeps match `some b` and `none` only.
- Simp lemmas keep their `@[simp]` attribute. Check that `simp [bufferTape]`
  call sites still close; a failure there is a consumer failure (rule 3).
- `Function.update_of_ne`; `dsimp only` after `cases` on control.
