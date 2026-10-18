# External audit pack — §13d G1, the alphabet-generic §12 library (separate gate)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b). The
§13d revision (`machine-library-design.md` §13d, attached) rebuilds the
Hennie–Stearns zone layer at the book's design. The simulator will be a machine
over a rich alphabet, finished by `alphabet_reduction`. Its building blocks
must therefore work over any alphabet, but the §12 library was written for
`Bool`.

**G1** generalizes the library **in place**: a type parameter replaces `Bool`
wherever it denotes the tape alphabet, and every existing `Bool` statement
becomes an instance. No new mathematics is involved.

**Governance (the user's rule for §13d).** Every Lean change from this revision
needs both the user's approval through a PR and a **separate audit gate**. G1 is
PR #15 (`s13d/g1` into `complexity/arora-barak-ch3-4`, head `10c2c08d`). The user
merges after this gate closes. The gate closes on zero blockers and zero majors
(`workflow.md` §4). The duplication rule (`audits/TEMPLATE.md`, failure mode 5)
is in force.

**The audit object.** The change is the attached single-commit patch
`audits/evidence/s13d-g1.patch` (Codex, integrated by `git am -3` as `ef96bea0`
from the agent's base `93f51a65`). The base sources are reconstructible from
the patch and the attached after-sources. **Every proof is kernel-checked.** The
maintainer's replay evidence is below. What you audit is the **surface**:

- whether each generalized statement is exactly its base statement under the
  sanctioned substitution;
- whether the generalized library is genuinely fit for large-alphabet
  consumers;
- docstring truth after generalization;
- duplication.

## What changed (verify)

| File | Generalized (public / private) | Kept at `Bool` by the brief |
|---|---|---|
| `Simulation.lean` | `FinTM.bufferTape` and `bufferTape_nil/nat/left/append` (5 / 0) | everything else, including `bufferTape_inputSymbol` |
| `Build/Embed.lean` | every declaration (24 / 13), including `MultiTapeTM.runFrom_mapState_of_agreeOn` | none |
| `Build/Seam.lean` | `seamCompTM`, `seamReleaseTM`, the `_ofCfg` trio, the release pair (7 / 12) | the canonical `Cfg.ofWords` theorems and the three space corollaries; private `seam_ofWords_mapState` |
| `Build/Catalog.lean` | the definitions `transferTM`, `copyTM`, `clearTM`, `compareTM` (the last with `[DecidableEq Symbol]`), and the framed contracts `transferTM_run_ofCfg`, `copyTM_run_ofCfg`, `clearTM_run_ofCfg` (7 / 14 trace privates) | `incrementTM` and its contracts, the canonical run rows, the space rows, both compare contracts, all of Part 2 |

**Sanctioned surface forms**, each to be verified, not assumed:

- the new binders `{Symbol : Type*}` and, for `compareTM` only,
  `[DecidableEq Symbol]`;
- the replacement of `x : List Bool` by `x : List Symbol` for inputs. Where an
  input came from a section `variable {x : List Bool}`, the generalized
  declarations take an explicit `{x : List Symbol}` binder, and one `variable`
  line in `Embed.lean` changes to
  `{S : Type*} {Symbol : Type*} {x : List Symbol}`;
- `bufferTape_nil`'s statement naming its new implicit argument,
  `bufferTape (Symbol := Symbol) [] = fun _ => none`, because nothing else in
  that statement fixes the alphabet;
- the single proof-body change: two type annotations in
  `runFrom_mapState_of_agreeOn`.

## Brief for the auditor

1. **Substitution fidelity (the central rule).** For each of the 43
   generalized public declarations, compare base and after (patch hunks):
   - Is the after-statement exactly the base statement with the sanctioned
     substitutions and binders above, and nothing else: no new hypotheses, no
     reordering, no renamed binders?
   - Is every definition body byte-identical up to the substituted types?

   The maintainer's mechanical check (`audits/logs/s13d-g1-surface.log`)
   normalizes the sanctioned forms and finds 464 declarations byte-identical
   and 82 equal after normalization. Challenge the normalization itself. A
   rule that deletes `{x : List …}` binders on both sides could hide a
   dropped binder, so check every such case by hand.
2. **Instance attestation.** `audits/logs/s13d-g1-instances.lean.txt` holds 30
   `example`s, one per generalized public theorem. Each states the **base**
   `Bool` statement verbatim and is proved by the generalized theorem at
   `Symbol := Bool`; they elaborate with 0 errors.
   - Verify that each `example`'s type matches the base statement character
     for character (the agent's comparison is
     `audits/evidence/s13d/g1/instance-signature-comparison.txt`).
   - Verify that the 30 cover every generalized theorem.
   - Rule on the one local notation that fixes `bufferTape` at `Bool` in the
     `bufferTape_nil` example. Does it leave that statement's meaning
     unchanged?
   - For the 13 generalized definitions, the attestation is the
     body-identity of question 1. Say whether that suffices, or whether a
     definitional-equality example is needed for any of them.
3. **Fitness for large alphabets.** Are the generalized contracts *usable* at
   a rich alphabet such as the planned `ZoneSym k := Bool ⊕ ZoneCell k` (§13d
   G3)? In particular:
   - Do the framed sweep contracts' premises (blank-delimited words, head
     positions, `catalogTape` overlays) depend on `Bool` anywhere?
   - Do the generalized Embed and Seam contracts require anything of `Symbol`
     beyond what they state?
   - Is there any **hidden `Bool` dependence** left in a generalized
     statement, for example through a helper still stated at `Bool`?

   The maintainer's pre-ship probe (`audits/evidence/s13d/G1PreShip.lean.txt`)
   exercised a generic copy at `Fin 7`.
4. **What stays at `Bool`.** Confirm that every declaration kept at `Bool` is
   one the brief named, and that none of them would have to be generalized
   for §13d G2–G4 as designed. Report any that would; that becomes a G2
   statement-phase item, not a G1 defect.
5. **Universe and inference.** Some existing signatures use `{S : Type}`, and
   `Symbol : Type*` must unify at every use. The replay is the evidence: 265
   modules, 0 errors, and no consumer edited. Check that no generalized
   declaration became unusable at its existing `Bool` call sites through
   universe or elaboration-order effects that the replay could hide. One
   example of such an effect: a consumer that elaborates only because it
   is never instantiated.
6. **Duplication (failure mode 5).** The copy-text screen over the four files
   is identical before and after (374 pairs, 116,990 characters). Verify that
   in-place generalization created no parallel `Bool` and generic copy of any
   declaration (brief rule 4), and that the private count did not rise in any
   file.
7. **Docstrings.** The agent changed no comment byte. Report any docstring
   whose content is now **false or misleading** because its declaration
   became generic. Examples would be "binary word", "Boolean tape" or "the
   bit under the head" on a generalized declaration. List each one; they will
   be swept doc-only.
8. **Freeze outside scope.** Confirm that the diff touches only the four
   files, that imports are unchanged, and that the 90 non-generalized public
   declarations are unchanged in full.
9. Report anything else in the standard table, on the standard severity
   scale.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** `SHA256SUMS` all OK. The zip's C shim
  (`evidence/proc-self.c`) is excluded and unreferenced by the patch. None of
  the agent's scripts was run by the maintainer. The delivered sources are
  byte-identical to the integrated files.
* **Surface** (`audits/logs/s13d-g1-surface.log`): the maintainer's
  independent declaration-level comparison, summarized under question 1.
  The agent's comparison (`audits/evidence/s13d/g1/surface-comparison.md`)
  agrees: 43 public and 39 private generalized, 90 public unchanged, and one
  changed proof body.
* **Instances** (`audits/logs/s13d-g1-instances.{lean.txt,log}`): 30
  examples, 0 errors, 0 warnings, checked by the maintainer against the
  side-branch olean tree.
* **Replay** (`audits/logs/s13d-g1-integration-replay.log`): 265 modules in
  dependency order, in a fresh olean tree separate from the campaign's: 74
  prerequisites and the 191-module downstream closure, the root `TCSlib`
  excluded. **0 errors.** The downstream sorry warnings are exactly the base
  set, 85 of them, allowing for the `NSPACE.lean` line shift of the campaign
  commit `44853c6f`, which is outside G1.
* **Axioms** (`audits/logs/s13d-g1-axioms-{base,after}.log`, from the probe
  `s13d-g1-axioms.lean.txt`): 143 prints. They cover every public declaration
  of the four files, the six phase constructors and the derived instances.
  The base and after logs are **byte-identical**, and `sorryAx` appears
  nowhere.
* **Lint** (`audits/logs/s13d-g1-stylelint.log`): 0 FAIL in
  `TCSlib/Complexity/TuringMachine` and in `…/Build`.
* **Screen** (`audits/logs/s13d-g1-copytext-{before,after}.txt`): identical.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s13d-g1-findings.md`. The gate closes on zero blockers and zero majors.
After it closes, the user merges PR #15, and §13d continues with the G2–G4
statement phase.
