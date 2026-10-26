# External audit pack — the interpreter's startup kit (PR #162, an API gate), round 2

**Round 1** (`findings.md`; resolutions `resolutions.md`): FAIL, 0 blockers, 1 major, 1 minor, 11
notes. The major: the kit's census, 2 of 9 declarations copy-family members (SK-1's
`embedSilentCfg_initCfg` and SD-1's private suffix drop `is_input_suffix`), past the one-fifth
rule and unrecorded. The minor: two timing phrases. **The user ruled (2026-10-25): re-point in
round 2**, not an acknowledgment.

**The head:** `lean/startup-kit` at `d4759581`. Since round 1's head `06d314c3` it has merged the
campaign branch after #161 (`e984516b`; the kit's four files unchanged by the merge), the fix
commit `f8860243` (`evidence/round1-fix/gate74-fix.patch`), and a records-only merge of the
campaign branch (`d4759581`). Its Lean diff from the campaign branch is still the kit,
`NDCodeSimulator`, `NTimeHierarchy` and the `TuringMachine` facade. This bundle's Lean files are
from `d4759581`, and its records from the records commit that the dispatch prompt names.

| File | Change since round 1 |
|---|---|
| `TuringMachine/Build/InterpreterStartup` | imports `Build/InputDevice`; the private `is_input_suffix` deleted, the window call citing `Turing.pairEncode_drop` (the same statement and proof, public since #161); `seamCompTM_step`'s docstring and the main results line name the one dispatch transition; `prefixCanon_pairExtract_halt`'s docstring states the common bound as a bound |

The campaign merge brings #161 (`Deterministic`, `Build/StepBlockForward`, `Build/InputDevice`)
and records only; it touches none of this PR's four files.

## Brief for the auditor

1. **The major.** Does `exists_windowCall` now consume the published `pairEncode_drop`, with
   nothing re-proved? Is the kit's census 1 of 8 (12.5%), and is the ledger's SD-1 and SK-1
   accounting now complete and correct on every side (`campaign/duplication-ledger.md`)?
2. **The new import.** `Build/InputDevice` imports `Build/VirtualInput`, `UniversalStartup`,
   `Build/Contract/Basic`, `Build/Seam` and `Build/Catalog`, none of which sees the kit,
   `CodeSimulator` or `NDCodeSimulator`: is it acyclic, and does it bring any name that clashes
   downstream (the kit's importers `NDCodeSimulator`, `NTimeHierarchy` and the facades)?
3. **The minor.** Are the two reworded docstrings exact readings of their statements?
4. **No regression.** The kit elaborates, its seal holds with its 22 controls, its axioms are
   unchanged, and the two re-pointed consumers still elaborate with it (below). Is anything else
   changed?
5. **Duplication.** The v3 screen on round 1's population widened by the suffix-drop family's
   files (`Codec/Parse`, `Logspace/PathWalk`, `Build/InputDevice`; 14 files without the kit, 15
   with it; `round1-fix/screen-population*.txt`), at the campaign tip (`39c649e6`, the tree after
   #161) and at the fix `f8860243`: 816 → 815 declarations, 446 → 446 pairs
   (`round1-fix/screen-kit-r2-*`, `pairdiff-r2-head-vs-tip.txt`). New: SK-1's pair,
   `embedSilentCfg_initCfg` ⇄ `UniversalK`'s `ss_captureInitial` (100% each way, as in round 1).
   Gone: SD-1's pair `ic_input_suffix` ⇄ `pairEncode_drop` (100%), whose private member the tip
   still has in `NDCodeSimulator` and which round 2 removes from the kit too. Against round 1's
   head screen, the six new pairs are all inside the three added files and already in round 2's
   base (`pairdiff-r2-head-vs-round1.txt`). Is SD-1 now absent from this PR's files, and is SK-1's
   accounting right?
6. **Round 1's other points.** Is anything in round 1's resolutions unaddressed?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lu2api`, the replayed tree after #161): the kit with no
  diagnostic; `NDCodeSimulator` and `NTimeHierarchy`, each checked as one file after the kit's
  text with the imports merged: no diagnostic, and only `ntime_hierarchy`'s sorry warning
  (`evidence/round1-fix/`; recipe `recheck.sh.txt`).
- **Seal** (`round1-fix/KitSealed.*`, `KitSealControl.out`): round 1's 22-definition seal on the
  fixed kit; its only errors are the 22 controls at its top (lines 56–135; the kit from line 137),
  which close unsealed.
- **Axioms** (`round1-fix/NDCSCatAx.out`): the eight kit lemmas, the canonizer, the core and the
  bridge on the standard three, `seamCompTM_step` on `[propext, Quot.sound]`.
- **Freeze** against round 1's head (`round1-fix/freeze/`): 8 → 8 public, 1 → 0 private
  (`is_input_suffix` removed); no statement changed; bodies or docstrings changed:
  `exists_windowCall`, `seamCompTM_step`, `prefixCanon_pairExtract_halt`.
- **Lint** (`round1-fix/lint-turingmachine.txt`): `TuringMachine` 0 FAIL, 67 WARN over 84 files;
  no added line over 100 characters.
- **Replay:** round 1's head after the #161 merge passed `replay-lkit` (5 of 5; `evidence/replay/`).
  Round 2's head: `replay-lkit2.sh` (`round1-fix/`), the same five modules at `d4759581`,
  chained from `oleans-lu2api`. **Pending** (the gate is dispatched before it).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/74-startup-kit-api/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `startup-kit-api-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
