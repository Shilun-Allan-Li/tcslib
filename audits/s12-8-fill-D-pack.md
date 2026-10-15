# External audit pack — §12.8 stream D: R8.0b (the rich-body counter loop, generalized in place) and R8.6, fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e). Design:
`machine-library-design.md` §12.8a §1 "R8.0b" and §8 "R8.0b target signatures", under the
user's decision **O2**.

§12.7's `counterLoopTM` runs only `Bool` bodies. Every rich-alphabet consumer of §12.8
needs a counter loop with a **rich body**: S1b's round, Savitch's frame step, and the record
rows' find and next. One batch (brief `briefs/s128-fill-D.md`, report attached verbatim)
built it **in place**, in `TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean`:

1. it generalized `counterLoopCfg`, `counterLoopOrbit` and `counterLoop_time_le` to any
   symbol type, types only;
2. it added `lastEmb`, `counterLoopTMVia` and the two generic contracts, proved by **the
   existing round induction, generalized**;
3. it re-derived the landed `Bool` contracts, with byte-identical statements, from the
   generic ones at `Function.Embedding.refl Bool` through Z5, `runFrom_eq_of_agreeOn`;
4. it filled R8.6, `expandTM_run_ofCfg`, **proved modulo** Scan's `writeAdvTM_run_ofCfg`.

**Why a separate gate.** This batch changes **audited public signatures**: the three
type-only generalizations. Under the §13d process rule, the user merges the PR (#38) only
after this gate closes. Fill gates close on zero blockers and zero majors (`workflow.md` §4).
The duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in force.

The fill is the attached single-commit patch, `audits/evidence/s12-8/r80b-fill/s128-fill-D.patch`.
- It is Codex-authored (agent commit `b2b7ac5d` on base `37ab6091`), integrated by
  `git am -3` as `be1b7691` at the campaign tip `aed5b4ff`.
- `CounterLoop.lean` is byte-identical between `5afed90b`, the brief's base, and `aed5b4ff`.
- Since then the campaign tip has advanced. Stream B's `writeAdvTM_run_ofCfg` is now proved,
  in PR #41, so on merge R8.6 is admission-free.

**Every proof is kernel-checked**; the replay evidence is below. The audit object is the
**surface and its fidelity**:
- the signature generalizations;
- the four new declarations;
- the routes the brief binds;
- the privates;
- the duplication rule, including escalation **E1**.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Type-only generalization, body verbatim** (the gate's main object) | `counterLoopCfg`, `counterLoopOrbit`, `counterLoop_time_le`: exactly `{S : Type}` ↦ `{Symbol S : Type}`, `x : List Bool` ↦ `x : List Symbol`, and `Bool` ↦ `Symbol` where it denotes the tape alphabet. The counter word `w : List Bool` stays |
| **New public, the brief's exact text** | `lastEmb`, `counterLoopTMVia`, `counterLoopTMVia_run_done`, `counterLoopTMVia_run_escape` |
| **Frozen statement, authorized body swap** | `counter_cfg_eq`, now an instance of the private `counter_layout`; `counterLoopTM_run_done`/`_escape`, now Z5 re-derivations; `expandTM_run_ofCfg`, from `sorry` to proof |
| **Frozen, statement and body byte-identical** | the other 20 publics, including `counterLoopTM` and `expandTM` |
| **Privates, 24 → 23** | added `counter_layout`, `counter_refl_agree`; removed (inlined, single-use) `counter_last_unselected`, `counter_patch_initial`, `counter_orbit_succ`; nine rewritten over a generic alphabet (ledger in the report); `counter_buffer_complement` by disposition (i), a body swap to `FinTM.bufferTape_map Equiv.boolNot.toEmbedding w p` |
| **Imports** | exactly one added: `TuringMachine.SymbolLift` |
| **Docstrings** | the flagged re-derivation appendices, new-declaration prose and sketches, and the module bullets and status |

## Brief for the auditor

1. **The signature changes are sound and harmless.**
   - Confirm that each of the three generalized statements is its base statement with exactly
     the substitutions above.
   - Confirm that every existing call site elaborates unchanged, and that the base statements
     still hold as instances. The instance file `R80bInstances.lean.txt` restates each base
     statement verbatim and proves it by the in-tree theorem, and the maintainer re-ran it:
     0 errors, 0 warnings.
   - Rule on whether any consumer could be broken or weakened by the generalization, for
     example through elaboration of an implicit `Symbol`.
2. **One host induction** (§12.7 fill gate F4).
   - Confirm that `counter_rounds` is still the **only** round induction, with its
     unrestricted final state.
   - Confirm that both generic contracts are derived from it.
   - Confirm that both `Bool` contracts are short Z5 re-derivations at `refl` with no
     induction: one `counter_refl_agree`, then `simp only [z5]` and the generic contract.
   - Check that no second host, decrement trace or overlay re-proof exists. That is rule 4: no
     `counterLoopCfgVia`, and nothing private restating `SymbolLift`'s overlay layer.
3. **Route fidelity** (the brief's routes 1–4).
   - **The generic decrement phase:** guarded transport with `emb := counterLoopDecExit a`;
     the R1 configuration at `lastEmb k`; the overlay transport
     `Cfg.liftOver_decodeSymbols` / `MultiTapeTM.liftSymbols_runFrom_over`, **cited, not
     re-proved**; the landed `decrementTM_run_*_ofCfg` on the shadow; and read-back by
     `decodeBool_eq_some` and `FinTM.bufferTape_map`.
   - **`counter_refl_agree`:** it computes R1's action at `lastEmb k` from Embed's **public**
     surface and names no private Embed declaration.
   - **R8.6:**
     - `counterLoopTM_run_done` with `τ := fun _ => pat.length + 1`;
     - the orbit's closed form by induction over the **writer's** orbit, never over host
       rounds;
     - liveness from `runFrom_state_ne_none_of_le`;
     - the gate's checks `d = 0`, `w = []`, and `pat = []` with `d > 0`.
4. **Guards and range** (F5, F6).
   - The injectivity and guard discipline, including anchor priority when `exit = some a`,
     must be preserved by the generalized `counter_debit`/`counter_body`.
   - Every physical cost must stay within `r ≤ value + 1`, which is `counterOverhead`'s
     range.
5. **Freeze.** Re-establish from the attached patch:
   - every public in its class;
   - base lines 106–541 (symbol transport, C1 decrement, counter arithmetic)
     **byte-identical**, except `counter_buffer_complement`'s one-line body. The maintainer
     confirms this: the only changed line in that block is base line 213;
   - only `CounterLoop.lean` changed.

   Two independent checks agree, the agent's mechanical surface diff and the maintainer's,
   and both are attached.
6. **Duplication (failure mode 5) and escalation E1.** The screen (CounterLoop, Catalog,
   Embed, Seam, Simulation, SymbolLift) goes from 414 to 418 pairs. All four new pairs are
   in-file, with no cross-file pair and none removed.
   - **E1.** `counterLoopTMVia` reproduces the frozen `counterLoopTM` at 91%, and 84% in the
     other direction. Both texts are mandated: one is the new definition's exact text, the
     other a frozen definition. So the pair cannot be factored without breaking a mandate.
     The agent escalated correctly. **Maintainer's proposed disposition:** authorize this
     one definition pair, and open a 12.2c follow-up to redefine `counterLoopTM` as the
     identity-embedding instance of `counterLoopTMVia`. Rule on that, or propose another
     disposition.
   - `counterLoopTM_run_escape` ↔ `_run_done`, 83% / 72%: the two required Z5
     re-derivations, which share transport setup. Rule on whether this is idiom or a copy
     to factor.
   - Check the brief's hazards: `counter_layout` against `counter_cfg_eq`, where the body
     must have moved and not been duplicated; and the expand orbit induction against
     `counter_rounds`.
7. **Docstrings.**
   - Check the re-derivation appendices and the new declarations' sketches against the
     proofs as delivered.
   - Check the module status line: it names `writeAdvTM_run_ofCfg` as R8.6's only admitted
     dependency. Say whether that is now stale, since B is proved at the tip, and if so,
     whether to fix it by a doc-only refresh after this gate.
8. **Size.** `CounterLoop.lean` grows from 1,279 to 1,697 lines. The justification is
   recorded: the brief makes the generalization in place and forbids new files, file size
   alone is not a driver (user, 2026-10-11), and 12.2c owns the per-theme split. Say whether
   you disagree.
9. Report anything else the fill misstates, in the standard table.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** `SHA256SUMS` are all OK. The zip's C file (`lean-readlink.c`, an
  environment shim) was not compiled or run, and nothing references it. The agent's Python
  helpers were not run, and are not attached.
* **Freeze** (`audits/logs/s12-8-fill-D-freeze.log`), the maintainer's declaration-level
  check. It is consistent with the agent's `declaration-freeze.md`:
  - publics 27 → 31, the four additions;
  - three type-only lines with byte-identical bodies;
  - exactly the four authorized swaps;
  - privates 24 → 23;
  - one import.
* **Replay** (`audits/logs/s12-8-fill-D-replay.log`). The downstream closure of
  `CounterLoop`, 6 modules (`CounterLoop`, `InputCall`, `CfgRecord`, `TQBF`, and the
  `ClassPSPACE` and `TuringMachine` facades), run at `be1b7691`. **0 errors.** 11 sorry
  warnings, all out of scope at that tree; `CounterLoop` has 0. The user ran it from the
  maintainer's command. The agent's own 74-module sweep agrees: 37 → 36, exactly
  `expandTM_run_ofCfg` removed.
* **Axioms** (`audits/logs/s12-8-fill-D-axioms.log`).
  - All 31 publics are printed. Each is within the standard triple, except
    `expandTM_run_ofCfg`, which has `sorryAx`.
  - The prints match the agent's after-log line for line. The agent's base/after comparison
    shows the 28 existing lines unchanged.
  - The **admission walk** (`…-admissions.log`) shows that `expandTM_run_ofCfg`'s only
    `sorryAx` source is `writeAdvTM_run_ofCfg`. That row is proved at the current tip.
* **Instances** (`audits/logs/s12-8-fill-D-instances.log`): the maintainer re-ran
  `R80bInstances.lean.txt` read-only, with 0 errors and 0 warnings. A control copy with an
  appended false `decide` example fails as expected.
* **Lint** (`audits/logs/s12-8-fill-D-stylelint.log`): 0 FAIL over `TuringMachine` and over
  `TuringMachine/Build`. The warnings are all file-size ones.
* **Screen** (`audits/evidence/s12-8/r80b-fill/screen-{base,after}.txt` and
  `screen-delta.md`; the maintainer's run is `audits/logs/s12-8-fill-D-screen-after.txt`):
  identical.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s12-8-fill-D-findings.md`. When this gate closes, the user merges #38. With stream B
already merged, R8.0b and R8.6 are then fully proved.
