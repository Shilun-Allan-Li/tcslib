# RB4 retrofit report — partial delivery

## Base, branch, and scope

- Repository: [tcslib](https://github.com/Shilun-Allan-Li/tcslib).
- Required starting branch: `complexity/arora-barak-ch3-4`; working branch: `fill/retrofit-rb4`. No rebase, push, or PR.
- Actual checkout base: `3e5dd8c7504725750720629a7be08855b89d4e87`.
- Brief issued at: `8f13d74ecba8e73a3642d605f462774092d7ef8a`. The intervening changes are documentation only; all three owned Lean files are identical at those two commits.
- Brief and named audits read in full, including the binding transport-first-then-agree plan in `audits/vhost-infra-findings.md`.
- Delivery head: `e6383fd2b3a0045dc4f9f480f2379b1ded4ada65`.
- The committed diff touches only `TCSlib/Complexity/TuringMachine/Build/Loop.lean`. Full final sources for all three owned files are included. Primitives and Hardness are byte-identical to the actual base.
- One permitted import added: `TCSlib.Complexity.TuringMachine.Build.Embed` in Loop. No other import changes.

## Status and measured deltas

| Task / file | Status | What landed |
| --- | --- | --- |
| Task 1 / Loop | Complete | One non-body `AgreeOn` fact; H3 administrative proofs consume transferred segments; 12 H3 declarations removed, `emLoopHost_prepare` retained with a rewritten proof; near-copy init and single-use body-forward declarations removed. |
| Task 2 / Loop | Complete | All four old relocation declarations removed. Three run consumers use R1 tape embedding, injective state transport, then same-carrier Z5. Selected/frame exports establish complete configurations; exit absorption also uses public contracts. |
| Task 2 / Primitives | Deferred, unchanged | Generic relocation/segment boundary recorded below. Four existing relocation members remain. |
| Task 2 / Hardness | Deferred, unchanged | Generic state-map/relocation boundary recorded below. Four existing relocation members remain; concrete sites not retrofitted. |

This is the brief's priority-ordered partial delivery. It does **not** discharge the entire three-file Task 2 debt.

| File | Lines before → after | Net lines | Private before → after | Net private | Public |
| --- | ---: | ---: | ---: | ---: | ---: |
| Loop | 5,515 → 5,513 | −2 | 204 → 191 | **−13** | 8 unchanged |
| Primitives | 6,374 → 6,374 | 0 | 254 → 254 | 0 | 18 unchanged |
| Hardness | 8,725 → 8,725 | 0 | 544 → 544 | 0 | 5 unchanged |

Task 1 alone removes 207 lines and 13 private declarations. Task 2's explicit public-contract frame proofs add 205 lines and have net zero private declarations (four removed, four added). The approximate 500-line saving anticipated by the brief was not achieved; the binding private-count reduction was achieved.

## Duplication ledger

Accounting uses the current ledger's **expanded correspondence membership**, not just a normalized-text test. Rewritten `emLoopHost_prepare` is conservatively still counted as a corresponding member. The near-copy init and body-forward removals do not receive ledger credit.

| Current ledger row | Deleted recorded members | Provisional shared-copy charge | Delivered accounting | Delivered members / declarations |
| --- | ---: | ---: | ---: | ---: |
| Loop: 104 | 12 H3 + 4 relocation = 16 | +1 | **89** | 89 / 199 = 44.72% |
| Primitives: 150 | 0 | 0 | **150** | 150 / 272 = 55.15% |
| Hardness: 4 | 0 | 0 | **4** | 4 / 549 = 0.73% |
| Owned-file total: 258 | **16** | **+1** | **243** | — |

**Conservative net ledger-member reduction: 15 (16 existing members removed, minus one charge for the permitted provisional shared-lemma copy).** Against only the currently recorded correspondences, Loop has 88 surviving members and the reduction is 16; the handoff accounting above deliberately also charges the new local implementation, even before its public counterpart is promoted. There are zero additional or undisclosed new copies. The one provisional implementation is in Loop only and is disclosed below. The eight old relocation members in Primitives/Hardness remain acknowledged debt; removing Loop's original-side members does not erase their copy-side membership.

### Removed private declarations

- Task 1, H3 members: `emLoopHost_fuel_capture`, `emLoopHost_input_rewind`, `emLoopHost_fuel_rewind`, `emLoopHost_fuel_copy`, `emLoopHost_fuel_return`, `emLoopHost_fuel_setup`, `emLoopHost_release`, `emLoopHost_borrow_step`, `emLoopHost_borrow_run`, `emLoopHost_borrow_rewind`, `emLoopHost_borrow`, `emLoopHost_reject`.
- Task 1, other removals: `emLoopHost_init`, `emLoopHost_body_forward`.
- Task 2: `emCallAction`, `emCallCfg`, `emCall_apply`, `emCall_relocate_run`.

### Every new private declaration

| Declaration | Purpose |
| --- | --- |
| `emLoopHost_agree` | The single all-reads agreement on non-body states. |
| `emCall_state_run` | The sole provisional local copy of the requested shared lemma; extends an injectively renamed source table, identifies its run, then uses Z5 on the host carrier. |
| `emCallEmbeddedCfg` | Thin composition of public `embedEmitCfg` with `Cfg.mapState`; no copied tape-selector implementation. |
| `emCallTripleEmbedding` | Packages the existing cleaner-bank index and inverse into an injective tape selection. |
| `emCallPairEmbedding` | Packages the existing argument/capture index and inverse into an injective tape selection. |

## Task 1 proof details and preservation

All 24 original `loopHost_*` lemma blocks are byte-identical to the base. All four surviving pre-existing `emLoopHost_*` statements and docstrings are byte-identical. All 31 public declaration blocks, including docstrings and proof bodies, are byte-identical without whitespace normalization; `verification/public-surface.json` records their hashes.

The 13 exact H3 copies are handled at segment boundaries rather than by assuming that an existential endpoint theorem supplies an entire prefix trace:

- Fuel capture transfers `loopHost_fuel_capture` by Z5; the original live-prefix hypothesis supplies the guard.
- Fuel rewind/copy/return are subsumed by transferring `loopHost_fuel_setup`. A local backwards state-shape invariant proves its prefix stays outside body control; its endpoint is the existing original theorem.
- Input rewind cites the existing `loop_rewind_bounded` engine with transition hypotheses obtained from the shared agreement. The endpoint-only original `loopHost_input_rewind` does not itself export a prefix-shape witness. No second rewind recursion survives.
- Init is an exact use of `loopHost_init` at the consumer.
- Release is a Z5 step transfer in `emLoopHost_start`.
- Borrow is a Z5 transfer of `loopHost_borrow`. Local guard reasoning uses `loopHost_borrow_step` on the scan and a rewind-position invariant. The guard includes the elementary rewind one-step arithmetic formerly present in the copied rewind proof; this is disclosed, not represented as a new exported infrastructure theorem.
- Prepare and reject retain their assembly of component segments in their consumers. `emLoopHost_prepare` remains a private wrapper; reject's single-use assembly is local to the round proof.
- The distinct forwarding body proof is moved into its sole `emLoopHost_anchor_return` consumer. The anchor-return near-copy itself remains; its removal was optional.

## Task 2 composition in Loop

For each cleaner bank, prepared evaluator, and finalizer:

1. Instantiate `embedEmitTM` / `embedEmitCfg` for the physical tape embedding.
2. Extend the injectively renamed machine's table to the full host state carrier. `Cfg.mapState_apply` and the existing unguarded `runFrom_comm_of_step` identify the reference run.
3. Apply `runFrom_eq_of_agreeOn` between reference and actual host on the image of good source states, from the identical starting host configuration.
4. Use `embedEmitTM_runFrom` to identify the source run and endpoint. Guard evidence is the original source first-return evidence transported by that contract.
5. Use `embedEmitCfg_selected_tape`, `embedEmitCfg_selected_pos`, and `embedEmitTM_frame` for selected and inactive fields, respectively. All five configuration fields are preserved as stated.

Z5 never compares machines of different tape counts or state types. There is no replacement induction over a relocated action's low-level writes. The extension proof exists in only one file.

## Requested shared lemmas

Request **one** public lemma in `Turing.MultiTapeTM` in `Simulation.lean`, named `runFrom_mapState_of_agreeOn` (name negotiable), with exactly the contract implemented by Loop's `emCall_state_run`:

```lean
{k : ℕ} {S H : Type} {x : List Bool}
(src : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
(emb : S ↪ H) (good : S → Prop)
(hagree : ∀ q, good q → ∀ inp work,
  host.tr (emb q) inp work = (src.tr q inp work).mapState emb)
(c : Cfg k Bool S x) (t : ℕ)
(hguard : ∀ u < t, ∀ q, (src.runFrom c u).state = some q → good q) :
host.runFrom (c.mapState emb) t = (src.runFrom c t).mapState emb
```

The proof is in the delivered full source. It uses no Embed declaration, so promoting it to Simulation introduces no import cycle. R1 is composed at the Loop call sites. This is the single permitted local copy; Simulation is outside ownership and was not edited. No second or third copy has been installed in Primitives or Hardness.

## Escalations and exact continuation frontier

The old generic relocation family is stronger than literal R1 embedding at its abstract interface:

- Its assumption `select (index i) = some i` forces `index` to be injective but permits **extra aliased host slots**. For example, with one source tape and two host tapes, take `index 0 = 0` and `select 0 = select 1 = some 0`. The old configuration maps source data onto both host tapes. R1 preserves the ambient frame at host tape 1, because it lies outside the index range. With source cell `some true` and ambient cell `none`, these configurations differ. The selected-tape exports do not imply equality of those generic configurations.
- The old state map is `S → H`, without injectivity. The requested shared lemma is injective. Adding injectivity to a surviving generic statement would weaken it, so this delivery does not do that.

In Primitives this reaches `emitterP2_segment` and `emitterP2_call_segment`: they preserve the broad selector/state-map quantifiers and explicitly mention the old Action/Cfg interface, including the mandatory first action when entry equals exit. In Hardness it reaches `clSlot_run` and the arbitrary-map `clMap_run`. These statements and their implementations remain exactly at baseline. No speculative narrowed replacement or failed proof is in the delivered sources.

These are obstructions to a **literal generic replacement**, not a claim that the concrete injective call sites are mathematically blocked. Loop's concrete sites demonstrate the public route. A continuation should promote the shared state lemma, then remove/specialize the generic private consumers while preserving every surviving statement, prove exact selector/range correspondence for each concrete layout, and retrofit Primitives before Hardness. Hardness's 13 direct `clSlot_run` sites and its `clMap_run` consumers remain untouched. The partial cutoff is after the completed Loop file; no further family is claimed discharged.

## Commits and verification

1. `ff75c81f054b56af491eb068d9005575b5f70287` — `refactor: transfer Loop administrative phases by guarded agreement`.
2. `e6383fd2b3a0045dc4f9f480f2379b1ded4ada65` — `refactor: replace Loop relocation family with R1 and guarded state transport`.

The required branch bootstrap (65-module order, imported prerequisites, and Build files) passed at the actual base. Baseline owned-file checks and the 31 baseline axiom prints contained no errors, sorry warnings, or `sorryAx`. Each changed Loop version was checked with a fresh direct Lean invocation before its commit. The second checked version also verifies the first commit's changes; the final six-check sweep verifies the delivery after the second commit. No admission was introduced and no `lake build` was run.

Toolchain: Lean 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), matching `lean-toolchain` and `lake-manifest.json`; mathlib pin `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Dependencies were obtained with `lake exe cache get`. A local runtime compatibility shim redirects this process's numeric `/proc/<pid>/exe` lookup to `/proc/self/exe`; it does not alter the Lean executable, libraries, source, or proof checking and is not a repository change.

The required final checks ran in exactly the brief’s order and all produced fresh nonempty `.olean` files:

| Check | Exit | Errors | Sorry warnings | Fresh `.olean` |
| --- | ---: | ---: | ---: | --- |
| `TuringMachine/Build/Loop` | 0 | 0 | 0 | yes |
| `TuringMachine/Build/Primitives` | 0 | 0 | 0 | yes |
| `TuringMachine/Build/Catalog` | 0 | 0 | 0 | yes |
| `CookLevin/Hardness` | 0 | 0 | 0 | yes |
| `TuringMachine` | 0 | 0 | 0 | yes |
| `CookLevin` | 0 | 0 | 0 | yes |

Final sweep tail:

```text
PASS 1/6 TCSlib/Complexity/TuringMachine/Build/Loop: exit=0; errors=0; sorry_warnings=0; fresh_olean_bytes=16869192; seconds=81.3
PASS 2/6 TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0; errors=0; sorry_warnings=0; fresh_olean_bytes=15726992; seconds=39.83
PASS 3/6 TCSlib/Complexity/TuringMachine/Build/Catalog: exit=0; errors=0; sorry_warnings=0; fresh_olean_bytes=24973120; seconds=97.45
PASS 4/6 TCSlib/Complexity/CookLevin/Hardness: exit=0; errors=0; sorry_warnings=0; fresh_olean_bytes=17847624; seconds=496.45
PASS 5/6 TCSlib/Complexity/TuringMachine: exit=0; errors=0; sorry_warnings=0; fresh_olean_bytes=45168; seconds=3.63
PASS 6/6 TCSlib/Complexity/CookLevin: exit=0; errors=0; sorry_warnings=0; fresh_olean_bytes=37456; seconds=2.04
FINAL SWEEP: 6/6 PASS; zero errors; zero sorry warnings
```

All 31 final axiom prints are byte-identical to `verification/axioms-baseline.log`; none contains `sorryAx`. SHA-256 of each complete axiom log: `d90de20553fd813f94f6741ba0b7ec4c69478b93b24c1e087add11ec3d18e171`.

```text
'Turing.stateWord' does not depend on any axioms
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitLoopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_installCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairConcat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairDup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolveWith' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_unaryToken' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_appendBit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NPHard.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT3_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT3_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both directory lint lines:

```text
style_lint: 0 FAIL, 3 WARN over 9 files
style_lint: 0 FAIL, 1 WARN over 2 files
```

The lint warnings are the existing oversized-file warnings (Build: Catalog, Loop, Primitives; CookLevin: Hardness). No lint failure is suppressed. The final working tree has no tracked changes after the two commits.

### Observed baseline admissions outside this scope

`verification/baseline-admissions.log` records all admission diagnostics observed during bootstrap. They are in `Robustness/AlphabetReduction`, `Robustness/SingleTape`, `CounterProgRun`, `NDCodes`, `Formulas/QBF`, `Formulas/QBFEncoding`, and `Build/Zone`. None is in an owned file. These existing admissions were not edited. The final six requested checks must have zero sorry warnings; importing an unchanged admitted dependency does not repeat that dependency's warning.

## Package

- `REPORT.md` — this status, accounting, shared-lemma request, and continuation frontier.
- `TCSlib/.../Loop.lean`, `Primitives.lean`, `Hardness.lean` — full delivered sources.
- `patches/` — the two `git format-patch` commits, in order.
- `retrofit-rb4.bundle` — incremental bundle requiring the actual base above.
- `sweep.log`, `axioms.log` — final required check output and all 31 final axiom prints.
- `verification/` — baseline/precommit evidence, exact public-surface manifest, statement-freeze checks, baseline axiom log, and both final lint logs.
- `SHA256SUMS` — hashes of every package member except itself.

For integration, start at the recorded base and apply the patch series in order; the sources and bundle represent the same delivery head. Replaying both patches against the base in an isolated Git index reproduces the exact delivery tree (`verification/patch-replay.log`). This archive contains no probe files or provisional Lean code.
