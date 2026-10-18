# External audit pack — Fill campaign, Epoch 2 (second fill round)

Audits commit `ee32391c` on `complexity/arora-barak-ch1`. Since the epoch-1
resolutions (`audits/epoch1-resolutions.md`), two things happened. **(a)** The
**epoch-2 merge refactor** (commit `24687122`, executing the epoch-1 audit's
endorsed pre-work): the new shared modules
`TuringMachine/StateRenaming.lean` (public `Action.mapState` moved verbatim
from `Oracle.lean`; new `Cfg.mapState` + application lemma;
`MultiTapeTM.relabelState` + step commutation + `relabelState_runFrom_init`)
and `TuringMachine/Simulation.lean` (the epoch-1 gadget layer, made public),
the two `Finite.lean` promotions (`computesInTime_iff`, generalized to any
alphabet, and `Computes.exists_computesInTime_iff`), and the rewiring of
`Encoding`/`Halting`/`Oracle`/`Composition` — with a declaration-level check
that no public name was lost. **(b)** The **epoch-2 fill round**: three
independent cloud agents (zip delivery — runners have no repository write
access) filled **all five epoch-2 targets**; the maintainer reviewed each
delivery against its brief and integrated the patches with authorship
preserved (five commits). **No audited statement changed at any point.**
Record findings in `audits/epoch2-findings.md`.

The campaign standing: **17 of the 21 audited sorries are now proved.** The
four that remain are `oblivious_of_mem_DTIME`, `exists_effectiveMachineCode`,
`universal`, and `timed_universal` — exactly epochs 3-4.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Statement freeze.** Net `git diff` from the pre-fill HEAD (`60bdab6b`)
   removes exactly 10 lines: the 5 target `sorry`s and 5 docstring closing
   lines, each re-appearing verbatim with an appended implementation note (the
   flagged appendix mechanism). Across the refactor (`9bb3176e → 24687122`),
   a declaration-name comparison shows no public declaration lost: 7 epoch-1
   private helpers were retired in favor of 6 public replacements plus the
   same-name promotions. All pre-existing declaration headers are unchanged;
   the three agent deliveries each shipped their own freeze evidence agreeing
   with this.
2. **Elaboration.** Full 24-module sweep via the strengthened
   `scripts/lean_check_tree.sh` (exit-status + fresh-olean enforcement; the
   epoch-1 finding-1 gate), fresh olean tree, Lean 4.25.0 / mathlib
   `029db123ddaa`: **zero `error:` lines, zero gate failures**, exactly 4
   `declaration uses 'sorry'` warnings (`Oblivious.lean:109`,
   `Encoding.lean:455`, `Universal.lean:102`, `Universal.lean:165`).
3. **Axiom footprints** (`#print axioms`, maintainer-run):

   ```text
   'Turing.FinTM.exists_comp_partial'        [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.computesFunInTime_comp'     [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.one_work_tape'              [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.nonnegative_heads'          [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.alphabet_reduction'         [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.one_work_tape_binary'       [propext, Classical.choice, Quot.sound]
   'Complexity.UC_not_computable'            [propext, Classical.choice, Quot.sound]
   'Complexity.PAL_mem_P'                    [propext, Classical.choice, Quot.sound]
   'Complexity.mem_P_iff_one_work_tape'      [propext, Classical.choice, Quot.sound]
   'Turing.universal_quadratic'              [propext, sorryAx, Classical.choice, Quot.sound]
   'Complexity.UC_computable_of_HALT_computable' [propext, sorryAx, Classical.choice, Quot.sound]
   'Complexity.HALT_not_computable'          [propext, sorryAx, Classical.choice, Quot.sound]
   ```

   **[AB09, Theorem 1.10] (`UC_not_computable`) is now fully machine-checked
   with no admissions**, as are the complete normal-form chain and the P-level
   corollaries. The three remaining `sorryAx` carriers inherit it solely
   through `universal` (epoch 3B/4).
4. **Soundness scan.** No added `axiom`, `native_decide`, `implemented_by`,
   `extern`, or `unsafe` anywhere in the fills. One scoped elaboration option
   in `SingleTape.lean`: `set_option synthInstance.maxSize 8192 in` on a
   `DecidableEq` instance for the sweep controller's sum/sigma representation
   — a typeclass *search budget*, not a proof-checking bypass (the kernel
   still checks the result); the file-header options are unchanged.
   `derive_fintype%` (mathlib's deriving elaborator) is used for one `Fintype`
   instance. New imports across the fills: precise `Mathlib.Data.Fintype.*`
   modules only.
5. **Policy conformance** (new attestation; `scripts/style_lint.py`, added
   this round per the epoch-1 process discussion). Result over
   `TCSlib/Complexity`: zero FAIL in campaign files after fixing one genuine
   catch (the refactor's own `StateRenaming.lean` lacked a `## References`
   section — added); three FAILs remain in the pre-campaign legacy
   `NPReductions/*` files (missing References sections), **out of this
   branch's scope**, recorded for a separate cleanup; one WARN:
   `SingleTape.lean` at 1315 lines exceeds the policy 1000-line threshold —
   batch B **escalated this in its report** as a single cohesive construction
   (75 private helpers for one theorem), accepted for now with a possible
   later split if its zipper/transduction layer is promoted. Every `sorry`
   carries a sketch; facades import all children.
6. **Delivery provenance.** Three zip deliveries per the standardized epoch-2
   contents (report, sources, format-patch, git bundle, full sweep log under
   the strengthened gate, per-theorem axiom log, SHA256 manifest). Bases
   verified as `24687122`; sources, patches, and bundles mutually consistent;
   the agents' own sweep and axiom logs agree with the maintainer's
   independent runs. Agent reports preserved in `audits/epoch2-agent-reports/`.

## What was filled / new surface

| Batch | Now proved | New declarations |
|---|---|---|
| A (Composition + Simulation) | `exists_comp_partial`, `computesFunInTime_comp` (explicit `c = 2`) | **26 public** in `Simulation.lean` (the buffered-composition layer — the primary blind-restatement target): `tapeBlocks` + 3 projection lemmas, `bufferTape` + 4 lemmas + `bufferTape_append`, `VirtualTag`, `virtualMove`, `virtualNextTag`, `bufferTape_inputSymbol`, `virtualMove_correct`, `bufferedCompTM`, `bufferedFirstCfg` + `_init`/`_step`/`_run`, `bufferedSecondCfg` + `_step`/`_run`, `bufferedScanCfg` + `_run`, `bufferedFirstCfg_rewind`, `bufferedComp_start`. No new privates |
| B (SingleTape) | `one_work_tape` (constant `9k + 6`; separate `k = 0` lockstep path) | 75 private (zipper/transduction sweep machinery; inventory with line numbers in the batch-B report) |
| C (Bidirectional + AlphabetReduction) | `nonnegative_heads` (constant `1`), `alphabet_reduction` (constant `3L + 2`, one-hot width `L = card Γ + 1`) | 88 private (fold layer + block-code layer; inventory in the batch-C report) |

## Brief for the auditor

Ground rules as in all previous rounds (trusted surface; no blanket approval;
tactic scripts are Lean-checked and axiom-audited — out of scope). Priorities:

1. **Blind-restate the 26 new public `Simulation.lean` declarations** — they
   are shared audited surface that epochs 3-4 will build on. The semantic
   heart: does `VirtualTag`/`virtualMove`/`virtualNextTag` +
   `bufferTape_inputSymbol` + `virtualMove_correct` faithfully reproduce the
   clamped native input semantics (`Turing.moveInputPos`) on the buffer, for
   every word including the empty one?
2. **Spot-check the three delivered constructions against their audited
   sketches** (definitions, not tactics): `bufferedCompTM`'s three-block
   layout, live administrative states, and exact `|y| + 2` rewind ledger
   (phase-4 finding 3 and epoch-1 finding 11 dispositions); `sweepTM`'s
   tagged-payload alphabet `Γ ⊕ Option (Fin k × (Option Γ × Bool × Bool))` —
   verify a *marked blank* is representable and distinct from both the
   physical blank and the boundary (the phase-2 round-1 correction), the
   saved-neighbor-flag mechanism for single-pass head movement, and the
   closed-form `S_k(t) = 2kt² + (5k+4)t + 2k + 2 ≤ (9k+6)(t+1)²`;
   `foldTM`'s alphabet `Bool × Option Γ × Option Γ` (the phase-2 round-2
   correction), canonical blank packing (`foldPack`), stationary fold
   crossings, and the `foldSafe` layer establishing `NonnegativeHeads` on
   **every** input (case A14) — note the delivered constant is `1` with a
   single initialization step.
3. **`alphabet_reduction` deviations**: the one-hot code (width
   `card Γ + 1`) instead of the sketch's logarithmic width — confirm this is
   within the statement's existential constant and the docstring appendix
   says so honestly; the output decoder totalization off `e`'s image
   (`arEmission_in_image` via `output_prefix`).
4. **Confirm the four remaining sorries** match their audited forms and that
   their sketches remain implementable — in particular whether epoch 3's
   `exists_effectiveMachineCode` canonizer sketch can now cite the *proved*
   `computesFunInTime_comp`/`exists_comp_partial`, and whether `universal`'s
   sketch composes with the now-public buffered-simulation layer.
5. Assess attestations 1-6, including the scoped `synthInstance.maxSize`
   reasoning (attestation 4) and the policy-conformance dispositions
   (attestation 5).

## Specific questions

1. `VirtualTag` constrains only boundary positions and leaves interior tags
   free; `bufferedSecondCfg_run` threads the tag existentially. Is there any
   reachable configuration where an unconstrained interior tag could suppress
   a legitimate move (`virtualMove` fires only on a blank read — interior
   buffer cells are never blank; challenge this)?
2. `bufferedCompTM`'s phase-one action writes `(a.output.map some, if
   a.output = none then 0 else .pos)` on the buffer: confirm the buffer-head
   invariant (head = emitted length, at the right blank) survives the
   simulated *halting* transition emission, which `bufferedFirstCfg_step`
   claims to include.
3. B's controller records the *left-neighbor* head flag in each cell during
   the forward sweep and carries *right-neighbor* flags in control on the
   return sweep, enabling both movement directions in one return pass — is
   this bookkeeping sound at zone edges (fresh blocks written at both ends
   each macro-step), and does `source_bounds` justify the `[-t, t]` zone?
4. C's `nonnegative_heads` claims constant `1` (one initialization step, then
   one physical step per source step): verify `T n + 1 ≥ 1 + τ` covers the
   initialization accounting for every halting time `τ ≤ T n`, including
   `n = 0`, and that `foldSafe` really quantifies over arbitrary
   (non-embedded) inputs as `NonnegativeHeads` requires.
5. The three shared-lemma/promotion requests on file: C requests
   `arUpdated_tape` (optional-write normalization) for `Simulation.lean`; B
   lists candidates in its report. Which promotions do you endorse for the
   epoch-3 merge, and with what statements?
6. Adversarial instantiations: `M₁` emitting on its halting transition
   through `exists_comp_partial`; `y = []` and `x = []` through the buffered
   layer; `k = 0` through `one_work_tape` and `alphabet_reduction`; a source
   machine that never moves through `sweepTM` (zone stays `[0, 0]`?);
   `Γ = Bool` with `e = id` through `alphabet_reduction`; `T = 0`-valued
   bounds (note `not_computesInTime_zero` makes such hypotheses vacuous).

## Scope

| Item | Where |
|---|---|
| Files under audit | `Simulation.lean` (26 new public decls + module docstring addition), `Composition.lean` (two fills + appendices), `SingleTape.lean`, `Bidirectional.lean`, `AlphabetReduction.lean` (fills + private layers), `StateRenaming.lean` + `Finite.lean` (refactor surface, new since the last audited commit); all 24 modules attached |
| Source text | Arora & Barak 2009, §1.3 (Claims 1.5, 1.6, 1.8; PDF pp. 41-44) for the three simulations; §1.2 for the model |
| Context | `AroraBarakChapter1Plan.md`, `policy.md`, `audits/epoch1-{findings,resolutions}.md`, `audits/phase2-{findings,reaudit-findings}.md` (the corrected construction designs), briefs `briefs/epoch2-batch{A,B,C}.md`, agent reports `audits/epoch2-agent-reports/` |
| Out of scope | tactic proofs; statements confirmed in closed rounds beyond the freeze check; legacy `NPReductions/*` style findings (recorded, deferred) |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.

---

# ATTACHMENT A — Agent delivery reports (per batch)

## ===== audits/epoch2-agent-reports/batchA.md =====

# Epoch 2, Batch A — guarded composition

Both targets are filled with kernel-checked proofs. The timed theorem uses the explicit constant **2**. The final 24-module sweep exits 0, with zero errors and exactly the seven out-of-scope admissions. Both targets depend only on `[propext, Classical.choice, Quot.sound]`.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch: `complexity/arora-barak-ch1`.
- Verified base: `246871220af82a033d5bf869195b081dbd45fb02`.
- Local delivery branch: `fill/epoch2-A`.
- Delivery commit: `d01fd6e000799a7824adecb6db1c66e06753ef98`.
- Specification: `briefs/epoch2-batchA.md`, read from the subsequent briefs commit `60bdab6b625b92622e07e694b50dfcffd670efba`; implementation is based on the required `24687122` pin.
- Execution: one agent, no delegation. No push or PR was attempted.

## Targets filled and relation to the sketches

### 1. `Turing.FinTM.exists_comp_partial`

Filled and checked before filling the timed target. The witness is the shared `bufferedCompTM M₁ M₂`.

The implementation uses `M₁.k + (1 + M₂.k)` tapes, with the single buffer between the two work blocks. Its state type is

```lean
Option M₁.State ⊕ (Unit ⊕ (M₂.State × Bool))
```

The complete correctness argument is as follows.

1. `bufferedFirstCfg` embeds any first-machine configuration. Its native input head and first work block are unchanged; its real output is `[]`; its second work block is blank. The buffer contains exactly the simulated emitted prefix, beginning at cell 0, and its head is at the prefix length. `bufferTape_append` proves that writing an emission changes exactly the old right blank. `bufferedFirstCfg_step` therefore gives one physical step per simulated step, including an emission on the halting transition.
2. The simulated state `none` is embedded as a **live** state `some (.inl none)`. First-phase lockstep holds through the first halting transition. If the first machine never halts, it holds for every time; hence no composite configuration can be halted.
3. From the completed buffer, the first left move is unconditional. It reaches scan position `|y|`; the scan then takes `|y| + 1` further transitions to reach cell 0 and dispatch. `bufferedFirstCfg_rewind` proves the exact total `|y| + 2`. All administrative states are live and nonemitting.
4. The second phase represents native virtual position `p` by physical buffer position `(p.val : ℤ) - 1`. `bufferTape_inputSymbol` proves equality of the virtual and physical reads. `VirtualTag` requires false at virtual position 0 and true at position `|y| + 1`, allowing either tag in the interior. `virtualMove` suppresses precisely the outward boundary move. `virtualMove_correct` proves the head equation and preservation of the tag, including stationary and suppressed moves. Dispatch sets the tag to true; for `y = []`, cell 0 is its right blank and cell −1 is its left blank, as required.
5. `bufferedSecondCfg_step` and `bufferedSecondCfg_run` give exact same-time correspondence with the second machine, including absorbing halting. The first block and physical input head are inactive; the second block starts fresh; only second-phase emissions reach the real output.
6. For the forward implication, a completed composite run first forces the first machine to halt by item 2. Choose its completed output. `bufferedComp_start` supplies a verified second-phase start. Extend the completed composite run beyond this prefix by absorbing halting and apply second-phase lockstep; this gives a completed second computation with the same output. For the reverse implication, concatenate the verified prefix with the supplied completed second computation. Output uniqueness identifies the intermediate word at the chosen first halting time.

This follows the audited buffered construction, with an explicit Boolean arrival tag and an exact rewind ledger. It requires no totality hypothesis. Administrative transitions cannot introduce extra completed outputs; divergence of either required component is preserved by the proved iff.

### 2. `Turing.FinTM.computesFunInTime_comp`

Uses the same witness and the same proved invariants. There is no second simulator construction. For each input `x`, set `n = |x|` and `y = f x`. The checked bounds are

\[
\begin{aligned}
|y| &\le T_1(n),\\
a &\le T_1(n)+|y|+2,\\
T_2(|y|)&\le T_2(T_1(n)),\\
a+T_2(|y|)
&\le 2T_1(n)+T_2(T_1(n))+2\\
&\le 2\bigl(T_1(n)+T_2(T_1(n))+1\bigr).
\end{aligned}
\]

Here `a` is the phase-two start supplied by `bufferedComp_start`. The first inequality is the existing `output_length_le`; the second comes from choosing the first halting time and the exact rewind. The third is the explicit application `hT₂ hlen` of `Monotone T₂`. Second-phase lockstep supplies the computation at time `a + T₂ |y|`, and `ComputesInTime.mono` weakens its bound to the stated expression. Thus `c = 2` discharges the original frozen conclusion.

## New declarations — complete inventory

All 26 new declarations are public in `TCSlib/Complexity/TuringMachine/Simulation.lean`, in namespace `Turing.FinTM`. Each has a docstring; substantial proofs include sketches. There are **no new private declarations**, including in `Composition.lean`.

| Declaration | One-line statement or definition |
|---|---|
| `tapeBlocks` | Combine a left block, one buffer entry, and a right block using nested `Fin.addCases`. |
| `tapeBlocks_left` | Projecting a left-block index returns the corresponding left entry. |
| `tapeBlocks_buffer` | Projecting any index of the singleton middle block returns its buffer entry. |
| `tapeBlocks_right` | Projecting a right-block index returns the corresponding right entry. |
| `bufferTape` | Store a word from integer cell 0 onward, with all other cells blank. |
| `bufferTape_nil` | The empty-word buffer is everywhere blank. |
| `bufferTape_nat` | A nonnegative cell reads the optional list entry at that natural index. |
| `bufferTape_left` | Cell −1 is blank for every word. |
| `bufferTape_append` | Appending a bit equals updating only the old right-blank cell. |
| `VirtualTag` | A tag is false at the left boundary and true at the right boundary; interior tags are unrestricted. |
| `virtualMove` | Suppress a blank-boundary outward move selected by the tag; preserve all other moves. |
| `virtualNextTag` | Record the last nonzero movement, retaining the tag on a stationary move. |
| `bufferTape_inputSymbol` | Buffer lookup at virtual position minus one equals the native input-symbol read. |
| `virtualMove_correct` | Physical buffer movement agrees with `moveInputPos`, and its next tag remains valid. |
| `bufferedCompTM` | The finite buffered two-phase machine, with live rewind states and virtual second input. |
| `bufferedFirstCfg` | Embed phase one with exact output buffering, empty real output, and a fresh second block. |
| `bufferedFirstCfg_init` | The composite initialization equals the embedded first-machine initialization. |
| `bufferedFirstCfg_step` | A live first-machine step commutes with the first-phase embedding. |
| `bufferedFirstCfg_run` | First-phase lockstep holds at time `t` if the simulated run is live before `t`. |
| `bufferedSecondCfg` | Embed a virtual-input configuration, retaining arbitrary inactive first tapes and physical input position. |
| `bufferedSecondCfg_step` | A valid second-phase embedding steps to a matching configuration with a valid next tag. |
| `bufferedSecondCfg_run` | At every time the second-phase run matches the virtual run with some valid tag. |
| `bufferedScanCfg` | The live rewind configuration with buffer head at integer position `j − 1`. |
| `bufferedScanCfg_run` | From `j ≤ |y|`, scan and dispatch in exactly `j + 1` steps to second initialization. |
| `bufferedFirstCfg_rewind` | From a halted first configuration, reach second initialization in exactly `|output| + 2` steps. |
| `bufferedComp_start` | A first computation completed by `t₁` reaches second initialization within `t₁ + |y| + 2` steps. |

The tape partition and complete buffered simulator form one reusable layer in `Simulation.lean`; every helper precedes its use. Final file lengths are 896 lines for `Simulation.lean` and 651 for `Composition.lean`.

## Requested shared lemmas

None. The reusable buffer and virtual-input infrastructure is already public in the owned shared module. No vendored or other shared file was changed.

## Escalations

None. Both original statements were proved without changing their names, hypotheses, signatures, statements, or attribution.

## Docstring appendices added

- `computesFunInTime_comp`: appended the implementation's tape count, exact rewind charge, and the constant `2`.
- `exists_comp_partial`: appended the tag invariant, empty-word dispatch behavior, live administrative states, and the forward-direction absorbing-halting argument.
- `Simulation.lean` module contents: added an entry identifying the buffered simulator and its exact rewind ledger.

The pre-existing sketches were retained. Every out-of-scope sorry and its sketch is untouched.

## Verification evidence

- `final-sweep.log`: complete output of the final prescribed sweep; exit **0**, **24 fresh nonempty oleans**, **zero `error:` diagnostics**. The checker is unchanged and requires successful Lean exit, no error diagnostics, and a fresh output per module.
- Exactly **seven** `declaration uses 'sorry'` warnings remain, at the declarations below. The only other diagnostics are the three pre-existing linter warnings in `Configuration.lean`. Neither owned module emits any warning.
- `axioms.log`: both targets print exactly `[propext, Classical.choice, Quot.sound]`; neither footprint contains `sorryAx`. `Axioms.lean` is the exact scratch input, originally run outside the repository using the same `LEAN_PATH` construction as the checker.
- `statement-freeze.json`: comment-stripped comparison against the pin confirms unchanged headers for all **38** pre-existing declarations (17 in Composition, 21 in Simulation) and unchanged bodies for all existing non-target declarations.
- `verification.json`: records the module outputs, pinned dependency revisions, exits, and diagnostics. Every dependency source checkout contributing to the checker's path is clean and matches `lake-manifest.json`.
- `git diff --check` passed. The committed diff contains exactly the two owned source files. The local branch is clean after commit.
- `bundle-verify.log`: Git accepts the exported incremental bundle and its prerequisite. The format-patch also passes `git apply --reverse --check` against the delivered source state.

| Remaining declaration | File |
|---|---|
| `alphabet_reduction` | `TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean` |
| `one_work_tape` | `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean` |
| `nonnegative_heads` | `TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean` |
| `oblivious_of_mem_DTIME` | `TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean` |
| `exists_effectiveMachineCode` | `TCSlib/Complexity/TuringMachine/Encoding.lean` |
| `universal` | `TCSlib/Complexity/TuringMachine/Universal.lean` |
| `timed_universal` | `TCSlib/Complexity/TuringMachine/Universal.lean` |

Toolchain: Lean 4.25.0 release `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Initial `lake exe cache get` reached a ProofWidgets cloud-release failure. `lake exe cache unpack` then successfully restored 1539 matching local cache files. The required fresh-clone bootstrap sweep passed before source edits; iteration used Simulation before Composition; the final full sweep checked all downstream modules. No project `lake build` was used.

This runtime needed the supplied `lean_proc_compat.c`: it redirects only `readlink("/proc/<own-pid>/exe")` to `readlink("/proc/self/exe")` so the unmodified Lean/Lake executables locate their installation. It was compiled as a shared library and set through `LD_PRELOAD` for setup and all Lean checks. It changes no Lean source, executable, proof checker, declaration, or cache content.

The exact final sweep command, from the repository root with the pinned toolchain available, was:

```bash
( while read -r m; do
    bash scripts/lean_check_tree.sh "$m" || exit 1
  done < scripts/ab_ch1_module_order.txt )
```

## Delivery and checklist

The ZIP contains the complete modified sources at repository-relative paths, this report, `epoch2-A.patch`, `epoch2-A.bundle`, both mandatory logs, and supplemental verification evidence. The bundle requires the base commit; it contains the local `fill/epoch2-A` branch. The patch was produced by `git format-patch 24687122 --stdout`.

`SHA256SUMS` hashes every other file in the ZIP. Its own SHA-256 is recorded in the ZIP comment, giving every archive member a checkable digest without a self-referential hash claim.

- [x] Both targets filled, with correspondence to the audited sketches.
- [x] Every new public/private declaration listed.
- [x] Requested shared lemmas: none.
- [x] Escalations: none.
- [x] Docstring appendices listed; original sketches preserved.
- [x] Full-sweep and axiom logs included; zero errors and exactly seven remaining admissions.
- [x] Diff touches only the two owned files.
- [x] Work committed locally; patch, bundle, complete sources, and hash coverage supplied.

Notation glossary: `M₁`, `M₂` are the input machines; `x` is the original input, `n = |x|`, and `y` is the completed intermediate word (`f x` in the timed proof). `T₁`, `T₂`, `f`, `g`, and `c` are the original theorem parameters. `a` is the verified phase-two start time; `p` is a virtual input position; `j` is a rewind scan position; `t` and `t₁` are step bounds. `|·|` is word length. Lean names retain their source meanings.

## ===== audits/epoch2-agent-reports/batchB.md =====

# Epoch 2, Batch B — one work tape

`Turing.FinTM.one_work_tape` is proved. The construction follows the audited
tagged-payload, interleaved-tape, two-sweep design, with a separate zero-work-tape
lockstep case. The final 24-module chapter sweep passed; the target depends only
on `propext`, `Classical.choice`, and `Quot.sound`.

## Repository and scope

| Item | Value |
|---|---|
| Repository | `https://github.com/Shilun-Allan-Li/tcslib` |
| Requested source branch | `complexity/arora-barak-ch1` |
| Verified base commit | `246871220af82a033d5bf869195b081dbd45fb02` |
| Local delivery branch | `fill/epoch2-B` |
| Delivery commit | `40eaff86e0ac818a3194cab37c57a993cecc646c` |
| Commits after base | One |
| Changed repository file | `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean` |
| Final source length | 1315 lines |
| Final source SHA-256 | `25e0cb9c28e1f99b9c9be6507be08e219d3e9e5dded4021b989c5fad1e81f003` |
| Working tree after commit | Clean |

The brief was read from the requested branch; implementation is based on the
brief's explicitly pinned commit. `policy.md`, plan §5, the two phase-2 audit
reports, the target sketch, and the relevant existing simulation constructions
were read. There was no push, PR, shared-file modification, or vendored-file
modification. All work was performed in this one batch without sub-agents.

The target signature is byte-for-byte identical to the base. Its original sketch
and attribution are retained, followed by the implementation note below. The
entire `one_work_tape_binary` docstring, declaration, and proof are byte-for-byte
identical to the base. The three original file-level `set_option` headers remain.
The owned source contains no `sorry`, `axiom`, `unsafe`, or `native_decide` token.
`freeze-check.json` records these comparisons.

## Brief checklist

- [x] Target filled; relationship to the sketch and the zero-tape path documented.
- [x] Every new authored private declaration listed, with a complete generated
  declaration inventory in the appendix.
- [x] Requested shared lemmas recorded.
- [x] File-size escalation recorded; no mathematical obstruction.
- [x] Appended target docstring note identified and reproduced.
- [x] Complete final sweep and axiom logs attached: zero errors and exactly the
  eight specified remaining sorry warnings.
- [x] Diff changes only `SingleTape.lean`; binary corollary untouched.
- [x] Local commit, format patch, incremental Git bundle, complete source, report,
  and SHA-256 manifest included.

## Construction and proof

### Zero work tapes

`unusedTapeTM` preserves the original control and native input/output action and
adds one work tape whose head stays at zero and whose contents stay blank. The
configuration embedding commutes with one step, including a halted step.
`unusedTape_computes` lifts this to runs and preserves the original time bound.
The conclusion then uses the identity alphabet embedding and constant `1`, since
`T(n) ≤ (T(n) + 1)²`. This branch has no sweeps or setup cost.

### Alphabet, finite control, and layout for positive k

Write `k = M.k`. The internal cell type is

```lean
Fin k × (Option Γ × Bool × Bool)
```

Its fields are the source tape index, payload, current head flag, and saved
left-neighbor head flag. The enlarged alphabet is

```lean
Γ ⊕ Option (Fin k × (Option Γ × Bool × Bool))
```

`Sum.inl` embeds source input/output symbols as unmarked data symbols. Internal
cells use `Sum.inr (some cell)`; `Sum.inr none` is the boundary symbol. The physical
blank is the outer `none` of the machine's work-tape `Option` type. Consequently
an internal cell with payload `none` and head flag `true` is a representable
marked blank, distinct from both a physical blank and a boundary.

`tapeRow` lists the `k` indexed cells in increasing tape-index order, and
`tapeZone` concatenates consecutive rows. After `t` simulated steps the interval
is `[-t, t]`, with `2t + 1` blocks; the physical left boundary is at `-t*k - 1`.
Thus a source coordinate `j` and tape index `i` occupy physical cell `j*k + i`.
Coordinates and interval lengths are proof parameters, not fields of the finite
controller.

The six controller phases are `init`, `back`, `growLeft`, `read`, `growRight`, and
`write`. They contain only finite source states, finite counters, symbols, and
tables indexed by `Fin k`. Both the finiteness and decidable-equality instances
are explicit private declarations, using the controller's sum/sigma
representation. The equality instance locally raises only the typeclass search
size bound to accommodate that representation.

### The two sweeps

Initialization writes the origin block with all `k` blank source heads marked,
sets the right boundary, returns over that block, and writes the left boundary.

For each live source step, the machine first writes one fresh blank block at the
left and moves the boundary. The forward sweep records each marked payload in a
finite table and saves each tape's previous head flag in the next cell of that
tape. At the old right edge, it writes one fresh right block, including the saved
left flags. The completed table is exactly the source's scanned-symbol tuple.

At the new right boundary the machine applies the source's native input movement
and mapped output emission once and turns left. On the return sweep it updates
each old-head payload according to the source action. The new head flag comes
from the old right-neighbor flag for a left move, the current flag for a stay, or
the saved left-neighbor flag for a right move. The return control carries each
tape's old right-neighbor flag. This permits both movement directions in a single
return pass. At the left boundary the controller installs the source's next state
or halts.

`source_bounds` proves by elapsed-time induction that source heads and nonblank
support lie within `[-t, t]`. It supplies the fresh-guard hypotheses. Generic
zipper and list-transduction lemmas establish exact-cost physical sweeps;
`read_row`, `write_row`, `read_zone`, and `write_zone` connect those sweeps to the
source configuration. `sweep_prepare` and `sweep_finish` compose into
`sweep_step`, preserving the entire canonical configuration, not merely the
output. `sweep_run_to_halt` then inducts to the source's first halt.

`sweepPos`, `sweepPos_move`, and `sweepInput_read` connect the true read-only input
tape to `x.map e`, including its endpoints. Output emissions are mapped through
the same embedding. No buffering or alternative input/output model is introduced.

### Exact costs and the quadratic bound

Let `S_k(t)` denote the simulator time at the boundary after `t` source steps.

| Quantity | Formal value |
|---|---|
| Initialization | `S_k(0) = 2k + 2` |
| One step with n old blocks | `(2n + 5)k + 4` |
| One step at source time t, where n = 2t + 1 | `(4t + 7)k + 4` |
| Recurrence | `S_k(t+1) = S_k(t) + (4t + 7)k + 4` |
| Closed form | `S_k(t) = 2kt² + (5k + 4)t + 2k + 2` |
| Uniform bound | `S_k(t) ≤ (9k + 6)(t + 1)²` |

These are proved by `sweep_step`, `sweepTime_eq`, and `sweepTime_le`. If the given
machine halts within `T(|x|)`, its least halting time `τ` satisfies
`τ ≤ T(|x|)`. The simulation reaches the matching halted configuration at
`S_k(τ)`; halt absorption identifies its output with `f x`. Monotonicity then
gives the required bound with constant `9k + 6`. No exact book constant or lower
bound on `T` is assumed.

Notation used here: `Γ` is the source alphabet, `Γ'` the enlarged alphabet,
`e` its symbol embedding, `k` the source work-tape count, `j` a source tape
coordinate, `i` a tape index, `t` elapsed source steps, `n` the current block count,
and `τ` the first source halt time.

## New private declarations

All 75 authored declarations below are `private`, in namespace
`Turing.FinTM`, and precede the target. Lines refer to the included complete
source. Descriptions reproduce the declaration documentation. All are technical
components of the existing [AB09, Claim 1.6] analogue, rather than new public claims.

| Declaration | Kind | Line | Role |
|---|---|---:|---|
| `unusedTapeTM` | def | 60 | Add one unused work tape to a machine with no work tapes. |
| `unusedTapeCfg` | def | 70 | The unused tape is blank and its head stays at the origin. |
| `unusedTape_step` | lemma | 75 | The zero-tape embedding commutes with a single transition, including halt. |
| `unusedTape_computes` | lemma | 93 | The zero-tape path is a lockstep simulation; no sweep or initialization is needed. |
| `sweepTape` | def | 107 | A finite tape zipper; the left list is stored nearest-cell first. |
| `sweepTape_read` | lemma | 112 | Read the current cell of a zipper. |
| `sweepTape_right` | lemma | 121 | A write followed by a right move transfers one cell to the left stack. |
| `sweepCfg` | def | 139 | A configuration at a sweep frontier, with arbitrary native input and output. |
| `sweepAct` | def | 144 | A sweep's local write, with the native input and output left stationary. |
| `sweepCfg_right` | lemma | 148 | The one-cell tape identity lifts to configurations. |
| `sweepFold` | def | 162 | A finite-state left-to-right transduction, recording both its final state and its rewritten word. |
| `sweep_run` | lemma | 175 | A local transition rule realizes a complete finite forward sweep. |
| `sweepRevCfg` | def | 205 | The same zipper viewed while scanning toward decreasing coordinates. |
| `sweepRevCfg_left` | lemma | 211 | Reflection converts the forward zipper identity into a left-moving step. |
| `sweep_run_reverse` | lemma | 228 | The finite transduction lemma for the return sweep, with the exact cost. |
| `sweepTape_turn` | lemma | 257 | Turning round exchanges the two finite stacks. |
| `sweepFold_append` | lemma | 269 | Concatenating two scans threads the finite control between them. |
| `indexedVisit` | def | 280 | A transducer whose state is a table, changing only the entry named by a cell. |
| `indexedFold` | lemma | 291 | On a block with distinct tape indices, each local rule sees the original table entry. This is the block invariant for both sweeps. |
| `indexedFold_block` | lemma | 318 | Each simulated tape contributes exactly one cell to an interleaved block. |
| `SweepCell` | abbrev | 328 | A cell stores a tape index, an optional payload, the head flag, and the left-neighbor head flag recorded by the forward sweep. |
| `readVisit` | def | 331 | The forward rule reads marked payloads and records the preceding head flag. |
| `writeVisit` | def | 339 | The return rule writes the old head's payload and determines the new head from the old flags at its left, current, and right neighbors. |
| `headAt` | def | 349 | The ghost head flag at a source coordinate. |
| `tapeRow` | def | 353 | One interleaved block; `read = true` includes the recorded left flag. |
| `readState` | def | 359 | The forward control immediately before reading block `j`. |
| `read_row` | lemma | 364 | Reading a whole block advances the control invariant by one coordinate. |
| `indexedFold_block_reverse` | lemma | 383 | The return sweep's block rule is valid in reverse tape-index order too. |
| `write_row` | lemma | 397 | A return-sweep block performs exactly the source action on that coordinate. |
| `tapeZone` | def | 425 | Consecutive interleaved blocks, in ascending coordinate order. |
| `read_zone` | lemma | 430 | The forward sweep processes any consecutive block interval. |
| `write_zone` | lemma | 442 | The return sweep processes the same interval in reverse order. |
| `sweepTape_nil` | lemma | 456 | One blank cell can be made explicit at the end of the zipper. |
| `sweepCfg_right_any` | lemma | 465 | The forward write identity also applies beyond the stored zone. |
| `sweepRevCfg_left_any` | lemma | 482 | The backward write identity also applies beyond the stored zone. |
| `sweep_generate` | lemma | 500 | A fixed finite sequence of writes, in either direction, takes its exact length. The hypothesis is the local controller rule, and has no global-run premise. |
| `SweepAlphabet` | abbrev | 523 | An enlarged symbol is input/output data, an internal cell, or a boundary. |
| `sweepEmbed` | def | 526 | Encode a source symbol as an unmarked data symbol. |
| `sweepBoundary` | def | 530 | A nonblank internal boundary, distinct from every payload (including blank). |
| `sweepSymbol` | def | 533 | Tag a complete internal cell. |
| `sweepInput` | def | 537 | Interpret the unchanged native input alphabet. |
| `SweepState` | inductive | 542 | Finite controller phases; unbounded coordinates never enter the state. |
| `sweepStateFintype` | instance | 551 | Enumerate the finite control through its finite sum/product representation. |
| `sweepStateDecidableEq` | instance | 555 | Equality of controller states is decidable through the same representation. |
| `sweepMove` | def | 562 | A stationary-input/output action that preserves the cell it scans. |
| `sweepTM` | def | 568 | The finite controller for the two sweeps and their boundary extensions. The forward sweep records left-neighbor flags in the cells. The backward sweep keeps right-neighbor flags in its control, so it needs no extra scan. |
| `source_bounds` | lemma | 619 | Source heads and nonblank cells stay within the elapsed-time interval. |
| `blankRow` | def | 653 | The initialized interleaving has `k` marked blank cells. |
| `tapeRow_blank` | lemma | 657 | A row outside both the source heads and the written support is blank. |
| `tapeRow_length` | lemma | 667 | The size of each block is the number of source tapes. |
| `tapeZone_length` | lemma | 672 | Zone length is the block count times the source tape count. |
| `tapeZone_append` | lemma | 682 | Split a zone at a block boundary. |
| `sweepPos` | def | 692 | The native input position is unchanged numerically by symbol embedding. |
| `sweepPos_move` | lemma | 697 | Input-head movement commutes with the unchanged-length symbol embedding. |
| `sweepInput_read` | lemma | 705 | The input read by an encoded configuration is the encoded source read. |
| `sweepStart` | def | 720 | Canonical configurations at the left boundary between simulated steps. |
| `sweepTape_write` | lemma | 729 | Replacing the current cell preserves both tails of the zipper. |
| `sweep_turn_left` | lemma | 743 | Write a boundary and turn from a forward scan into a backward scan. |
| `sweep_turn_right` | lemma | 756 | Write the left boundary and turn toward the first forward-scan cell. |
| `sweep_init_block` | lemma | 773 | Initialization writes the marked origin block in exactly `k` steps. |
| `sweep_grow_left_block` | lemma | 797 | Growing the left boundary writes exactly one reversed blank block. |
| `rightRow` | def | 822 | The right guard block records the flags from the last scanned block. |
| `sweep_grow_right_block` | lemma | 826 | Growing the right boundary writes one guard block, retaining the collected reads. |
| `sweepFold_id` | lemma | 850 | A sweep with the identity rule only changes the physical scan frontier. |
| `sweepRevCfg_write` | lemma | 857 | Writing without moving in a backward-facing zipper. |
| `sweep_init` | lemma | 874 | Initialization builds the marked origin block and both boundaries. |
| `sweepCfg_stay` | lemma | 924 | A stationary phase change preserves a forward-facing tape. |
| `sweepRevCfg_stay` | lemma | 930 | A stationary phase change preserves a backward-facing tape. |
| `sweep_prepare` | lemma | 942 | The first half of a simulated step grows the left guard and collects all marked source symbols. Its exact cost includes both phase changes. |
| `sweep_finish` | lemma | 1030 | The second half grows the right guard, executes the native input/output action once, rewrites the zone, and enters the next boundary configuration. |
| `sweep_step` | lemma | 1139 | One source transition is one bounded burst, preserving the complete zone shape and growing it by one block at each end. |
| `sweepTime` | def | 1157 | Exact transition count after a given number of source steps. |
| `sweepTime_eq` | lemma | 1162 | Summing the exact per-step costs gives a quadratic polynomial. |
| `sweepTime_le` | lemma | 1169 | A single constant bounds initialization and all sweeps, at every input size. |
| `sweep_run_to_halt` | lemma | 1188 | Up to the source's first halt, initialized runs agree at every macro boundary. |

`SweepState` also introduces the private constructors `init`, `back`, `growLeft`,
`read`, `growRight`, and `write`. Lean generates recursors, constructor theorems,
matchers, equation theorems, private proof auxiliaries, and the representation
used by the two private instances. The complete exact-name inventory is included
in the appendix and independently in `declarations.log`.

## Requested shared lemmas

These are requests for a later coordinated change; this batch keeps the private
copies above and changes no shared file.

| Suggested shared home | Private components to consider promoting | Purpose |
|---|---|---|
| `Simulation.lean` or a maintainer-approved sweep helper module | `sweepTape`, `sweepCfg`, `sweepRevCfg`, their write/move/turn lemmas, `sweepFold`, `sweep_run`, `sweep_run_reverse`, `sweep_generate` | Reusable finite-word sweep and generation proofs with exact costs and native input/output preservation. |
| `Simulation.lean` | `indexedVisit`, `indexedFold`, `indexedFold_block`, `indexedFold_block_reverse` | Independent finite-table updates over distinct tape indices. |
| `Simulation.lean` / `Finite.lean`, as maintainers choose | `unusedTapeTM`, `unusedTapeCfg`, `unusedTape_step`, `unusedTape_computes` | The zero-work-tape lockstep embedding into one unused work tape. |
| `Simulation.lean` | `source_bounds` | General elapsed-time head and support bounds on initially blank work tapes. |

## Escalations

No mathematical obstruction or statement change was needed.

**File size / future extraction:** the owned file is 1315 lines,
above policy §1's approximate 1000-line threshold. The proof is decomposed into
75 private components, including a generic sweep layer and two explicit
macro-step halves. A maintainership follow-up should move reusable sweep and
finite-table infrastructure into a shared location, then shorten this file's
imports and local proof. This delivery keeps the construction in the one owned
file as the batch explicitly requires; no unilateral file split or shared API
change has been made. This is a structural follow-up, not an unfilled proof.

## Docstring appendices

Only the following implementation note was appended to the existing target
sketch; its preceding paragraphs remain intact:

```text
**Implementation note.** The forward pass records the preceding block's head
flags in the cells; the return pass carries the following block's flags in its
finite control. This implements both movement directions using exactly the two
stated sweeps. Each macro-step extends the zone by one blank block at each end.
For positive `k`, initialization costs `2k + 2` transitions and source step `t`
costs `(4t + 7)k + 4`; `sweepTime_le` supplies the constant `9k + 6`.
The zero-tape branch is a separate lockstep embedding with constant `1`.
```

The new nontrivial helper proofs have their own local explanatory documentation,
including explicit sketches for the sweep invariant, block invariant, bounds,
initialization, both macro-step halves, and induction to halt.

## Verification evidence

The repository's prescribed `scripts/lean_check_tree.sh` was used throughout. It
deletes each old output before checking and rejects a nonzero Lean exit, an
`error:` diagnostic, or a missing fresh `.olean`. `lake build` was never run.

| Check | Outcome | Evidence |
|---|---|---|
| Bootstrap full chapter sweep | Exit 0; 24 modules; the original 9 sorry warnings | `bootstrap-sweep.log` |
| Final owned-module check | Exit 0; no output or warnings | `owned-check.log` |
| Downstream suffix after the owned module | Exit 0; all 15 downstream entries | `downstream-sweep.log` |
| Final full chapter sweep | Exit 0; 24 modules; zero `error:` lines | `final-sweep.log` |
| Final axiom scratch check | Exit 0 | `axioms.log`, `verification/Axioms.lean` |
| Module declaration inventory | Exit 0; 284 recorded constants | `declarations.log`, `verification/Declarations.lean` |
| Scope and frozen statements | All comparisons pass | `freeze-check.json` |
| Patch and bundle integrity | Replay/source comparisons pass | `package-check.json`, `bundle-verify.log` |

The complete final sweep output is attached without truncation. It contains
exactly these eight `declaration uses 'sorry'` warnings:

| Declaration | File under `TCSlib/Complexity/TuringMachine/` | Line |
|---|---|---:|
| `computesFunInTime_comp` | `Composition.lean` | 361 |
| `exists_comp_partial` | `Composition.lean` | 409 |
| `alphabet_reduction` | `Robustness/AlphabetReduction.lean` | 69 |
| `nonnegative_heads` | `Robustness/Bidirectional.lean` | 76 |
| `oblivious_of_mem_DTIME` | `Robustness/Oblivious.lean` | 109 |
| `exists_effectiveMachineCode` | `Encoding.lean` | 455 |
| `universal` | `Universal.lean` | 102 |
| `timed_universal` | `Universal.lean` | 165 |

There are also three pre-existing `Configuration.lean` linter warnings: two
unnecessary-sequence-focus warnings (lines 137 and 155) and one unused-variable
warning (line 140). There are no new owned-file warnings.

The exact final axiom output is:

```text
'Turing.FinTM.one_work_tape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.one_work_tape_binary' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`one_work_tape_binary` still depends on `sorryAx` because the separately owned
`alphabet_reduction` remains unfilled at this base. Its other input theorem,
`one_work_tape`, has no such dependency. Neither declaration was weakened.

The axiom and declaration probes were executed from scratch files outside the
repository, using exactly the check script's `LEAN_PATH` construction:

```bash
LP="$PWD/.lake/tcslib-check-oleans"
[ ! -d "$PWD/.lake/build/lib/lean" ] || LP="$LP:$PWD/.lake/build/lib/lean"
for d in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do
  [ ! -d "$d" ] || LP="$LP:$d"
done
export LEAN_PATH="$LP"
lean /absolute/path/outside/repository/Axioms.lean
```

The final sweep command was:

```bash
( while read -r m; do
    bash scripts/lean_check_tree.sh "$m" || exit 1
  done < scripts/ab_ch1_module_order.txt )
```

### Environment

The pinned toolchain is `leanprover/lean4:v4.25.0`, compiler commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`. Mathlib is pinned at
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The repository toolchain and dependency manifest
were not changed. `lake exe cache get` was used for setup; after a slow broad
download was interrupted, the chapter's transitive dependency cache and the
additional precise imports were retrieved with targeted cache requests.

This container's process namespace required a small runtime compatibility shim:
the compiler's `readlink("/proc/<own-pid>/exe", ...)` lookup is mapped to
`readlink("/proc/self/exe", ...)`. The complete C source is attached as
`environment/lean_proc_compat.c`. It was compiled as a shared object and supplied
through `LD_PRELOAD` for Lean/Lake invocations. It affects executable-path
discovery only; all proofs were checked by the pinned Lean kernel. A conventional
environment does not need this shim. For an environment with the same procfs
issue, it can be rebuilt with:

```bash
cc -shared -fPIC -o /tmp/lean_proc_compat.so environment/lean_proc_compat.c -ldl
export LD_PRELOAD=/tmp/lean_proc_compat.so
```

## Archive, replay, and hashes

Required deliverables are at the archive root, except the complete source,
which retains its repository path. Additional audit evidence consists of
`bootstrap-sweep.log`, `owned-check.log`, `downstream-sweep.log`,
`declarations.log`, `freeze-check.json`, `verification-summary.json`,
`package-check.json`, `bundle-verify.log`, the two verification probe files,
and the compatibility-shim C source.

The patch and bundle were produced with the exact requested base range:

```bash
git format-patch 24687122 --stdout > epoch2-B.patch
git bundle create epoch2-B.bundle 24687122..fill/epoch2-B
```

The bundle is incremental and requires the base commit. To replay the patch in
an existing clone containing that base:

```bash
git switch -c review/epoch2-B 24687122
git am /absolute/path/to/epoch2-B.patch
```

Alternatively, import the commit from the bundle without a GitHub write:

```bash
git fetch /absolute/path/to/epoch2-B.bundle fill/epoch2-B:review/epoch2-B
```

An isolated worktree at the base was used to apply-check and apply the patch;
the resulting complete source matched the delivery source and committed blob
byte-for-byte. The bundle was verified against the base and imported into a
separate local ref; its commit and source tree matched the delivery commit.

`SHA256SUMS` contains a sorted SHA-256 entry for every other archive file, with
paths relative to the archive root. As with a standard checksum manifest, it
excludes itself: a literal checksum of the manifest inside itself is a
self-reference and is not a practical hash-manifest format. Run
`sha256sum -c SHA256SUMS` after extraction. ZIP integrity, member set, and all
manifest hashes were checked before delivery.

## Appendix: complete module declaration inventory

The following is the complete sorted output of the attached Lean environment
probe. It contains 280 private constants, including the 75
authored declarations and all generated auxiliaries; the two existing public
headline theorems; and `Turing.Cfg.workTapeSymbols.eq_1` and
`Turing.MultiTapeTM.step.eq_1`, the lazily materialized equation theorems for
unchanged imported definitions. Those two equation theorems are not newly
authored public helpers. No public `SweepState` instance or other new public
helper is introduced.

```text
Turing.Cfg.workTapeSymbols.eq_1
Turing.FinTM.one_work_tape
Turing.FinTM.one_work_tape_binary
Turing.MultiTapeTM.step.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.eq_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepAlphabet
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepCell
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_inst
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.back
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.back.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.back.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.casesOn
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.ctorElim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.ctorElimType
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.ctorIdx
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.noConfusionType
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.proxyType
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.proxyTypeEquiv
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.rec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.recOn
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.blankRow
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.blankRow.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.headAt
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.headAt.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold._simp_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block._simp_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block_reverse
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block_reverse._simp_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block_reverse._simp_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedVisit
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedVisit.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readState
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readState.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readVisit
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.read_row
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.read_row._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.read_zone
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.read_zone._proof_1_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.rightRow
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.rightRow.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.source_bounds
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.source_bounds._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.source_bounds._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.source_bounds._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepAct
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepAct.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepBoundary
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg_right
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg_right_any
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg_stay
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold._sunfold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold._unsafe_rec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.eq_def
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold_append
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold_id
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput_read
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput_read._simp_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepMove
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepMove.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos_move
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_left
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_left._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_left._simp_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_left_any
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_stay
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_write
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_write._simp_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStart
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateDecidableEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepSymbol
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_8
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_6
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_nil
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_read
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_read._simp_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_write
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_write._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._sunfold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._unsafe_rec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime.eq_def
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime_eq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime_le
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_15
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_17
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_8
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._simp_1_10
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._simp_1_16
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._simp_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_10
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init._proof_1_14
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init._simp_1_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_15
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_16
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_8
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_9
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._simp_1_11
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_reverse
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_reverse._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_10
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_11
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_6
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_8
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_9
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_step
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_turn_left
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_turn_right
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_turn_right._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_turn_right._simp_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow_blank
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow_length
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._sunfold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._unsafe_rec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.eq_def
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_append
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_append._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_append._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_length
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_length._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeCfg
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeCfg.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeTM
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeTM.congr_simp
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTape_computes
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTape_step
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row._proof_1_6
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row._proof_1_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row._simp_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_zone
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_zone._proof_1_7
```

## ===== audits/epoch2-agent-reports/batchC.md =====

# Epoch 2, batch C — proof delivery

Both assigned theorems are filled and kernel-checked. The original statements,
hypotheses, names, attributions, and `NonnegativeHeads` definition are unchanged.
Only the two owned source files differ from the required base.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required base: `246871220af82a033d5bf869195b081dbd45fb02`.
- Local branch: `fill/epoch2-C`.
- Delivered head: `63d346933273c527e6a2d81af9bbfeafc92fbd7e`.
- Brief: `briefs/epoch2-batchC.md`, blob `a7a73e6308d1b48e3c2c008984444f5264543c05`,
  read from the requested branch at `60bdab6b625b92622e07e694b50dfcffd670efba` before
  checking out the required base. A copy is in `verification/BRIEF.md`.
- No push, pull request, or remote write was attempted. No delegation was used.

## Checklist

- [x] Both targets filled, in the prescribed order.
- [x] Corrected sketches followed; implementation details explained below.
- [x] Every new authored declaration is private and listed below.
- [x] Requested shared lemma recorded below; shared and vendored files untouched.
- [x] Escalations recorded below.
- [x] Appended implementation notes identified below; original sketches retained.
- [x] Final full sweep exits 0; all 24 modules checked with fresh `.olean` outputs.
- [x] Zero `error:` diagnostics; exactly the seven permitted sorry warnings remain.
- [x] Both target axiom footprints contain no `sorryAx`.
- [x] Complete source files, format-patch, Git bundle, logs, and checksums included.
- [x] Diff touches only the two owned files.

## Target 1: `Turing.FinTM.nonnegative_heads`

The alphabet is exactly `Bool × Option Γ × Option Γ`, and the embedding is
`γ ↦ (false, some γ, none)`. Each physical nonnegative coordinate stores both
source cells, including independent blanks. `foldPack` canonically represents an
untagged pair of blanks as physical `none`; `foldUnpack_pack` establishes the
corresponding decoding identity. The origin is explicitly tagged, including when
both payloads are blank.

The source coordinate is transported by

\[
\phi(z)=\begin{cases}z&0\le z,\\-z-1&z<0.\end{cases}
\]

`foldMove_correct` checks all direction and track cases. A crossing between source
cells zero and minus one stays physically at zero and changes the active track.
`foldTape_update` proves that writing changes exactly the selected payload.
`foldCfg_apply`, `foldCfg_step`, and `foldCfg_run` establish full configuration,
one-step, and initialized-run correspondences, respectively. Input positions and
reads are transported through the embedding, and output is mapped symbolwise.

`foldStartAction` writes the origin tags simultaneously on all work tapes. If its
first input read is invalid, it halts on that same initialization transition.
Otherwise it enters the source's initial state with positive tracks. Subsequent
invalid input reads select a stationary halt before any source transition.
`foldSafe` and its preservation lemmas quantify over **every** enlarged-alphabet
input, independently of the computation premise. They establish nonnegative heads,
correct origin tags, and impossibility of returning to the initialization state.
Zero work tapes and an empty source alphabet are handled by the same construction.

There is one initialization step, followed by one physical step per source step.
Thus the implementation proves the claimed bound with

\[
T(n)+1=1\cdot(T(n)+1),\qquad c=1,
\]

and preserves the work-tape count by definition.

## Target 2: `Turing.FinTM.alphabet_reduction`

The compiler factors through an arbitrary injective block code
`E : Option Γ ↪ (Fin (N + 1) → Option Bool)` satisfying
`E none = fun _ => none`. The final instantiation uses the brief's permitted
arbitrary fixed-width scheme: a one-hot binary code of width
`L = Fintype.card Γ + 1` for nonblank symbols. Logical blank uses an all-physical-blank
block. This deliberately does not optimize the alphabet-dependent constant to the
logarithmic width described in the original sketch.

`arCoords` and `arPos_coords` establish the block address bijection on the entire
integer tape, including negative coordinates. `arTape_at`, `arTape_ext`, and the
update lemmas support the exact tape invariant without an initialization scan.
All machine states are finite: the state stores a source state, bounded phase
counters, a fixed-size read buffer, and a pending transition's work symbols and
movements. The use of classical choice selects a fixed finite code and decoder;
it adds no oracle or infinite control state.

Every live source step is simulated as follows, simultaneously on the existing
work tapes:

| Phase | Physical steps | Effect |
|---|---:|---|
| Read | `L` | Read each block into finite control while moving right. |
| Dispatch | `1` | Decode the source reads, compute its transition, move the native input head, emit at most one decoded bit, and step left to the block's last cell. |
| Write | `L` | Write the replacement block from right to left, finishing at its first cell. |
| Reposition | `L` | Move each physical head in its own source direction. |
| Finish | `1` | Enter the next source-read state or halt. |

Consequently,

\[
L+1+L+L+1=3L+2,
\qquad
(3L+2)T(n)\le(3L+2)(T(n)+1).
\]

The read-only input is used directly, with each bit translated through `e` inside
the transition table. Boundary blanks stay blank. The compiler's total output
decoder returns true exactly on `e true` and otherwise false, so it is an inverse
on both embedded bits. `arEmission_in_image` uses `MultiTapeTM.output_prefix` to
prove that every emitted source symbol on a hypothesis input belongs to the image
of `e`, at every time; after the budget the source has halted. Hence its arbitrary
non-image behavior is unreachable on these runs. The configuration invariant also
proves the stronger correspondence obtained by mapping the entire output through
this total decoder, without needing to restrict arbitrary intermediate configurations.

`arCfg_cycle` assembles the phase proofs; `arCfg_run` iterates them. Absorbing
halting makes sampling at every macro-boundary valid even after the source halts.
`arCfg_init` uses the all-blank property, and `arTM_computes` transfers the completed
output and time bound. The generic construction includes `k = 0`: its finite
controller still executes the positive cycle length, with empty work tuples.
The work-tape count is definitionally unchanged.

## New private declarations

All entries below are in namespace `Turing.FinTM`, are declared `private`, and
precede the target that uses them. The source files provide their complete types
and bodies; Lean-generated equation auxiliaries are internal to these private
definitions. There are 88 authored private declarations.

### `TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean`

| Declaration | Kind |
|---|---|
| `FoldSymbol` | `abbrev` |
| `foldEmbedding` | `def` |
| `foldPos` | `def` |
| `foldSide` | `def` |
| `foldPack` | `def` |
| `foldUnpack` | `def` |
| `foldUnpack_pack` | `lemma` |
| `foldTape` | `def` |
| `foldMove` | `def` |
| `foldPos_nonneg` | `lemma` |
| `foldMove_correct` | `lemma` |
| `foldRead` | `def` |
| `foldRead_tape` | `lemma` |
| `foldWrite` | `def` |
| `foldTape_update` | `lemma` |
| `foldAction` | `def` |
| `foldCfg` | `def` |
| `foldCfg_input` | `lemma` |
| `foldCfg_origin` | `lemma` |
| `foldCfg_apply` | `lemma` |
| `foldDecode` | `def` |
| `foldHalt` | `def` |
| `foldInitAction` | `def` |
| `foldStartAction` | `def` |
| `foldStartAction_embed` | `lemma` |
| `foldTM` | `def` |
| `foldCfg_step` | `lemma` |
| `foldCfg_init` | `lemma` |
| `foldCfg_run` | `lemma` |
| `foldWrite_origin` | `lemma` |
| `foldMove_nonneg` | `lemma` |
| `foldSafe` | `def` |
| `foldAction_safe` | `lemma` |
| `foldHalt_safe` | `lemma` |
| `foldSafe_step` | `lemma` |
| `foldSafe_init` | `lemma` |
| `foldTM_nonnegative` | `lemma` |

### `TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean`

| Declaration | Kind |
|---|---|
| `ArBlock` | `abbrev` |
| `arCell` | `def` |
| `arIndex` | `def` |
| `arPos` | `def` |
| `arCoords` | `lemma` |
| `arPos_coords` | `lemma` |
| `arPos_eq` | `lemma` |
| `arTape` | `def` |
| `arTape_at` | `lemma` |
| `arTape_ext` | `lemma` |
| `arTape_update` | `lemma` |
| `arCode` | `def` |
| `arDecode` | `def` |
| `arDecode_code` | `lemma` |
| `arBit` | `def` |
| `arBit_embed` | `lemma` |
| `ArPending` | `abbrev` |
| `ArState` | `abbrev` |
| `arReady` | `def` |
| `arPending` | `def` |
| `arTM` | `def` |
| `arCfg` | `def` |
| `arCfg_input` | `lemma` |
| `arBuffer` | `def` |
| `arBuffer_zero` | `lemma` |
| `arBuffer_full` | `lemma` |
| `arBuffer_update` | `lemma` |
| `arReadCfg` | `def` |
| `arReadCfg_zero` | `lemma` |
| `arReadCfg_symbols` | `lemma` |
| `arReadCfg_step` | `lemma` |
| `arReadCfg_run` | `lemma` |
| `arTail` | `def` |
| `arTail_full` | `lemma` |
| `arTail_zero` | `lemma` |
| `arTail_update` | `lemma` |
| `arUpdated_tape` | `lemma` |
| `arMoveCfg` | `def` |
| `arWriteCfg` | `def` |
| `arMoveCfg_step` | `lemma` |
| `arMoveCfg_finish` | `lemma` |
| `arMoveCfg_run` | `lemma` |
| `arWriteCfg_step` | `lemma` |
| `arWriteCfg_finish` | `lemma` |
| `arWriteCfg_run` | `lemma` |
| `arReadCfg_dispatch` | `lemma` |
| `arCfg_cycle` | `lemma` |
| `arCfg_run` | `lemma` |
| `arCfg_init` | `lemma` |
| `arEmission_in_image` | `lemma` |
| `arTM_computes` | `lemma` |

## Requested shared lemmas

Request promotion of `arUpdated_tape` to `Simulation.lean` (with a shared name).
It normalizes the raw model's optional-write convention: writing is equivalent
to updating the scanned cell with the proposed symbol, or with the existing read
when the action declines to write. The current implementation keeps this generic
lemma private in the owned alphabet-reduction file:

```lean
private lemma arUpdated_tape {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (a : Action k Γ S) (i : Fin k) :
    (a.apply c).workTapes i = Function.update (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i))
```

No shared-file changes are included or required to replay this delivery.

## Escalations

None. Both targets were proved as stated; no mathematical obstruction, added
hypothesis, weakened conclusion, or additional axiom was needed.

## Docstring appendices

Only an implementation note was appended to each target's existing docstring.
The folding note records canonical blank packing, one-step initialization,
lockstep simulation, universal input safety, and immediate initial invalid-input
halting. The alphabet note records the permitted one-hot width, the generic
blank-preserving codec interface, the exact cycle length, zero tapes, and the
formal output-prefix lemma. Original sketches and attributions are retained.
New private helpers have additional explanatory comments.

## Verification evidence

- `final-sweep.log` is the complete output of the required full 24-module sweep.
  Exit code: **0**. Every module was checked by `scripts/lean_check_tree.sh`, which
  removes its old `.olean`, checks the Lean exit status and diagnostics, and
  requires a newly produced `.olean`.
- Zero `error:` or `FAIL(...)` lines. Neither owned file produces any warning.
- The only additional warnings are three pre-existing linter warnings in the
  frozen `Configuration.lean`; they are not sorry warnings.
- The exact remaining sorry warnings are listed below. Their source files are
  byte-unchanged from the required base.

| File under `TCSlib/Complexity/TuringMachine/` | Remaining theorem |
|---|---|
| `Composition.lean` | `computesFunInTime_comp` |
| `Composition.lean` | `exists_comp_partial` |
| `Robustness/SingleTape.lean` | `one_work_tape` |
| `Robustness/Oblivious.lean` | `oblivious_of_mem_DTIME` |
| `Encoding.lean` | `exists_effectiveMachineCode` |
| `Universal.lean` | `universal` |
| `Universal.lean` | `timed_universal` |

`axioms.log` was generated by the scratch `CheckAxioms.lean` outside the repository,
using the check script's `.olean` tree and dependency `LEAN_PATH`:

| Theorem | Axioms |
|---|---|
| `Turing.FinTM.nonnegative_heads` | `[propext, Classical.choice, Quot.sound]` |
| `Turing.FinTM.alphabet_reduction` | `[propext, Classical.choice, Quot.sound]` |
| `Turing.FinTM.one_work_tape_binary` | `[propext, sorryAx, Classical.choice, Quot.sound]` |

The regression corollary still depends on the untouched `one_work_tape` sorry.
Neither newly filled theorem does. No `sorry`, `admit`, added `axiom`, `unsafe`,
or `native_decide` occurs in the delivered owned files.

`verification/freeze-check.json` and `verification/verify_freeze.py` record and
reproduce byte comparison of both target statements, the `NonnegativeHeads`
definition, preservation of the old sketches and option headers, privacy of every
new authored declaration, and the exact two-file diff scope. `git diff --check`
passes. `verification/results.json` records the pinned toolchain/dependency and
verification outcomes. The Git bundle and format-patch are also validated for
transport in the accompanying delivery log.

### Environment

Lean is **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
Mathlib is the manifest's exact commit
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
No `lake build` command was run, and neither pin nor the manifest was modified.

The preinstalled Lean executable initially failed to locate its application path
because this container's numeric process path did not resolve consistently with
its process namespace. The included `lean_proc_compat.c` redirects only the
current process's `/proc/<its-pid>/exe` lookup to `/proc/self/exe`. It does not
modify Lean's executable, elaborator, kernel, source, or proof checking. All
verification used the stock pinned executable with this compatibility wrapper.
The original full cache invocation failed; the cache executable's targeted retry
restored the required closure of 878 dependencies successfully. The targeted-cache
and initial bootstrap logs are included. These accommodations affected local
setup only; none changes repository code or the verification script.

## Delivery and replay

The root contains `REPORT.md`, the complete modified source files at their
repository paths, `epoch2-C.patch`, `epoch2-C.bundle`, `final-sweep.log`,
`axioms.log`, and `SHA256SUMS`, plus verification evidence.
`SHA256SUMS` hashes every other file in the archive; the checksum manifest itself
is omitted from its own contents under the standard non-self-referential
checksum convention.

In a clone containing the base commit, use either the patch or the bundle:

```bash
git switch -c review/epoch2-C 24687122
git am /absolute/path/to/epoch2-C.patch
```

Alternatively:

```bash
git fetch /absolute/path/to/epoch2-C.bundle fill/epoch2-C:review/epoch2-C
git switch review/epoch2-C
```

After dependency setup, use the prescribed sweep:

```bash
( while read -r m; do
    bash scripts/lean_check_tree.sh "$m" || exit 1
  done < scripts/ab_ch1_module_order.txt )
```

A normal installation needs no process compatibility wrapper. If reproducing in
the same affected container, compile the included C wrapper with
`cc -shared -fPIC lean_proc_compat.c -o lean_proc_compat.so -ldl` and set
`LD_PRELOAD` to its absolute path before the prescribed commands.

### Local commits

```
73122d5afaaa6fc71481586da45fe7f2f3999e6d Prove nonnegative work-head simulation by tagged tape folding
c8a517f6f90e18687a2c0a1e374a91d01e9b52df Prove alphabet reduction with blank-preserving block simulation
63d346933273c527e6a2d81af9bbfeafc92fbd7e Halt immediately on invalid initial folding input
```

## Notation glossary

`Γ`: source nonblank alphabet; `γ`, `a`: source symbols or the explicitly typed
source action; `Bool`: binary nonblank alphabet; `Option`: addition of a blank
value; `e`: input/output symbol embedding; `E`: injective work-block code;
`N`: code-width parameter; `L = N + 1`: positive block width; `k`: number of work
tapes; `M`: source machine; `M'`: simulator; `f`: computed string function;
`T`: original time bound; `n`: input length; `x`: input string; `t`: time;
`z`: virtual integer tape coordinate; `p`: physical or explicitly named scanned
coordinate; `φ`: folding map; `c`: multiplicative slowdown constant, or the
explicitly typed configuration in Lean snippets; `i`: work-tape index;
`j`: within-block index; `w`: completed output or explicitly typed replacement
symbol. All machine constants are fixed independently of the input.

---

# ATTACHMENT B — Context documents

## ===== AroraBarakChapter1Plan.md =====

# Formalization Plan: Arora-Barak Chapter 1

**Branch:** `complexity/arora-barak-ch1` · **Governing standards:** [`policy.md`](policy.md)

This document is the working plan for formalizing Chapter 1 of Arora & Barak,
*Computational Complexity: A Modern Approach* (CUP 2009) — "The computational model — and
why it doesn't matter" (book pages 9–37) — in TCSlib. It records the foundation decision,
the architecture that keeps the model robust to variations (oracles, nondeterminism), the
module layout, and the phasing. Source tag throughout the development: `[AB09]`.

## 1. Scope: what Chapter 1 contains

| Section | Content | In scope |
|---|---|---|
| §1.2 | k-tape TM `(Γ, Q, δ)`: read-only input tape, work tapes, output tape (read-write in [AB09]; append-only write-only in our model — a variation [AB09, p. 19] itself sanctions, declared in `DTIME.lean`); start configuration; halting; Example 1.1 (palindromes in 3n steps) | Yes |
| §1.3 | Computing `f` in time `T(n)` (Def 1.3); time-constructibility; Claim 1.5 (alphabet reduction, `4 log|Γ|` slowdown); Claim 1.6 (k tapes → 1 tape, `5kT²`); Remark 1.7 (oblivious TMs); Claim 1.8 (bidirectional → unidirectional, `4T`) | Yes (oblivious: statement only at first) |
| §1.4 | Machines as strings: every string decodes to some TM, every TM has infinitely many encodings; universal TM; Theorem 1.9 (universal simulation), relaxed `O(T²)` version; time-bounded universal TM | Yes |
| §1.5 | Uncomputability: `UC` via diagonalization (Thm 1.10); `HALT` via reduction (Thm 1.11); §1.5.2 Gödel discussion | Thms 1.10–1.11 yes; Gödel material is prose — out of scope |
| §1.6 | `DTIME(T(n))` (Def 1.12, with constant absorption), `P` (Def 1.13), examples | Yes |
| §1.7 | Hennie-Stearns `O(T log T)` universal simulation (amortized zone argument) | Stretch goal, off the critical path |

Additionally in scope, ahead of the book's own ordering: the **oracle TM** definition
(the book defers it to §3.4). We pull it forward to validate that the architecture supports
model variations before the expensive theorems are built on it.

## 2. Foundation decision

**Decision: vendor cslib's multi-tape TM model; do not build on Mathlib's TMs; do not take
cslib as a dependency.** Findings behind this (surveyed Sept 2026, against our pinned
mathlib `029db123ddaa`, toolchain v4.25.0):

- **Mathlib** is a computability library, not a complexity library. It has no multi-tape TM
  (TM0/TM1 are single-tape, TM2 is a stack machine); its model-simulation theorems carry no
  time bounds; `TM2ComputableInPolyTime` is a stub whose only instance is `id`. Building
  Arora-Barak on it means fighting the design. What we do reuse: `Language`,
  `Turing.FinEncoding`, and (later, as an optional bridge) the recursion-theory stack
  (`Nat.Partrec`, `Halting`/Rice, `Reduce`, `RecursiveIn`).
- **cslib** (github.com/leanprover/cslib, `Cslib/Computability/Machines/Turing/MultiTape/`,
  Apache-2.0) has an Arora-Barak-style `MultiTapeTM` (its write-only output tape is an
  [AB09, p. 19]-sanctioned variation of the book's read-write one): read-only input
  tape, k work tapes, explicit time and space semantics, a nondeterministic
  variant, and configuration-count bounds — actively developed, with a complexity roadmap
  (issue #611) that plans oracles as a wrapper over any model.
- **Why vendor rather than depend:** cslib targets Lean v4.35.0-rc1 with the new module
  system; TCSlib is pinned to v4.25.0 and the PFR dependency chains us there. The vendored
  surface is small (~1,400 lines). We stay structurally aligned with upstream so we can
  migrate to a real dependency at the next toolchain bump, and upstream anything we prove
  that they lack (universal TM, robustness claims).
- Vendored files follow `policy.md` §2: original copyright headers preserved, source commit
  recorded, local modifications listed (expected: de-module-system syntax, import-path
  ports to v4.25 mathlib).

Reference mechanization to mine for proof architecture: the Isabelle AFP entry
`Cook_Levin` (Balbach) — the only completed Arora-Barak-faithful development. Its lemma
decomposition, especially for TM composition and the universal machine, transfers.

## 3. Architecture

### 3.1 The Action/apply split (model variations)

cslib's configuration layer mentions no machine: a step is an **`Action`** (input-head
move, per-work-tape write/move, optional output symbol, successor state) plus
**`Action.apply`** (its effect on a configuration). A *machine* is then just the thing
that **chooses** the action from the current state and read symbols. Every model twist is a
different chooser over the same configurations, the same `apply`, and the same run/time/
space measures:

| Model | Chooser |
|---|---|
| Deterministic TM (Ch. 1) | function `State × reads → Action` |
| Nondeterministic TM (Ch. 2) | relation over actions |
| Oracle TM (§3.4, Definition 3.4, pulled forward) | function consulting `O : Language _` via query tape and `q_query`/`q_yes`/`q_no` states (pairwise distinct: `OracleTM.WellFormed`) |
| Probabilistic TM (Ch. 7, future) | two transition functions + coin |

Because `DTIME`-style definitions are stated over the shared run layer, `P`, `Pᴼ`, and
later `NP`/`BPP` are instances of one pattern, not parallel developments. Phase 1 locks
the design with sanity theorems in both directions: a plain machine embeds as an oracle
machine whose runs are in lockstep with the original under *every* oracle
(`ofMultiTapeTM`), and conversely an oracle machine run with the empty oracle is
eliminated into a plain machine in exact lockstep (`plainEmptyOracle`).

### 3.2 Finiteness: raw layer vs. bundled layer

Finiteness of `Γ` and `Q` is mathematically non-negotiable: with infinite states, δ can
memorize the input and decide any language in linear time (P would collapse to all
languages), and `⌞M⌟` has no finite representation. The design question is only *where*
the hypothesis lives:

- **Raw layer** (`MultiTapeTM k Γ Q`, parametric types, no finiteness): configurations,
  `step`, runs, time/space counting, and simulation *constructions*. Deferring finiteness
  here keeps semantics lemmas clean and lets compound state types (`Q × Γᵏ`, `Option Q`,
  sums) arise without instance-threading; finiteness of a constructed machine is an
  afterthought (`inferInstance`). This follows both cslib and mathlib TM0/TM1 practice.
- **Bundled layer** (`FinTM Symbol`: a raw machine bundled with `Fintype`/`DecidableEq`
  instances for its *state* type — analogous to mathlib's `FinTM2`): **all headline
  definitions and theorems** — `DTIME`, `P`, `⌞M⌟`, Theorem 1.9, oracle classes — are
  stated exclusively over the bundled layer, so a finiteness hypothesis can never be
  forgotten. The alphabet is *not* bundled: it stays an explicit parameter, fixed to
  `Bool` by the headline classes; results over a general `Symbol` (e.g. machine
  encodings) take `[Fintype Symbol]`/`[DecidableEq Symbol]` at their statements, and
  oracle complexity classes (Ch. 3) will introduce a finite oracle-machine bundle
  before they are defined. Encoding needs `Fintype`/`DecidableEq` as *data* (δ's table
  must be enumerated), which is why the bundle carries instances rather than `Finite`
  propositions.

Per `policy.md` §1 (layering), the raw layer is internal plumbing; the bundled layer is
the textbook object.

### 3.3 Conventions

- **Strings/languages:** `{0,1}*` as in the book; languages via mathlib's `Language`.
- **Namespaces:** `Turing` for the vendored core (minimizes diff against upstream; no
  clashes with mathlib's `Turing.*` at our pin), `Complexity` for classes and
  uncomputability. Revisit only if a clash appears.
- **NP/NTM:** strictly Chapter 1 here. cslib's nondeterministic file is in the vendorable
  set but lands with the Chapter 2 effort.

## 4. Module layout

Per `policy.md` §1: facades, 150–600-line files, precise imports, `TCSlib.lean` exports.

```
TCSlib/Complexity/TuringMachine.lean          -- facade + module docstring
TCSlib/Complexity/TuringMachine/
  Configuration.lean      -- Cfg, Action, Action.apply, space measure   [vendored]
  Deterministic.lean      -- MultiTapeTM, run, ComputesInTime(AndSpace) [vendored]
  Finite.lean             -- bundled FinTM layer (§3.2)
  Oracle.lean             -- oracle wrapper over the same Cfg/Action layer
  Composition.lean        -- sequential composition, basic combinators
  Robustness/
    AlphabetReduction.lean  -- [AB09, Claim 1.5]
    SingleTape.lean         -- [AB09, Claim 1.6]
    Bidirectional.lean      -- [AB09, Claim 1.8]
    Oblivious.lean          -- [AB09, Remark 1.7] (statement; proof deferred)
  Encoding.lean           -- ⌞M⌟ : TM ↔ string; totality + padding [AB09, §1.4]
  Universal.lean          -- [AB09, Thm 1.9] relaxed O(T²) + timed variant
  UniversalEfficient.lean -- [AB09, §1.7] Hennie-Stearns O(T log T)  [stretch]
TCSlib/Complexity/Uncomputability.lean        -- facade
TCSlib/Complexity/Uncomputability/
  Computable.lean         -- computable functions, no time bound [AB09, §1.4-§1.5]
  Diagonalization.lean    -- UC, [AB09, Thm 1.10]
  Halting.lean            -- HALT, [AB09, Thm 1.11]
  MathlibBridge.lean      -- link to Nat.Partrec / Rice  [optional, later]
TCSlib/Complexity/ClassP.lean                 -- facade
TCSlib/Complexity/ClassP/
  DTIME.lean              -- decides, DTIME with constant absorption [AB09, Def 1.12]
  TimeConstructible.lean  -- time-constructibility [AB09, §1.3]
  P.lean                  -- P, closure basics, model-invariance [AB09, Def 1.13]
  Examples.lean           -- PAL ∈ DTIME(n+1) [AB09, Ex 1.1]; selected Ex 1.14
```

## 5. Phasing

Each phase lands first as a **compiling sorry-skeleton** (the GraphTheory/Core precedent):
statements are the contract, proofs fill in via the sorry-ladder workflow. Per `policy.md`
§3, proof sketches are written at skeleton time — each `sorry` corresponds to a named
sketch step. After each phase compiles: dep-graph rebuild, `/blueprint-extract`,
`blueprint_validate.py --strict`, `dataset_hygiene.py --strict`. The blueprint is
**late-bound**: extraction runs only at phase boundaries, and no blueprint LaTeX is
written by hand ahead of the Lean.

### Audit protocol (between phases)

Right after a phase's skeleton lands — statements frozen, proofs mostly `sorry` — an
**external audit** runs before the next phase begins: an LLM from a different vendor, in
a fresh context, reviews the phase's trusted surface (definitions, theorem statements,
remaining sorries) against the book, adversarially. Statement bugs are the dominant
failure mode of formalization (Lean already checks proofs) and are cheapest to fix at
this moment. Mechanics: instantiate `audits/TEMPLATE.md` as `audits/phaseN-pack.md`, hand
it plus the listed files to the auditor, record results in `audits/phaseN-findings.md`;
every finding is fixed or explicitly waived before the next phase starts. An optional
light second pass when a phase's proofs complete diffs the statements for quiet
weakening. Audits complement, not replace, in-Lean sanity theorems, which are the
machine-checked and permanent form of the same checks.

1. **Core model + classes.** Port the two vendored files to v4.25; `Finite.lean`;
   `ComputesInTime`, `decides`, `DTIME`, `P`; the oracle wrapper + trivial-oracle sanity
   theorem; PAL as an end-to-end usability check. *This phase alone unblocks future
   chapters (NP needs only these definitions).*
2. **Robustness.** Claims 1.5, 1.6, 1.8; `Composition.lean` combinators; corollary that P
   is invariant under the model tweaks. First real machine-construction proofs — builds
   the simulation vocabulary everything later reuses. The convention obligations
   recorded by the phase-1 audit are dispositioned per the phase-2 audit (findings 3
   and 13): the append-only-output and initialization bridges are **waived** (no
   read-write-output model is formalized; no exact step count is ever imported from
   [AB09]), to be revisited only if a downstream result needs a formal bridge; the
   persistent vs auto-erased query-tape statement (polynomial overhead only — constant
   overhead provably impossible) moves to the Chapter 3 oracle-class work.
3. **Encodings + universal machine.** `⌞M⌟` with totality and padding lemmas; Theorem 1.9
   in the relaxed `O(T²)` form (U simulates the one-work-tape *binary* normal form from
   phase 2 — `FinTM Bool`, i.e. three tape symbols counting blank; if the construction
   wants [AB09]'s four-symbol alphabet, that is an additional named embedding step) and
   the time-bounded variant.
4. **Uncomputability.** Thm 1.10 (needs only encoding + semantics; the diagonalization is
   short); Thm 1.11 (needs composition + the universal machine). Proof blueprints for
   both are in `audits/phase3-reaudit-findings.md`, Argument F. Scope additionally
   includes the API pieces that audit identified: a **guarded/partial composition (or
   guarded-simulation) lemma** with buffered intermediate output — the total-function
   `computesFunInTime_comp` cannot take the partial evaluator as a component — and,
   where a proof needs a globally chosen evaluator or a semantically identified code,
   an explicitly stated named-evaluator interface.
5. **Stretch — explicitly off the critical path, and deferred to a much later
   effort.** §1.7's `O(T log T)` simulation; oblivious TMs; the RAM-TM exercise
   (Ex 1.9); the mathlib recursion-theory bridge. **Not scheduled** (decision of
   2026-09-16): phase 5 is a task for much later — it is not part of the current
   push, no audit pack will be prepared for it, and it is revisited only after the
   phase-1-4 fill campaign completes. Chapter 1's critical path *ends with phase 4*.

### Fill campaign (epochs and batches)

With all four phase gates closed, the remaining critical-path work is filling the
21 audited-true sorries. The campaign runs in **epochs** — sequential, with an
audit round at each epoch boundary — each consisting of **batches** run in
parallel, one agent per batch, with disjoint file ownership. Difficulty points
(1-15 scale) are planning estimates. Agents work in the cloud from the
self-contained briefs in `briefs/`, branching off `complexity/arora-barak-ch1`
and PRing back into it (`github.com/Shilun-Allan-Li/tcslib`). Verification is
`scripts/lean_check_tree.sh` over `scripts/ab_ch1_module_order.txt` (direct
`lean`; `lake build` stays banned).

| Epoch | Batch | Contents (points) | Owned files |
|---|---|---|---|
| **1** | 1A | `Computes.exists_computesFunInTime` (2), `UC_not_computable` (2), `universal_quadratic` (2), `UC_computable_of_HALT_computable` (3) — the assembly/integration tests | `Uncomputability/{Computable,Diagonalization,Halting}.lean`, `Universal.lean` (quadratic only) |
| 1 | 1B | `computesFunInTime_const` (2), `computesFunInTime_ifEq` (3), `exists_cond` (6) | `Composition.lean` |
| 1 | 1C | `pairEncode_injective` (3), `computesFunInTime_pairEncode_diag` (4), `exists_codeTM` (5) | `Encoding.lean` |
| 1 | 1D | `PAL_mem_DTIME_linear` (4), `timeConstructible_id` (5) | `Examples.lean`, `TimeConstructible.lean` |
| **2** | 2A | `exists_comp_partial` (8) then `computesFunInTime_comp` (7) — shared infrastructure, sequential within the batch | `Composition.lean`, `Simulation.lean` |
| 2 | 2B | `one_work_tape` (12) | `Robustness/SingleTape.lean` |
| 2 | 2C | `nonnegative_heads` (7), `alphabet_reduction` (8) | `Robustness/{Bidirectional,AlphabetReduction}.lean` |
| **3** | 3A | `exists_effectiveMachineCode` (13) | `Encoding.lean` |
| 3 | 3B | `universal` (15) | `Universal.lean` |
| 3 | 3C | `oblivious_of_mem_DTIME` (12) — droppable per the phase-5 deferral without reopening any gate | `Robustness/Oblivious.lean` |
| **4** | 4A | `timed_universal` (10), reusing `universal`'s infrastructure | `Universal.lean` |
| 4 | — | Closure: zero-sorry sweep with build evidence (phase-4 finding 8), final drift attestation across all gates, fill-round audit pack, `/blueprint-extract` | — |

Epoch loads: ≈ 41 / 42 / 40 / 10 points. Rationale: epoch 1 maximizes
risk-retirement per point (the assemblies machine-check that the phase-3/4
interfaces compose; the machine batches validate the invariant pattern at small
scale), epoch 2 retires the two biggest technique risks (guarded composition
with buffered output; sweep-based simulation), epoch 3 climbs the summit with
every needed technique already precedented in-repo, epoch 4 is wind-down.

**Ground rules** (binding on every batch; full text in each brief): (1)
exclusive file ownership — helpers live `private` in owned files; lemmas
belonging in shared files are *requested* via the PR description and added
serially at epoch merge, flagged for audit; (2) statement freeze — audited
declarations are never renamed, re-signatured, or re-stated by a fill PR; a
target that looks unprovable as stated is an *escalation*, reported in the PR
with the obstruction, never "fixed" inline; (3) verification per batch via the
check script, zero `error:` lines, sorry warnings only at documented
out-of-scope items; (4) at epoch merge the maintainer re-runs the full sweep,
produces the comment-stripped drift attestation, and prepares the epoch's
fill-round audit pack with elaboration evidence.

**Blueprint reference ingestion:** ingest Chapter 1 as
`blueprint/src/references/arora-barak-ch01-*.md` (raw/clean pair, ch. 13 shows the format)
so `\statementsource`/`\proofsource` citations are possible once proofmatch runs are
approved.

## 6. Risks and honest effort assessment

- **The proof-sketch gap is the main cost.** The book proves Claims 1.5/1.6 and Thm 1.9 in
  a paragraph each; formally these are the expensive items. The AFP `Cook_Levin` entry
  spent most of its effort exactly here. `Composition.lean` is the hidden load-bearing
  file — budget for it.
- **Vendoring means drift** against a fast-moving upstream. Mitigation: minimal local
  modification, source commit recorded per file, periodic upstream diffs.
- **Definitions before theorems pays off:** phases 1–2 already give TCSlib a citable,
  blueprint-documented model of computation with P and oracles, onto which the existing
  `Complexity/NPReductions/` files can eventually be retargeted — even if phases 3–5 fill
  slowly.

## 7. Decision log

| Decision | Status |
|---|---|
| Vendor cslib `MultiTapeTM`; reuse mathlib only for `Language`/`FinEncoding`/bridge | Decided |
| Finiteness deferred in raw layer, enforced via bundled `FinTM` for all headline defs | Decided |
| Oracle wrapper lands in phase 1 (ahead of book order) | Decided |
| Work on branch `complexity/arora-barak-ch1`; verify via `scripts/lean_check.sh` (CI runs on main only) | Decided |
| Namespaces: `Turing` (vendored core) / `Complexity` (classes) | Working assumption; revisit on clash |
| NP/NTM signatures deferred to Chapter 2 work | Decided |
| §1.7 `O(T log T)` and oblivious-TM proofs are stretch goals | Decided |
| Blueprint: late-bound — generated from compiled Lean at phase boundaries only, nothing hand-written ahead of the Lean | Decided |
| External audits between phases: cross-vendor LLM with prepared packs (`audits/`), findings gate the next phase | Decided |
| Vendored cslib source commit: `a374775894efb9b7196cccf11235c60a97086dc1` (2026-09-14); relational semantics (`RelatesInSteps`) dropped in the port | Decided |
| Phase-1 audit round 1 (`audits/phase1-findings.md`): all 8 sorries confirmed true; 3 majors fixed — `TimeConstructible` repaired to `∃ c > 0, … c·(T n + 1)` (the literal exact bound refutes AB's own `id` example in this model), `OracleTM.WellFormed` added, oracle-tape constant-overhead claim corrected to polynomial; minors swept; audit-requested sanity statements added. Oracle citation is [AB09, Definition 3.4] (not 3.6) | Decided |
| Phase 1 requires a clean re-audit of the fixes before phase 2 starts | Decided |
| Phase-1 audit round 2 (`audits/phase1-reaudit-findings.md`): zero blockers/majors — all round-1 resolutions verified, all 8 new sorries confirmed true (with a worked `timeConstructible_id` witness machine reusable in the fill phase); 5 prose minors swept, blankness-certificate lemma added per note 6. **Phase-1 audit gate closed**; see `audits/phase1-resolutions.md` | Decided |
| Phase-2 renderings: Claim 1.6 rendered as **one work tape** (the merged input/work/output single-tape model is a genuinely different structure — it has an `Ω(n²)` palindrome lower bound our model beats — and is out of scope, with no identification claimed); Claim 1.8 rendered as **`NonnegativeHeads`** (our tapes are already bidirectional, so the meaningful direction is unidirectional use); obliviousness constrains input/work-head trajectories only — it does **not** force length-determined halting (phase-2 audit finding 1 refuted that with a stationary-head counterexample) and leaves emission schedules unconstrained; the `TimeConstructible` hypothesis in Exercise 1.5 is needed by the padding construction, not by the definition | Decided — audited (phase-2 round 1) |
| Output-tape/initialization convention obligations (phase-1 finding 4): **waived**, per phase-2 audit finding 3 — no formal bridge is possible without formalizing [AB09]'s read-write-output model, which this development does not do; the compensating restriction is that no exact-step-count transfer from [AB09] is ever claimed (all bounds carry existential constants, all results are self-contained in-model). The buffer-and-flush technique is documented in `Composition.lean`; a formal bridge is added only if a downstream result needs it | Decided — waiver accepted by phase-2 audit as a labeled option |
| Persistent-vs-erased query-tape polynomial-overhead statement moved from phase 2 to the Chapter 3 oracle-class work, where polynomial overhead is meaningful (class level); the impossibility of constant overhead stays documented in `Oracle.lean`. Outstanding obligation before importing any oracle-class invariance | Decided — deferral accepted by phase-2 audit (finding 13) |
| Phase-2 audit round 1 (`audits/phase2-findings.md`): 4 majors, 6 minors, 3 notes — **no theorem formula refuted**; all 11 new sorries assessed true as stated. Majors were prose/sketch-level: the false frozen-heads implication removed, the oblivious-simulation sketch replaced by the audit's corrected construction, the convention-discharge overclaim converted to the waiver above, ModelInvariance's invariance claims stated at delivered strength (alphabet: DTIME up to constants; tape count: P only). Sketch repairs: all-blank block for logical blank (1.5), tagged `Option Γ` payloads and `k = 0` case (1.6), piecewise fold coordinate with origin tags and safe-halt on non-embedded symbols (1.8) | Decided |
| Phase-3 audit round 2 (`audits/phase3-reaudit-findings.md`): zero blockers/majors — both round-1 counterexamples formally excluded (`serialize` proved injective and prefix-free from its parse grammar; the canonizer contract shown to decide the undecidable set for Argument A's scheme, so it cannot instantiate `EffectiveMachineCode`; code-first startup arithmetic verified with no input-length term). The α-dependent evaluator constant confirmed **necessary** (Argument E) — never to be described as [AB09]'s machine-dependent constant. Two minors swept (left-boundary marker in the evaluator sketch; `Nat.bits` order wording). Argument F provides complete phase-4 proof blueprints and identifies the guarded-composition API obligation. **Phase-3 audit gate closed**; see `audits/phase3-resolutions.md` | Decided |
| Phase-3 audit round 1 (`audits/phase3-findings.md`): **two blockers on the phase-3 statements, both accepted** — (1) the algebraic `MachineCode` admits noncomputable-meaning schemes against which no universal machine exists (Argument A), repaired by `EffectiveMachineCode`: an in-model canonizer into the new **fixed scheme-independent** `CodeTM.serialize` (canonizing into the scheme's own encode provably does not exclude the pathology); (2) the input-first `pairEncode x α` layout falsifies all three time bounds (Argument B), repaired by the **code-first** layout `pairEncode α x`. Majors: `universal` restated as the all-string evaluator `U(x, α) = M_α(x)` with a divergence-preservation converse and α-dependent constants; `universal_quadratic` labeled as the total-function corollary; `serialize` records the initial state (finding 5's collision). Minors: deadline-inclusive timeout convention documented; pack namespace erratum (`Complexity.succ_pow_le`). Fill round and supporting lemmas: audited clean (findings 9-13). Re-audit pending | Decided |
| Fill round 1 (commit `f8621285`): 20 of 28 phase-1/2 sorries proved — all semantics/arithmetic/chaining obligations, both oracle lockstep theorems, `mem_P_iff`, and `computesFunInTime_id` with an explicit machine. The 8 remaining sorries are exactly the heavy machine constructions (`const`, `comp`, the four robustness simulations, `timeConstructible_id`, `PAL_mem_DTIME_linear`), each with an audited outline. Repository-side verification: no audited declaration signature changed or was removed. Phase-3 skeleton delivered (5 statement sorries): `CodeTM`, abstract `MachineCode` scheme, `pairEncode`, Theorem 1.9 (linear for coded machines / relaxed quadratic / timed). Audit round covering fills + phase-3 pending | Decided |
| Phase-2 audit round 2 (`audits/phase2-reaudit-findings.md`): zero blockers/majors — both corrected load-bearing sketches certified as adequate proof outlines; 4 prose minors swept (fold alphabet `Bool × Option Γ × Option Γ`, waiver-prose synchronization, `O((k+1)·L)` overhead, one-work-tape *binary* normal form in phase 3); Lean-code identity between the audited commits verified repository-side by comment-stripped git comparison. **Phase-2 audit gate closed**; see `audits/phase2-resolutions.md` | Decided |
| Phase-4 skeleton landed (after the closed phase-3 loop, gate commit `b61e876d`): `Uncomputability/{Computable,Diagonalization,Halting}.lean` + facade — `Complexity.Computable`, `UC` (over an **arbitrary** `MachineCode`: the diagonalization never computes `encode`/`decode`, per round-2 Argument F; effectivity appears only in Theorem 1.11), `HALT` (totalized `false` off the `pairEncode` image; pair format = the evaluator's code-first layout), `UC_not_computable`, the reduction `UC_computable_of_HALT_computable` (uses only the *forward* clause of `universal`), `HALT_not_computable` (proved from the two). The audit-mandated guarded API landed in `Composition.lean` (`exists_comp_partial` — partial sequential composition with buffered intermediate output; `exists_cond` — branch on a decided predicate; `computesFunInTime_ifEq`), plus `computesFunInTime_pairEncode_diag` in `Encoding.lean` and `FinTM.Computes`/`ComputesInTime.output_unique`/`ComputesFunInTime.computes` in `Finite.lean` (additions to audited files, flagged for the phase-4 audit). 7 new sorries (21 total), every phase-4 proof sketch names only stated results. Phase-4 audit pack pending | Decided |
| Phase-4 audit round 1 (`audits/phase4-findings.md`, audited at `49d25a27`): **zero blockers, zero majors — the first single-round gate**. All 18 new declarations blind-restated in agreement; both headline arguments (UC diagonalization over an arbitrary `MachineCode`; `HALT → UC` reduction using only the forward evaluator clause) independently re-derived end-to-end from stated interfaces — no missing machine-construction API. One minor swept (the diagonal-pairing sketch's step count corrected to the auditor's `4n + 5 ≤ 6(n+1)` schedule; statement unchanged); note-level sketch refinements (unconditional first rewind move + empty-buffer boundary tag in `exists_comp_partial`; `HALT` off-image convention warning for downstream clients). **Phase-4 audit gate closed** — Chapter 1's critical path is fully specified and audited; see `audits/phase4-resolutions.md`. Remaining critical-path work: the 21-sorry fill campaign | Decided |
| Phase 5 (§1.7 `O(T log T)`, oblivious proofs, RAM-TM, mathlib bridge) **deferred to a much later effort** — not scheduled in the current push; revisit only after the phase-1-4 fill campaign completes | Decided |
| Fill campaign schedule (2026-09-16, §5 "Fill campaign"): 4 epochs of parallel disjoint-ownership batches (E1 ≈ 41 pts: assemblies + small machines + encoding list layer + classic machines; E2 ≈ 42: guarded-composition core + `one_work_tape` + remaining simulations; E3 ≈ 40: canonizer + `universal` + oblivious (droppable); E4 ≈ 10: `timed_universal` + closure), audit rounds at epoch boundaries. Cloud agents work from `briefs/epoch1-batch{A,B,C,D}.md`, branch off `complexity/arora-barak-ch1`, PR back into it; verification via `scripts/lean_check_tree.sh` + `scripts/ab_ch1_module_order.txt` | Decided |
| Epoch-1 fill round audited and closed (`audits/epoch1-findings.md` → `audits/epoch1-resolutions.md`): **zero statement-level blockers/majors** — freeze, all 22 elaborations, and all 13 axiom footprints independently reproduced; all four delivered machines certified against their audited schedules. One major was a pre-existing **tooling** defect: `scripts/lean_check_tree.sh` discarded Lean's exit status (false success on a diagnostics-free crash) — fixed (status propagation + fresh-olean requirement + failing sweep recipe), exploit reproduced against old and new gates, full sweep re-run under the strengthened gate. Auditor-endorsed epoch-2 merge pre-work: promote `Computes.exists_computesInTime_iff` (A) and a `Symbol`-generalized `computesInTime_iff` (B) into `Finite.lean`; create `TuringMachine/StateRenaming.lean` reusing `Turing.Action.mapState` (from Oracle.lean) at the raw layer; split the ~950-line `Composition.lean` (also resolves the finding-11 source-order obligation — epoch-1 gadgets sit *after* the remaining composition sorries, and they are not yet a buffered-composition simulator: 2A owes buffer/virtual-input invariants and explicit time bounds) | Decided |
| Epoch-2 merge refactor executed (commit `24687122`), per the epoch-1 resolutions: new `TuringMachine/StateRenaming.lean` (public `Action.mapState` moved verbatim from `Oracle.lean`; `Cfg.mapState` + application lemma; `MultiTapeTM.relabelState` + step commutation + `relabelState_runFrom_init`), new `TuringMachine/Simulation.lean` (the epoch-1 gadget layer made public and moved out of `Composition.lean`, with the finding-11 scope note that the embeddings are not yet a buffered simulator), the two `Finite.lean` promotions (`computesInTime_iff` generalized to any alphabet; `Computes.exists_computesInTime_iff`), and rewired `Encoding.lean`/`Halting.lean`/`Oracle.lean`. Declaration check: no public name lost (7 privates retired, 6 publics added); 24-module sweep clean under the strengthened gate, same 9 sorries. Epoch-2 briefs in `briefs/epoch2-batch{A,B,C}.md`, base `24687122`; **delivery is a zip archive** (runners have no GitHub write access — no PR step), standardized contents per epoch-1 findings 1 and 13: report, full sources, format-patch, git bundle, complete sweep log, per-theorem `#print axioms` log, SHA256 manifest | Decided |
| Fate of this file at merge (graduate to `docs/` vs. superseded by blueprint) | Open — decide at merge time |

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

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

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

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

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

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
5. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
6. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.

## ===== audits/epoch1-findings.md =====

Independent adversarial audit — Arora–Barak Chapter 1, epoch-1 fill round

Audited commit: [`d3393b35764710ff3d7ae538d5133284291d9ef4`](https://github.com/Shilun-Allan-Li/tcslib/commit/d3393b35764710ff3d7ae538d5133284291d9ef4), compared with `9f735248212c1d1d842b299b431b2b680220ac5b`, on `complexity/arora-barak-ch1`. Inputs: the uploaded `epoch1-bundle.md` and Arora–Barak (2009), §§1.2–1.5.1, PDF pp. 35–49. The pinned repository supplied the baseline sources, the three facade modules, the verification script and module order, and the referenced phase-1 and phase-4 findings. One auditor; no delegation. No repository write was performed.

I found one **major verification-tooling defect**, in a pre-existing script used by the campaign, and one **minor packet-scope defect**. Independent checks reproduce the statement freeze, successful elaboration of all 22 modules, and all 13 reported axiom footprints. The tooling defect did not invalidate this independently checked elaboration. The remaining construction obligations and the limits of the proposed helper reuse are dispositioned individually below.

The following eight restatements were recorded from comment-stripped signatures and defining equations before reading their surrounding implementation prose. The subsequent comparison found no disagreement with their docstrings.

| File · promotion candidate | Blind restatement |
|---|---|
| `Halting.lean · halts_iff_eq_of_computes` | For any alphabet and fixed machine computing the total string function `g`, `(∃ t, M.ComputesInTime x w t) ↔ w = g x`. This characterizes completed outputs. It requires neither a finite alphabet nor a uniform time bound. |
| `Composition.lean · computesInTime_iff` | For a Boolean machine and specified input, output, and time, `M.ComputesInTime x w t` is equivalent to the initialized run being halted and having output exactly `w` at time `t`. No totality or minimal-halting-time claim is made. |
| `Encoding.lean · codeMapAction` | Any function between state types maps the action's optional successor state; input movement, work writes and movements, and emission are unchanged. `none` stays `none`. Injectivity is unnecessary. |
| `Encoding.lean · codeMapCfg` | Any function between state types maps the configuration's optional state and preserves every other field: input position, work tapes, work-head positions, and output. |
| `Encoding.lean · codeMapCfg_apply` | Applying a mapped action to a mapped configuration equals mapping the result of the original application. This holds even for a noninjective state function. |
| `Encoding.lean · codeRelabelTM` | A state equivalence maps the initial state forward. Each transition maps the current state backward, performs the original transition, then maps its optional successor forward. Alphabet and tape count are unchanged. |
| `Encoding.lean · codeRelabel_step` | From any mapped configuration, one relabeled-machine step equals the mapped original-machine step, including the halted case. |
| `Encoding.lean · codeRelabel_run` | For every input and natural time, the initialized relabeled run equals the mapped initialized original run at that same time. The stated theorem concerns initialized runs; it does not quantify over arbitrary starting configurations. |

For the first characterization, choose a completed computation of `g x` from `hM x`. A completed computation of `w` has the same output by `ComputesInTime.output_unique`; conversely, substituting `w = g x` gives the chosen computation. For the second characterization, unfold `ComputesInTime` and `ComputesInTimeAndSpace`. The existential space variable is constrained only to equal `M.tm.spaceUsed (M.tm.initCfg x) t`, so that very natural number supplies the reverse-direction witness. These are distinct useful facts: one characterizes the graph of a total function after existentially quantifying time; the other unfolds a fixed-time predicate without assuming totality.

The promotion recommendations are as follows.

| Candidate | Recommended public name and home | Statement requirements before promotion |
|---|---|---|
| A's completed-output characterization | `Turing.FinTM.Computes.exists_computesInTime_iff`, in `Finite.lean`. The requested `Computes.halts_iff_eq` is also acceptable if its docstring explicitly says “halts with completed output `w`.” | Keep its arbitrary-alphabet statement and `M.Computes g` hypothesis. No mathematical repair is needed. Do not replace completed output by an intermediate emitted prefix. |
| B's fixed-time characterization | `Turing.FinTM.computesInTime_iff`, in `Finite.lean`. | Generalize the unnecessary `Bool` restriction to `{Symbol : Type}` before sharing. No `Fintype` or `DecidableEq` assumption is needed. Keep this lemma as well as A's. |
| C's state mapping and relabeling | A non-vendored `TuringMachine/StateRenaming.lean`, depending on the raw deterministic model. Reuse the existing public name `Turing.Action.mapState`; add `Cfg.mapState`, its application lemma, `MultiTapeTM.relabelState`, and step/run correspondence. | Move the existing `Action.mapState` out of `Oracle.lean` into the shared lower layer and import it from Oracle and Encoding. Retain arbitrary functions for action/configuration mapping and an equivalence for machine relabeling. Name the current run lemma explicitly as an initialized-run lemma, such as `relabelState_runFrom_init`. An arbitrary-starting-configuration version would be a useful additional theorem, requiring its own checked statement. Preserve the generic universes and avoid new finiteness assumptions. |

An arbitrary state function is insufficient for relabeling a whole transition table: if it identifies two states with different emissions on the same scanned symbols, the target state would need two different transitions. No such issue affects action application, which receives its action explicitly. Oracle's embedding also adds a tape and query states; generic state renaming should factor out its state-mapping component, not replace the entire oracle embedding.

The independent freeze comparison covered **eight modified modules**, containing **45 pre-existing explicit declarations**, and identified **85 new private explicit declarations**:

| Module | Pre-existing declarations checked | New private declarations |
|---|---:|---:|
| `TuringMachine/Composition.lean` | 8 | 31 |
| `TuringMachine/Encoding.lean` | 18 | 18 |
| `TuringMachine/Universal.lean` | 3 | 0 |
| `Uncomputability/Computable.lean` | 2 | 0 |
| `Uncomputability/Diagonalization.lean` | 4 | 0 |
| `Uncomputability/Halting.lean` | 5 | 1 |
| `ClassP/Examples.lean` | 3 | 15 |
| `ClassP/TimeConstructible.lean` | 2 | 20 |

Every pre-existing comment-stripped declaration header agrees with its baseline header. Independently reproducing the textual diff gives exactly 15 removed lines: twelve `sorry` lines and the three specified docstring closing lines. All other changes are additions. All 19 attached Lean modules have the Git blob hashes in the audited commit. The commit comparison reports exactly the eight modules above and four intervening commits; the manifest and toolchain files are unchanged. The added source contains no new `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, option command, or attribute command. The added imports are precisely the listed Fintype modules.

All three docstring appendices accurately describe implementation choices. The counter appendix states the proved potential bound and final emission charges. The conditional appendix records the first-emission invariant, live administrative state, and absorbing-halting argument. The coding appendix correctly distinguishes the private action mapper from the older sketch's `Action.mapState` name and describes eliminating `hk` before relabeling. None changes the mathematical claim or attribution.

The delivered machines were checked against the audited transition schedules and the source model's write-before-move, clamped-input, and append-only-output semantics.

* `pairDiagTM` has six active states and no work tape. States 0 and 1 emit each input bit twice, with the first emission stationary and the second moving right. States 0 and 2 emit the two separator bits at the right blank. State 3 makes the unconditional first left move; state 4 scans left and then moves right from the left blank; state 5 copies once and halts. Thus, for input length `n`,

  $$
  2n+2+(1+n+1)+n+1=4n+5\le 6(n+1).
  $$

  For `n=0`, the five transitions emit `false`, emit `true`, move left, move right, and halt. The output is exactly `pairEncode [] [] = [false,true]`. This is the corrected phase-4 schedule, including its separate initial rewind transition.

* `palTM` implements the copy/rewind/test table from the phase-1 findings. The right-blank copy transition moves only the input head left; the left-blank rewind transition moves the input head right and work head left together. The work head is then at cell `n−1`. Matching comparisons move the two heads in opposite directions; a mismatch emits `false` and halts. A successful run costs

  $$
  (n+1)+(n+1)+(n+1)=3(n+1).
  $$

  At `n=0`, the work head reaches `−1`, and the three boundary transitions emit `[true]`. The test state's acceptance on an input blank is sound on initialized runs: the established scan invariant places the work head at `−1` after all comparisons. It need not validate arbitrary corrupted configurations. This matches the previously audited adaptation of AB Examples 1.1 and 1.4, rather than asserting the book's unpadded numerical bound in this model.

* `counterTM` exactly implements the four-state count/carry/rewind/emit table in the phase-1 reaudit. Counting advances the input once per increment. Carry clears the initial true bits, writes a final true bit, and rewind returns through the untouched blank at work cell `−1`. If `r = counterCarry (i.bits)`, one increment costs `r+1+r+1 = 2r+2` transitions. The proved local identity and bit bridge give

  $$
  \operatorname{popcount}(i+1)+r=\operatorname{popcount}(i)+1.
  $$

  Consequently, if elapsed time `t` satisfies the invariant at count `i`,

  $$
  \begin{aligned}
  (t+2r+2)+2\operatorname{popcount}(i+1)
    &=t+2\operatorname{popcount}(i)+4\\
    &\le 4i+4=4(i+1).
  \end{aligned}
  $$

  The base case has `t=0` and `popcount(0)=0`. At count `n`, nonnegativity of the potential yields `t≤4n`. Entering emission costs one step, emitting costs `length(n.bits)` steps, and the final blank halts in one step. Therefore

  $$
  \begin{aligned}
  t+1+\operatorname{length}(n.\mathrm{bits})+1
   &\le 4n+\operatorname{length}(n.\mathrm{bits})+2\\
   &\le 5n+2\\
   &\le 5(n+1).
  \end{aligned}
  $$

  Here `counter_bits_length` supplies `length(n.bits)≤n`, including zero. The empty input takes exactly two transitions and emits `[]`. Thus `c=5` is valid for every `n`.

  `counterInc_bits` is the correct canonical-representation bridge. Its cases are `[] ↦ [true]`; for `m>0`, `false :: m.bits ↦ true :: m.bits`; and `true :: m.bits ↦ false :: counterInc(m.bits) = false :: (m+1).bits`. These are respectively the representations of `0 ↦ 1`, `2m ↦ 2m+1`, and `2m+1 ↦ 2m+2`. Starting with `0.bits=[]`, exact equality to `(i+1).bits` preserves the absence of redundant high zeros. The potential lemma alone, which accepts arbitrary Boolean lists, would not establish that canonicality.

* `condTM` captures emissions with `reg.or a.output`, so the first emission wins and later nonemitting transitions preserve it. The invariant is `reg = simulatedOutput.head?`. Even when the simulated successor is `none`, the composite successor is `some (.inl (none, reg))`: the composite remains live. It starts rewinding only from that administrative state. For an input-head position `j`, the first left move gives `max(j−1,0)≤n`, after which the scan reaches 0 and the final right move reaches 1. This includes both boundaries and `n=0`.

  The controller's work tapes are separate from the fresh branch tapes, and its simulated emissions do not reach the real output. If the register is empty at dispatch, `reg.map ... = none` halts without output; that case is excluded by the theorem's singleton-output hypothesis. An early emission followed by divergence never dispatches. Under the hypothesis, the first completed controller computation identifies the register with `p x`. The expression `branchTM M₁ M₂ false` in the transition dispatcher does not force the false branch: the Boolean parameter affects only that machine's initial state; its transition function is independent of the parameter, and dispatch chooses the initial state using the register.

The remaining small gadgets also conform to their sketches. `constTM` emits the fixed word and uses one final halting step, including an empty word. `ifEqTM` tests the boundary after the last expected bit, so an extra input symbol is rejected, while an early blank or mismatching bit selects the other emission chain. The bound is at most `w₀.length + max u.length v.length + 2` before absorbing it into the stated linear budget. `pairDecode` consumes aligned pairs, recovers either doubled bit, and treats `[false,true]` as the separator; its round trip proves injectivity, including empty components.

There is no degenerate-state arithmetic defect in `exists_codeTM`. The initial state supplies an inhabitant, hence

$$
1\le\operatorname{card}(M.\mathrm{State}),\qquad
(\operatorname{card}(M.\mathrm{State})-1)+1=\operatorname{card}(M.\mathrm{State}).
$$

For a singleton state type the witness has `numStates=0`, and its actual state type is `Fin 1`, as required by `CodeTM`. An empty state type cannot support the supplied machine. Eliminating `hk` changes no alphabet or tape semantics. State relabeling preserves whole configurations apart from the state coordinate; the existential space witness is then recovered directly in both directions of the public theorem.

All nine remaining sorry declarations retain their audited forms. For the five in modified files, their complete docstring, declaration, and `sorry` body were compared byte-for-byte with the baseline. The other four reside in files untouched by the pinned commit comparison, whose attached contents match their repository blobs.

| Remaining declaration | Sketch disposition after epoch 1 |
|---|---|
| `computesFunInTime_comp` | The buffered two-phase construction remains implementable. Preserve output redirection, fresh second-phase tapes, and the monotonicity argument `length(f x)≤T₁(length x)` followed by `T₂(length(f x))≤T₂(T₁(length x))`. A bounded simulation invariant is still needed. |
| `exists_comp_partial` | Retain the compulsory first left move on the buffer, the right-boundary initial tag for an empty intermediate word, and clamping at both virtual boundaries. The two directions concern completed outputs and must exclude halting during administrative transitions. |
| `alphabet_reduction` | The fixed-width block construction, all-blank encoding of logical blank, and `k=0` case remain compatible with the model. No new helper invalidates the audited sketch. |
| `one_work_tape` | The marked-payload enlarged alphabet and sweep construction remain obligations; `k=0` is handled by an unused work tape. The new small-machine constructions do not discharge the sweep invariant. |
| `nonnegative_heads` | Preserve the detectable origin flag, independent folded payloads, stationary crossings at the fold, and safe behavior on nonembedded input symbols. The new counter's negative work-head visit is not a counterexample: this theorem constructs a different machine. |
| `oblivious_of_mem_DTIME` | Preserve the all-false-input simulation of the constructibility witness, fixed sweeps, parked real input head, and fixed final time. The newly proved identity example alone does not replace the arbitrary constructibility witness. |
| `exists_effectiveMachineCode` | The aligned parser is now an explicit list function, but its in-model implementation, record validation, short-circuit rejection, padding handling, and canonizer remain to be constructed. A Lean list parser alone is not an in-model parsing machine. |
| `universal` | Code-first preprocessing and the marked virtual left boundary remain essential. The total-function corollary is not a replacement for this partial evaluator construction. |
| `timed_universal` | Preserve buffered output, deadline-inclusive halting, timeout at `t=0`, and the bounded clock simulation. The ordinary counter is relevant infrastructure, not a completed timed evaluator. |

In particular, B's `leftCfg`/`rightCfg` suite is sound within its actual hypotheses but is not already a buffered-composition simulator. Both embeddings preserve the original input parameter, native input position, and output list; `leftAction`/`rightAction` pass emissions through. For example, a first component emitting a bit changes the embedded real output, whereas composition phase one must keep that output empty and write the bit to a buffer. A second component reading `y` cannot use the same-input configuration equation directly when the physical input is `x`. Moreover, `rewind_scan` and `rewind_from_any` inspect the native input and preserve work heads, so they do not rewind a buffer work head. Epoch 2 can reuse the tape-partition and induction patterns, but must add the buffer representation and virtual-input relation. The untimed existential conclusion of `rewind_from_any` also supplies no public numerical bound for the timed composition proof.

The placement of these helpers after the two remaining composition theorems is an additional practical constraint: Lean has no forward references. A fill that uses them in those earlier proof bodies must first move the required private infrastructure above its use, preserving its statements, or place genuinely shared infrastructure in an earlier imported module. This is a source-order/refactoring obligation, not a false helper statement. No new private name is directly referenced from another source module; public theorems intentionally depend on their own private helpers.

The assembly checks follow the actual quantifier scopes. `Computes.exists_computesFunInTime` and `UC_not_computable` use no evaluator. The former takes finite suprema of chosen halting times, with positive-length inputs vacuous over an empty alphabet. The latter normalizes the hypothetical total decider, relabels it, and chooses its fixed code using `decode_encode`; it never executes encoding or decoding.

`universal_quadratic` chooses one evaluator before quantifying over the simulated machine and uses only `(hCU x).1`. With `(T n+1)²≥1`, its absorption is exactly

$$
C_U\bigl(c_1(T(n)+1)^2+1\bigr)
\le C_U(c_1+1)(T(n)+1)^2.
$$

`UC_computable_of_HALT_computable` likewise chooses one evaluator before the per-input cases. It constructs the diagonal HALT decider, the self-pair/evaluator/postprocessor branch, and the constant-true branch using the stated gadgets and three applications of `exists_comp_partial`. A positive HALT answer supplies an actual decoded halting witness; `(hC α).1` supplies the evaluator's completed output. Output uniqueness identifies whether that output is `[true]`. A negative answer selects the constant branch. Neither proof uses the evaluator's converse clause or requires a globally named evaluator shared with other theorems.

The independent elaboration used Lean 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, and mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The locally available dependency checkouts used by the sweep matched the manifest and had clean tracked source trees. All 22 module sources came from the verified packet or the pinned repository. I used a fresh output tree, the prescribed dependency order and direct Lean invocations, checking each actual process exit code and newly generated `.olean`; no `lake build` was used. A narrowly scoped executable-path compatibility shim was needed in the auditor's runtime. Imported dependency caches were reused; they were not rebuilt from scratch.

Result: **22 successful process exits, 22 fresh module oleans, zero `error:` lines, exactly nine `declaration uses 'sorry'` warnings**. The only other warnings were the three pre-existing style/unused-variable warnings in `Configuration.lean`.

All 13 requested `#print axioms` results were reproduced. `pairEncode_injective` uses `[propext, Quot.sound]`. The other eight listed results without admissions use `[propext, Classical.choice, Quot.sound]`: the constant machine, comparator, conditional, diagonal pairing, coding relabeling, palindrome, identity constructibility, and finite-length time-bound bridge. The four remaining listed results have those usual axioms plus `sorryAx`. Traversing the checked environment's constant dependencies identifies their precise remaining admitted theorem dependencies:

| Theorem | Reachable declarations among the nine remaining sorries |
|---|---|
| `universal_quadratic` | `alphabet_reduction`, `one_work_tape`, `universal` |
| `UC_not_computable` | `alphabet_reduction`, `one_work_tape` |
| `UC_computable_of_HALT_computable` | `exists_comp_partial`, `universal` |
| `HALT_not_computable` | `alphabet_reduction`, `one_work_tape`, `exists_comp_partial`, `universal` |

Thus the dependency explanation is correct. The phrase “four assembly theorems” needs precise bookkeeping: of the four newly filled Batch A targets, the finite-length time-bound bridge is admission-free; the fourth admission-bearing item in the displayed footprint list is the already-proved consequence `HALT_not_computable`. None of these parametrized theorems currently depends on `exists_effectiveMachineCode`; constructing an inhabitant remains a separate obligation.

The independent sweep also exposed a defect in the prescribed verification script. At lines 31–36 of [`scripts/lean_check_tree.sh`](https://github.com/Shilun-Allan-Li/tcslib/blob/d3393b35764710ff3d7ae538d5133284291d9ef4/scripts/lean_check_tree.sh), the status of the command substitution running Lean is discarded; the script checks only for the text `error:` and then exits 0. In an isolated copy, I supplied a test executable named `lean` that printed `compiler terminated without diagnostics`, exited 23, and created no output. The unchanged checker returned 0 and created no `.olean`. This is a concrete false-success path, not evidence that the present Lean proofs failed. The documented sweep recipe's `|| break` also does not propagate a failing status as a failing overall shell command.

The fix is to capture and propagate Lean's status, reject a missing output, prevent stale output from satisfying that check, and make the sweep exit unsuccessfully on a failed module. The independently checked 22-module result above already used these stronger conditions. This issue is major for the reliability of the campaign's verification gate, while being pre-existing and separate from the mathematical content of the epoch-1 fills.

For delivery provenance, repository history corroborates the four integrated commits and their file ownership. The original delivery archives/git bundles and their asserted hash manifests are not included in the uploaded packet. Their mutual consistency, exact original bases, runner credential limitations, and cross-vendor independence therefore remain maintainer/agent attestations. Commit author metadata is not proof of those assertions. The source/hash/build checks here establish the delivered snapshot independently of those delivery-history claims.

The findings table follows. “Note” records a specific disposition or remaining obligation, not general approval.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `scripts/lean_check_tree.sh` · elaboration gate; attestation 2 | The pre-existing checker can report success after Lean fails. | The command's exit status is discarded. An isolated test executable exited 23 and produced no `.olean`; the unchanged checker returned 0. The sweep's `|| break` can also hide failure in the overall exit status. The independently guarded current sweep passed. | Propagate the compiler status; require fresh output; propagate a failed module out of the sweep. Keep exit/output evidence with future attestations. |
| 2 | minor | Audit brief · priority 1 and scope table | The packet miscounts the changed modules and omits one promised context document. | It says six modified modules but names eight; the independent diff confirms eight. `phase4-findings.md` is referenced as attached but is absent from the 30 file sections. It was obtained from the pinned repository for this audit. | Change six to eight and include the promised findings document in future upload-only packets. |
| 3 | note | Eight changed modules · freeze and soundness scan | The reported statement freeze is independently supported. | 45 old declaration headers unchanged; 85 new explicit declarations all private; all 19 attached Lean blobs match; exactly twelve sorry removals and three docstring-closing replacements; no added soundness bypass. | Retain this baseline and rerun the comparison after any promotion/refactoring. |
| 4 | note | `halts_iff_eq_of_computes`; `computesInTime_iff` | Both are sound promotion candidates with different roles. | Total-function completed-output uniqueness proves A; existentially choosing actual space proves B. B's Boolean restriction is unnecessary. | Promote both into `Finite.lean`, with the names and generalization specified above. Preserve totality only in A. |
| 5 | note | `Encoding.lean · codeMapAction` through `codeRelabel_run` | State renaming is sound; the machine construction correctly requires an equivalence. | Mapping application works for any function; identifying states with different transitions would invalidate unrestricted machine relabeling. The present run theorem is initialized-only. | Factor out a non-vendored state-renaming module, preserving `Action.mapState`; distinguish initialized and arbitrary-start run lemmas. |
| 6 | note | `Encoding.lean · pairDiagTM` | The delivered controller implements the corrected `4n+5` schedule. | Two emissions per first-pass bit, two separator transitions, `n+2` rewind transitions, second copy and halt; empty input takes five transitions. | No mathematical change required. Retain the explicit rewind charge. |
| 7 | note | `Examples.lean · palTM` | The delivered boundary transitions agree with the audited palindrome machine. | Copy and rewind align heads at input position 1 and work position `n−1`; complete matching runs take `3(n+1)` steps. Empty input accepts in three transitions. | No change required. Keep the reachable-configuration invariant when reusing the test state. |
| 8 | note | `TimeConstructible.lean · counterInc_potential`, `counterInc_bits`, `counter_count`, `timeConstructible_id` | The exact binary bridge and amortization justify `c=5`, including zero. | Each increment costs `2r+2`; elapsed time plus twice popcount increases by four. Emission adds `length(n.bits)+2≤n+2`; `n=0` takes two transitions. | No change required. Do not infer canonical output from the potential identity alone; retain the `Nat.bits` bridge. |
| 9 | note | `Composition.lean · condTM`, `exists_cond` | Register, administrative-state, rewind, and dispatch behavior match the audited design. | `Option.or` keeps the first emission; simulated halt remains a live composite state; fresh branch tapes and suppressed controller output are preserved; empty-register dispatch halts; early emission followed by divergence never dispatches. The apparent `false` parameter in the branch transition table does not select the branch. | No change required. Preserve the pre-halt hypothesis of `controlCfg_run` and the chosen first-halting-time argument. |
| 10 | note | `Encoding.lean · exists_codeTM`; three docstring appendices | Card arithmetic and the implementation notes are accurate. | `q₀` gives positive state cardinality, so subtraction/addition recovers the cardinality; one state gives `numStates=0` and `Fin 1`. All three appendices describe the delivered implementation without altering a claim. | No statement repair required. |
| 11 | note | Remaining nine sorries; B's proposed epoch-2 helper reuse | The audited statements/sketches are unchanged, but the helpers do not already implement buffered composition. | The existing embeddings preserve the same native input and pass output through; their rewinds leave work heads fixed. Buffering and virtual-input clamping need new invariants. Helpers also occur after the current composition proof bodies. | Preserve the nine statements. Move required helpers before use or into an earlier shared module; add buffer/virtual-input invariants and explicit time bounds. |
| 12 | note | Batch A; `HALT_not_computable` · evaluator scope and axiom footprints | The assemblies use exactly the intended interfaces; the remaining admissions are accurately located. | All 13 footprints reproduced; checked dependency traversal gives the four rows above. Only the quadratic corollary and HALT-to-UC reduction use an evaluator, each choosing one once and using only its forward clause. | Keep the dependency labels. Distinguish the clean finite-length bridge from the already-proved, admission-bearing HALT consequence. |
| 13 | note | Attestations 2 and 5 · verification and delivery provenance | Current elaboration is independently reproduced; original delivery history is only partially checkable. | 22 successful Lean exits and fresh oleans, nine expected sorry warnings, pinned dependencies. The original archives and their hash manifests are not supplied. | Preserve current build evidence; attach original manifests/archives if independent delivery-provenance verification is required. |

Notation glossary: `x` is an input word and `n` its length; `w` is a proposed completed output; `g` is the prescribed string function; `M`, `M₁`, `M₂`, `D`, and `U` are the machines named in the source statements; `e` is a state map or equivalence as indicated. `i` counts completed increments, `t` is elapsed time, and `r=counterCarry(i.bits)` counts the initial true bits cleared by the next increment. `popcount(i)=i.bits.count true`; `m` is the high-order integer in the binary cases. `j` is a native input-head position; `length` is list length; `card` is finite cardinality; `::` prepends a list element. `T` is the time-bound function, and `C_U,c₁` are its simulation constants from `universal_quadratic`. All other identifiers retain their Lean-source meanings.

## ===== audits/epoch1-resolutions.md =====

# Epoch 1 (fill round) — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Fill campaign" (audit rounds at epoch
boundaries). External auditor: cross-vendor LLM per decision log.

## Round 1 (`epoch1-pack.md` → `epoch1-findings.md`, audited at `d3393b35`)

**Zero statement-level blockers or majors.** Every mathematical attestation was
independently reproduced by the auditor: the statement freeze (45 pre-existing
declaration headers unchanged across the eight modified modules; 85 new
declarations, all `private`; exactly the 12 sorry removals and 3 docstring-tail
rewrites), the full 22-module elaboration (with the auditor's own strengthened
exit-code and fresh-olean conditions), and all 13 `#print axioms` footprints —
plus an environment-traversal locating each assembly theorem's exact remaining
admitted dependencies (findings table, row 12). All four delivered machines
were certified against their audited schedules (`4n+5` pairing; `3(n+1)`
palindrome; the four-state counter's `c = 5` amortization; `condTM`'s
register/rewind/dispatch design, including the confirmation that the apparent
`false` parameter in its dispatcher does not select the branch).

One **major (tooling, pre-existing — not epoch-1 content)** and one **minor
(pack erratum)**:

| Finding | Resolution |
|---|---|
| 1 major — `scripts/lean_check_tree.sh` discards Lean's exit status and checks only for `error:` text, so a compiler crash without diagnostics passes; the documented sweep's `\|\| break` also hides failure in the overall status. (Auditor demonstrated with a stub `lean` exiting 23: old gate returned 0.) | Script rewritten in the closing commit: Lean's exit status is captured and propagated; the target `.olean` is deleted up front and required to exist afterward (no stale-output satisfaction); the documented sweep recipe now runs in a subshell with `\|\| exit 1`. The auditor's exploit was reproduced against the old script (exit 0) and re-run against the new one (fails on both the status and missing-olean conditions). The full 22-module sweep was then re-run under the strengthened gate: all modules pass, zero errors, the nine expected sorry warnings. Note: epoch-1's mathematical evidence was never in doubt — the integration sweep used a freshly wiped olean tree whose 22 emitted oleans (and the facades' imports of them) certify completion, and the auditor's independent guarded run reproduced it — but the gate itself is now sound for future rounds |
| 2 minor — the pack's scope prose says "six modified modules" while naming eight (eight is correct), and `phase4-findings.md` was cited as attached but absent from the bundle (the auditor fetched it from the repository) | Acknowledged; the shipped pack is preserved as the historical artifact (phase-3 precedent). Future packs: count files programmatically and verify every promised attachment is present in the assembled bundle |

Selected note dispositions (full table in the findings file):

- **Promotions endorsed** (finding 4, 5; audit question 1): both completed-run
  characterizations go to `Finite.lean` at the epoch-2 merge — batch A's as
  `Turing.FinTM.Computes.exists_computesInTime_iff` (arbitrary alphabet,
  totality hypothesis kept), batch B's as `Turing.FinTM.computesInTime_iff`
  **generalized from `Bool` to an arbitrary `Symbol`** before sharing; both are
  kept (different roles). Batch C's suite becomes a non-vendored
  `TuringMachine/StateRenaming.lean` at the raw-model layer, *reusing the
  existing public name `Turing.Action.mapState`* (currently in `Oracle.lean`)
  rather than a parallel one, with the run-correspondence lemma explicitly
  named as initialized-run (`relabelState_runFrom_init`-style); arbitrary
  functions suffice for action/configuration mapping, an equivalence is
  genuinely required for machine relabeling (the auditor's identification
  argument), and no finiteness assumptions are added.
- **Epoch-2 constraints recorded** (finding 11): B's `leftCfg`/`rightCfg`
  suite is sound *as stated* but is not yet a buffered-composition simulator —
  the embeddings pass emissions to the real output and preserve the native
  input, whereas `exists_comp_partial`/`computesFunInTime_comp` need a buffer
  representation, virtual-input clamping invariants, and (for `comp`) explicit
  time bounds. Additionally a **source-order obligation**: the helpers sit
  *after* the two remaining composition sorries in `Composition.lean`, and
  Lean has no forward references — shared infrastructure must move above its
  use or into an earlier imported module. Both constraints fold into the
  epoch-2 brief 2A and the planned `Simulation.lean`/`StateRenaming.lean`
  split of the ~950-line `Composition.lean` (policy §1 size threshold).
- **Provenance scope** (finding 13): the auditor verified the delivered
  snapshot independently (blob hashes, diff, elaboration, axioms); the
  original delivery archives' history remains a maintainer attestation. The
  original zips are retained locally by the maintainer; attach manifests if
  independent delivery-provenance verification is ever required.

## Gate status

**CLOSED** — the statement surface is clean (zero blockers/majors); the sole
major was a verification-tooling defect, fixed and re-verified in the closing
commit. Standing state: 12 of 21 sorries proved and audited; 9 remain, all
with sketches the auditor re-confirmed implementable (findings rows in the
"Remaining declaration" table). Carried obligations, tracked in the plan:

- Epoch-2 merge pre-work: the two `Finite.lean` promotions (with the auditor's
  names and the `Symbol` generalization), the `StateRenaming.lean` module
  unifying `Action.mapState`, and the `Composition.lean` split; re-run the
  freeze comparison after the refactor (finding 3).
- Epoch-2 brief 2A must demand the buffer/virtual-input invariants and time
  bounds beyond the epoch-1 gadgets (finding 11).
- Future packs ship exact attachment inventories (finding 2) and keep
  exit/output evidence with attestations (finding 1).

## ===== audits/phase2-findings.md =====

**Phase 2 external audit: statements, model fidelity, and proof obligations**

Audited the supplied `phase2-bundle.md`, identified by its brief as commit `2917a1b9` on `complexity/arora-barak-ch1`, against the attached Arora–Barak textbook. The principal source locations are printed pp. 16–19 (PDF 42–45), pp. 25–26 (PDF 51–52), and Exercise 1.5 on p. 34 (PDF 60). I additionally checked the underlying tape model on pp. 12–13 and the intended Cook–Levin use on pp. 47–49 (PDF 73–75).

This is a mathematical statement/source audit, not a Lean proof certificate. The packet contains 11 new `sorry`s and 28 in total, as advertised. Lean and Lake are unavailable in this environment, so I have not independently reproduced the claimed successful elaboration or verified the repository commit. Phase-1 material was spot-checked only. The input attachments were not modified.

There are four major findings concerning a false implication, an inadequate simulation sketch, an undischarged model bridge, and an overstatement of time-class invariance. These findings do not establish a counterexample to any of the eleven new Lean theorem statements; the declaration-specific assessments below distinguish mathematical plausibility and constructive arguments from completed formal proofs.

The following restatements were made from the declaration bodies, extracted without Lean comments, before comparing their docstrings. File references abbreviate the attached paths: machine files live under `TCSlib/Complexity/TuringMachine/`, and class files under `TCSlib/Complexity/ClassP/`. The plan decision log refers to `AroraBarakChapter1Plan.md`.

| Declaration | Independent mathematical restatement | Comparison with the source |
|---|---|---|
| `TuringMachine/Finite.lean` · `ComputesFunInTimeVia` | On every string over the source alphabet, the machine halts by the stated length bound on the symbolwise embedded input and produces the symbolwise embedded function value. It imposes no computation requirement on other target-alphabet inputs. | Appropriate interface for binary inputs and outputs inside a larger common tape alphabet; more generally usable for an embedded source alphabet. This is not a promise restricted to some binary strings. |
| `Composition.lean` · `computesFunInTime_id` | Some finite binary machine copies every input within a constant times its length plus one. | Technical composition infrastructure consistent with §1.3; not a separately numbered AB claim. |
| `Composition.lean` · `computesFunInTime_const` | For each fixed binary word there is a finite binary machine producing it on every input within a constant times the input length plus one. The machine and constant may depend on the word. | Correct but weaker than the available constant-time bound in the input length. |
| `Composition.lean` · `computesFunInTime_comp` | Given total computations of two binary string functions with the stated budgets, and a nondecreasing second budget, a finite binary machine computes their composition within a constant times the sum of the first budget, the second budget evaluated at the first, and one. | A valid quantitative version of the high-level composition convention; it concerns this append-only model throughout. |
| `Robustness/AlphabetReduction.lean` · `alphabet_reduction` | A finite-alphabet machine computing a total binary string function through a bit embedding has a binary simulator with exactly the same number of work tapes and time at most a constant times the original budget plus one. | Acceptable in-model analogue of Claim 1.5. It generalizes Boolean output to strings and drops time constructibility; neither is needed by this simulation. The explicit logarithmic constant is not retained. |
| `Robustness/SingleTape.lean` · `one_work_tape` | A total string computation over any finite alphabet can be reproduced through an embedding into a finite enlarged alphabet using exactly one work tape in padded quadratic time. | A weaker target restriction than Claim 1.6: dedicated input and output remain. Accept the declared restricted scope, not equivalence to the merged single-tape claim. |
| `Robustness/SingleTape.lean` · `one_work_tape_binary` | A total binary string computation has a binary simulator using exactly one work tape with the same padded quadratic bound. | Correct combination of the preceding two in-model statements; it still does not merge input, work, and output. |
| `Robustness/Bidirectional.lean` · `NonnegativeHeads` | On every initialized input and at every time, each work head has a nonnegative integer coordinate. Nothing is required of arbitrary starting configurations. | Appropriate semantic predicate for unidirectional work-tape use in the existing model. |
| `Robustness/Bidirectional.lean` · `nonnegative_heads` | A total finite-alphabet computation has a finite enlarged-alphabet simulator preserving the work-tape count, computing the embedded function with constant slowdown, and using nonnegative work coordinates on every input over its enlarged alphabet. | Acceptable in-model analogue of Claim 1.8. The nonnegativity obligation includes inputs outside the embedding range, although functional correctness does not. |
| `Robustness/Oblivious.lean` · `Oblivious` | At each natural-number time, every two inputs of equal length give the same numerical input-head position and the same tuple of work-head positions. It says nothing about states, halting indicators, or output emissions. | Matches length-dependent trajectories of the heads represented in this model. It does not imply equal halting times and is not, without a bridge, AB's predicate on all physical heads. |
| `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME` | A language in `DTIME T`, for time-constructible `T` in the repaired sense, has some finite binary decider satisfying that head-position predicate within padded quadratic time. | The literal formula is supportable. It contains neither the two-tape normal form from Exercise 1.5's final sentence nor a uniform-halting conclusion. |
| `ClassP/ModelInvariance.lean` · `DecidesInTimeVia` | On every embedded binary input, the machine halts within the stated bound and outputs exactly the embedded membership bit. | Correct embedded-alphabet form of a decider from §1.6. |
| `ClassP/ModelInvariance.lean` · `mem_DTIME_of_decidesInTimeVia` | Such a finite-alphabet decider puts the language in binary `DTIME` for the original budget plus one, with a constant absorbed into the class definition. | Valid alphabet-invariance direction; no tape-count invariance of a fixed time class is asserted by this theorem. |
| `ClassP/ModelInvariance.lean` · `mem_P_of_decidesInTimeVia_poly` | An embedded finite-alphabet decider with any stated polynomial bound puts the binary language in `P`. | Valid alphabet-invariance corollary of §1.6.1 within the declared conventions. |
| `ClassP/ModelInvariance.lean` · `mem_P_iff_one_work_tape` | A language is in `P` exactly when some binary machine with one work tape decides it within a constant times a power of input length plus one. | Correct invariance of `P` under reducing the number of work tapes to one; not a bridge to AB's merged single-tape structure. |

The findings table uses the severity definitions in the brief.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `Robustness/Oblivious.lean` · `Oblivious` design; plan decision log | Frozen heads force length-determined halting. | A two-live-state machine with no work tapes keeps its input head stationary, halts after one step on `[false]`, and after two on `[true]`. It satisfies `Oblivious` on all inputs. The complete transition table and induction appear below. | Remove the implication from both documents. If a downstream normal form needs equal halting times, prove it separately or add it to that normal-form theorem. |
| 2 | major | `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME` | The supplied sketch establishes the quadratic oblivious simulation. | `one_work_tape_binary` already has a quadratic time bound; only linearly many simulated steps of its output are not justified. The time-constructibility witness can have input-dependent trajectories, and retaining a simulated machine's real input-head moves also fails obliviousness. | Run the clock on a virtual constant string of the same length; copy the real input; sweep a fixed layout of the original machine for a length-determined budget, including its virtual input head. Use fixed-duration binary coding. This supports the literal theorem without strengthening `TimeConstructible`. |
| 3 | major | `Composition.lean` · module design; plan decision log | Composition discharges the read-write/append-only output and initialization convention obligations. | Both hypotheses and the conclusion of `computesFunInTime_comp` already use append-only output. Its intermediate buffer receives irrevocable emissions; no read-write-output source model, final-output extraction, or initialization relation appears in the statement. Existential constants do not establish semantic equivalence. | Add explicit simulation statements and configuration invariants before recording these obligations as discharged, or mark the bridges deferred/waived and restrict source-transfer claims accordingly. A new proof need not precede the skeleton, but the missing bridge statement must. |
| 4 | major | `ClassP/ModelInvariance.lean` · module description | `DTIME` up to constants and `P` are independent of alphabet size and number of work tapes. | Constant slowdown is supplied for alphabet reduction; tape reduction supplies a quadratic bound. The theorems do not justify preserving a fixed `DTIME T` when reducing tapes. AB §1.6.1 draws polynomial-time invariance, not invariance of every time class. | State separately: alphabet reduction preserves time up to a constant; tape reduction preserves polynomial time with quadratic overhead. Keep the existing theorem formulas. |
| 5 | minor | `Robustness/SingleTape.lean` · `one_work_tape`, `one_work_tape_binary`; `mem_P_iff_one_work_tape` | One work tape is a faithful replacement for all of Claim 1.6. | AB explicitly merges input, work, and output. The retained input/work pair can decide palindromes in linear time; the book records a quadratic lower bound for the merged single-tape model. This difference survives constant absorption. | Call these “in-model analogues” and retain the declared exclusion of the merged model. Do not mark the full cross-model claim proved. The restricted scope itself is acceptable. |
| 6 | minor | `Robustness/Oblivious.lean` · `Oblivious`; brief rendering 4 | Omitting output positions literally matches AB's all-head definition. | AB's output tape is a read-write tape with a head; the present stream has no such position field. Equality of the two stored kinds of head positions places no restriction on output emission schedules. Conversely, AB head-position equality does not by itself require equal write times. | Explicitly identify this as input/work-head obliviousness under the stream-output convention. For a direct all-head bridge, specify how output is represented; a fixed-time final emission works for the current one-bit decider theorem. Do not silently identify AB write times with stream length. |
| 7 | minor | `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME` | The statement covers the whole normal-form conclusion of Exercise 1.5. | The exercise additionally requires one input tape and one work/output tape. The theorem leaves `M.k` unrestricted. A separate existential one-work-tape theorem cannot be conjoined with this existential oblivious theorem without a preservation argument. | Label the theorem as the first assertion, adapted to this model. If the later proof needs both properties, add a simultaneous normal form, at least `M.k = 1 ∧ M.Oblivious`, with its output-convention bridge. |
| 8 | minor | `Robustness/AlphabetReduction.lean` · `alphabet_reduction` sketch | The stated binary block length can encode every nonblank symbol and reserve an additional binary code for blank. | For two nonblank symbols the proposed length is one, leaving only two binary codes for three logical values. The physical alphabet also contains `none`, but the sketch does not distinguish that solution from reserving a binary code. | Encode logical blank by an all-`none` block and nonblank symbols by binary blocks; explain lazy initialization. Alternatively enlarge the binary block length and give an explicit representation of initially blank blocks. No extra work tape is necessary. |
| 9 | minor | `Robustness/SingleTape.lean` · `one_work_tape` sketch | Pairs of a source symbol and a head flag suffice for the stated marked-cell representation. | Source cells have type `Option Γ`, and every initial scanned cell is blank. The literal product `Γ × Bool` omits a marked blank; it also needs a specified treatment of sweep boundaries. | Use tagged `Option Γ` payloads, head flags, and boundary information in the enlarged finite alphabet. Handle `k = 0` separately by adding an unused tape. |
| 10 | minor | `Robustness/Bidirectional.lean` · `nonnegative_heads` sketch | The origin is directly detectable and folded coordinates are absolute values. | The transition table cannot read a head coordinate, and all work tapes start blank. With pairs `(j, -j-1)`, the virtual positions `0` and `-1` both map to physical fold coordinate zero; this is not absolute value. | Initialize an origin tag or sentinel and preserve it. Use the piecewise folding coordinate described below, with any sentinel offset stated explicitly, and specify safe handling of non-embedded input symbols. The theorem's formula need not change. |
| 11 | note | `Finite.lean` · `ComputesFunInTimeVia`; `AlphabetReduction.lean` · `alphabet_reduction` | All binary inputs, an arbitrary bit embedding, and the unchanged tape count are appropriate. | The alphabet may contain irrelevant other input symbols. On a valid input every emitted symbol belongs to the final embedded output because output only grows; even an early emission cannot later be erased. Finite control and fixed blocks suffice with the existing tapes. | No statement change. Document the generalization from Boolean to string output and the unnecessary time-constructibility hypothesis from the original claim. |
| 12 | note | `Composition.lean` · `computesFunInTime_comp`; `SingleTape.lean` · binary corollary; model-invariance corollaries | The length substitution and constant-absorption inequalities are valid. | Intermediate output length is at most actual halting time and hence the first budget. Monotonicity gives the required second-budget comparison. The padded square is at least one, so the extra alphabet-reduction constant is absorbable at every input length. Calculations are below. | Keep the statements. Global monotonicity is sufficient; eventual monotonicity or a finite maximum would support optional alternative APIs. |
| 13 | note | Plan decision log; `Oracle.lean` · convention disposition | Defer persistent-versus-erased query-tape polynomial simulation to the oracle-class phase. | None of the new results depends on this bridge, and no oracle complexity class is defined here. The current documentation already forbids transporting exact time bounds across these conventions. | Accept the deferral, with an explicit outstanding obligation before importing oracle-class invariance. Update the older phase-2 scope paragraph to agree with the decision log. |

The following arguments assess each of the eleven new `sorry`s as literally stated. They are constructive mathematical assessments, not claims that the unimplemented transition invariants have already been formalized.

| New `sorry` | Literal-statement assessment, with a 2–5 sentence argument |
|---|---|
| `computesFunInTime_id` | A machine with no work tapes emits the current input bit and moves right on each bit, then halts when it reads the right blank. It takes exactly `n + 1` steps, including one step on empty input, so constant one witnesses the theorem. One live state suffices because `none` is the halting state. |
| `computesFunInTime_const` | Use one live state for each successive output position and a final live state that halts on its next transition. This emits the fixed word and halts within its length plus one, independently of the input. Taking the theorem's constant to be that positive number gives the required bound even at length zero. |
| `computesFunInTime_comp` | Simulate the first machine while diverting its output to one fresh work tape, using fixed binary blocks for data and distinguishable boundaries. Rewind this buffer and simulate the second machine with its bounded input head represented on the buffer; the other two groups of work tapes simulate the original work tapes. The buffer length and rewind cost are at most a constant times the first budget, and monotonicity bounds the second phase by the second budget evaluated at the first. Phase switching and empty-buffer handling have constant cost, giving the stated sum. |
| `alphabet_reduction` | Store each original work cell in a fixed-length block on the corresponding binary work tape, with an all-blank block representing logical blank and binary blocks representing nonblank symbols. Finite control holds the original state, scanned symbols, and block phase, while actual input bits are interpreted through the embedding. On every valid input the output-prefix property ensures every emission has a bit preimage, so a finite decoder preserves output. A fixed number of microsteps per original step and constant startup give the bound while preserving the work-tape count, including zero. |
| `one_work_tape` | For positive tape count, interleave cells on one tape and explicitly encode marked blanks and sweep boundaries. After a given number of original steps, each head lies within that distance of its origin, so the interleaved active interval has length linear in that number, with a machine-dependent constant. A constant number of sweeps and bounded local mark updates simulate each step, and summing their costs gives the padded quadratic bound. For zero original work tapes, add one unused tape. |
| `one_work_tape_binary` | Apply the previous theorem and then alphabet reduction through its returned embedding. Alphabet reduction preserves the already established one-work-tape count. Its additive constant is bounded by a multiple of the padded square using the calculation below. |
| `nonnegative_heads` | Fold each work tape, retain a component bit for each virtual head, and initialize a detectable origin tag or sentinel. Crossing between virtual cells zero and minus one changes the component without moving the fold coordinate below zero; other moves change that coordinate by at most one. Source symbols outside the chosen input embedding can cause a safe halt, so nonnegative use holds even on malformed enlarged-alphabet inputs. Initialization and each simulated step cost a fixed constant, preserving the original work-tape count. |
| `oblivious_of_mem_DTIME` | The literal theorem is supportable, but its supplied sketch is inadequate for finding 2's reasons. Run the constructibility witness with every nonblank input symbol replaced by a fixed bit; its complete run then depends only on length and still computes the required budget. Copy the real input and simulate the original decider directly by fixed sweeps over a budget-sized marked layout, keeping the real input head parked during that simulation. Pad simulated halting, use a length-dependent counter and fixed-duration binary coding, and emit the stored answer at the end. This gives quadratically bounded trajectories and termination determined by length; the more explicit construction obligations are recorded below. |
| `mem_DTIME_of_decidesInTimeVia` | Apply alphabet reduction to the string function returning the singleton membership bit. Its result is a binary decider with budget a constant times the original budget plus one. That constant is precisely the witness required by the definition of the concluding `DTIME` class. |
| `mem_P_of_decidesInTimeVia_poly` | The preceding theorem yields `DTIME` membership for the given polynomial plus one. For every length, this is dominated by `(C + 1) * 2^d * (n^d + 1)`, as calculated below. Absorb constants and use the corresponding component of `P`. |
| `mem_P_iff_one_work_tape` | Forward, the existing polynomial characterization supplies a binary decider, to which the one-work-tape binary theorem applies. The resulting squared polynomial is bounded by `c * (C + 1)^2 * (n + 1)^(2*d)` at every length. Reverse, forget the tape-count conjunct and apply `mem_P_iff`. |

Here is a fully specified counterexample to the false implication in finding 1. Use zero work tapes, live states `start` and `delay`, and initial state `start`. Every action has zero input-head movement; the tuple of work actions is the unique empty tuple.

| Current state | Read input symbol | Emission | Successor state |
|---|---|---|---|
| `start` | `some true` | none | `some delay` |
| `start` | `some false` or `none` | `false` | `none` |
| `delay` | any | `true` | `none` |

This specifies a finite `FinTM Bool` transition table on every possible read. From `Cfg.init`, the numerical input-head position is one; `moveInputPos_zero` and induction on the number of steps imply that it is one at every time on every input. The work-position tuple is unique because the work-tape index type is empty. Therefore the two equalities in `Oblivious` hold for every pair of equal-length inputs and every time, including after halting.

On input `[false]`, the state is `some start` at time zero and `none` at time one. On input `[true]`, it is `some start` at time zero, `some delay` at time one, and `none` at time two. Thus the first halting times are respectively one and two although both inputs have length one. This also gives a total decider with input-dependent halting time; nontermination is not needed for the counterexample.

The definition already compares input-head positions after both halts: its quantifier ranges over all natural-number times. Adding that same comparison again cannot repair the implication. AB's Cook–Levin discussion on printed p. 47 explicitly assumes both equal runtime and prescribed head positions; to follow that normal form literally, add a separate guarantee of length-determined halting. Alternatively, a bounded tableau can run every computation to a common length-dependent upper bound using the existing absorbing halted configurations; this route needs no theorem that `Oblivious` alone determines the first halting time.

Output timing is a separate issue. A finite machine can keep all represented heads stationary, halt on every input after two steps, and emit its single answer on step one for a first bit `false` but on step two for a first bit `true`; therefore even equal first halting times would not constrain emission times. If one defines an implicit stream-output position as the number of emitted symbols, this example violates its obliviousness. AB's read-write output head, however, can write without moving, so equality of such stream positions is a choice of bridge, not a literal consequence of AB's wording. For decision computations, buffering the answer in finite control and emitting once at a common final time resolves this issue.

The main quantitative checks are as follows; they also address sublinear bounds and small inputs without importing AB's exact step counts.

1. **Composition and early emissions.** Let the actual first halting time of the first machine on `x` be `τ`. Absorption and `output_length_le` give

   \[
   |f(x)|
   =|\operatorname{output}(\operatorname{run}(x,\tau))|
   \le \tau\le T_1(|x|),
   \qquad
   T_2(|f(x)|)\le T_2(T_1(|x|)).
   \]

   Simulate, rewind, and switch phases in at most

   \[
   c_0\bigl(T_1(|x|)+|f(x)|+T_2(|f(x)|)+1\bigr)
   \le 2c_0\bigl(T_1(|x|)+T_2(T_1(|x|))+1\bigr),
   \]

   where `c₀` bounds the fixed per-step and phase-switching overheads; take `c = 2*c₀`. The proof uses no monotonicity of the first budget. Eventual monotonicity of the second budget would also suffice after absorbing the finite exceptional maximum; without either condition, replacing the evaluated second budget by the maximum over lengths up to the first budget is a valid alternative.

   On an embedded input, every output prefix up to the budget is a prefix of `(f x).map e`; hence every emitted symbol belongs to the range of the embedding. Past that budget, the machine is halted and emits nothing. An emission before the rest of the input has been read does not escape this argument: the total-computation hypothesis already requires that irrevocable emission to be correct.

2. **Visited-zone growth.** At original step `t`, every work-head coordinate lies between `-t` and `t`, by induction from zero using the one-cell movement bound. For positive `k`, the coordinates `j*k+i`, with `0 ≤ i < k`, fit in an interval of `k*(2*t+1)` cells; fixed guard blocks and boundary tags add at most a constant multiple of `k + 1`. For a run halting at `τ ≤ T(n)`, a constant-per-cell sweep construction therefore costs at most

   \[
   c_0+c_0\sum_{t=0}^{\tau-1}(t+1)
   =c_0\left(1+\frac{\tau(\tau+1)}2\right)
   \le 2c_0(T(n)+1)^2.
   \]

   Here `c₀` is a fixed overhead bound for this construction. No scan of the whole input is required for this in-model work-tape reduction, so no hypothesis `T(n) ≥ n` or time constructibility is needed here. This observation does not supply a bridge to the merged tape model.

3. **Binary-corollary constant.** Since `(T(n)+1)^2 ≥ 1`,

   \[
   c_2\bigl(c_1(T(n)+1)^2+1\bigr)
   \le c_2(c_1+1)(T(n)+1)^2.
   \]

   Thus `c = c₂*(c₁+1)` works at all lengths, not just eventually.

4. **Polynomial corollaries.** For natural `n,d`, splitting off `n = 0` and using `n+1 ≤ 2n` for `n ≥ 1` yields

   \[
   (n+1)^d\le 2^d(n^d+1),
   \]

   including `d = 0`. Consequently,

   \[
   C(n+1)^d+1
   \le(C+1)(n+1)^d
   \le(C+1)2^d(n^d+1),
   \]

   and

   \[
   c\bigl(C(n+1)^d+1\bigr)^2
   \le c(C+1)^2(n+1)^{2d}.
   \]

   Moreover, any `DecidesInTimeVia` hypothesis on all binary strings implies `T(n) ≥ 1` at every length: instantiate it on a string of `n` false bits and use impossibility of zero-step halting. Thus the alphabet-invariance conclusion can even be strengthened from `DTIME (T+1)` to `DTIME T`, since `T(n)+1 ≤ 2T(n)`. This observation does not apply to tape reduction's squared bound.

5. **Folding.** The fold coordinate for the paired layout in the sketch is

   \[
   \phi(z)=
   \begin{cases}
   z,&z\ge0,\\
   -z-1,&z<0.
   \end{cases}
   \]

   It is always nonnegative, and `φ(0)=φ(-1)=0`. Crossing between these two virtual cells changes only the component flag; it must not issue an actual left move from physical zero. An origin tag can detect this case, or a sentinel can implement it with a stated positive offset and constant extra moves. Arbitrary configurations need not satisfy the invariant: a predicate requiring nonnegative coordinates from every possible starting configuration would already fail at time zero for any machine with a work tape.

For the oblivious theorem, the following replacement strategy explains why the repaired time-constructibility hypothesis suffices. These are the machine-construction obligations still requiring formal implementation; the paragraph is not presented as a completed Lean proof.

- Choose the decider constant `a` from `DTIME T`, and a constructibility machine with bound `b*(T(n)+1)`. Simulate the latter with every nonblank input symbol replaced in the transition table by `false`, while preserving the boundary blanks. Its behavior on any input of length `n` is exactly its behavior on the all-false input of length `n`, so all its states, trajectories, emissions, and termination time depend only on `n`. Redirect its budget output to a work tape.
- Copy the real input in a fixed scan and rewind as needed. This costs a constant times `n+1`, which is absorbed because `n ≤ T(n)`. All physical motions of this phase depend only on length.
- Set the number of simulated original steps to `B(n)=(a+1)*(T(n)+1)`. It bounds both `a*T(n)` and `n+1`. Prepare a layout of length at most a fixed multiple of `B(n)` containing the original work tapes, a virtual copy of the input, all virtual head markers, and counter information. Preparing counters and the layout can be done within the quadratic allowance by length-dependent operations.
- Simulate **one step of the original decider** by a fixed number of complete sweeps, each of length at most a fixed multiple of `B(n)`. The virtual input head is included in the layout, and the real input head stays parked. Data may affect writes, simulated states, and virtual markers, but never the physical sweep path or its duration; after simulated halting, continue the same schedule idly. Fixed-duration block coding gives a binary machine without relying on the bare existential alphabet-reduction theorem to preserve obliviousness.
- Perform exactly `B(n)` such macrosteps and emit the stored one-bit answer at the end. Counter maintenance can be charged within the per-macrostep linear allowance. The total cost is at most a machine-dependent constant times `b*(T(n)+1)+B(n)^2`, hence at most a constant times `(T(n)+1)^2`; the full physical schedule and actual first halting time depend only on length.

An arbitrary constructibility witness cannot simply be assumed oblivious: add one scratch tape, move its head left or right depending on the first input bit, restore it, and then run any valid witness. The resulting witness still has cost at most `(b+2)*(T(n)+1)` and the same output, but has different trajectories at the first step. The constant-input substitution above removes that dependence without presupposing an oblivious-simulation theorem. Likewise, `one_work_tape_binary` is not a black-box linear-time preprocessing step: it supplies a quadratic bound, and applying another generic quadratic simulation to that bound would yield a fourth power. The direct sweep construction avoids that unjustified composition.

There is no loss of binary inputs from allowing an arbitrary bit embedding. When translating a particular AB machine, choose the embedding to name its designated data bits; a different embedding simply describes a different symbol encoding, and the input interpretation and output decoding use it consistently. Strings containing other alphabet symbols are not in the binary function's domain. Quantifying over every binary string is essential for the advertised language-class corollaries, which are not promise-problem claims.

The following adversarial instantiations were attempted. Outcomes follow from the definitions; finite executable spot-checks of the stationary-head example and the constant inequality were supplemental checks only, not substitutes for the arguments above.

| Case | Instantiation | Outcome |
|---|---|---|
| A1 | `T = fun _ => 0` in alphabet reduction, both one-work-tape results, and folding | Every computation premise fails already on the empty input, since an initialized machine has a live state. The padded conclusions do not make any premise satisfiable; these instances are vacuous. |
| A2 | `T = fun _ => 0` in oblivious simulation | Constructibility fails at length one because it requires `1 ≤ T(1)`, and `DTIME 0` is empty. No degenerate decider results. |
| A3 | `k = 0` in one-work-tape reduction and folding | Add an unused tape for the first theorem. In folding, retain zero work tapes: the nonnegativity quantifier is empty, and the original machine with identity embedding already supplies a witness after weakening the budget. |
| A4 | A one-element alphabet in alphabet reduction | No injection of the two Boolean values exists. This is appropriate: the interface requires two distinct represented data symbols; the separate blank is not a third input data symbol. |
| A5 | Two nonblank symbols in the alphabet-reduction sketch | A one-bit binary code cannot also reserve a binary blank code. All-physical-blank blocks supply the needed third logical value without an extra tape; this exposes finding 8 rather than refuting the theorem. |
| A6 | Identity as the first function, any fixed constant word as the second | With first budget `n+1` and second budget the word length plus one, the second budget is monotone and the composition bound dominates a direct constant-output machine, including on empty input. |
| A7 | A nonhalting machine with all heads stationary | It satisfies `Oblivious`, as a head-trajectory predicate should allow. It cannot witness the theorem's additional `DecidesInTime` conclusion. |
| A8 | A total stationary-head decider halting in one or two steps on equal-length inputs | This is the fully specified counterexample above. It refutes length-determined halting even with total correctness. |
| A9 | A fixed two-step halting time but different one-bit emission times | The represented heads can stay fixed while one branch emits on the first step and the other on the second. This isolates the output-schedule omission from the halting-time issue. |
| A10 | Virtual work-head path `0, -1, -2, -1, 0` | The corresponding fold coordinates are `0, 0, 1, 0, 0`. Component flips at the origin suffice; an actual move to physical minus one would violate the intended simulator invariant. |
| A11 | A first-step emission outside the bit embedding's range | No such run can satisfy the total embedded-output hypothesis on that input: the symbol remains in every later output prefix. Early emission does not break the decoding argument. |
| A12 | A constructibility witness with a first-bit-dependent scratch-head detour | The repaired budget still holds after increasing its constant, but the witness is not oblivious. Hence simply “running the witness” is not a correct first phase without the constant-input substitution or an equivalent argument. |
| A13 | The time bound `T(n)=n` in the oblivious theorem | The repaired constructibility predicate admits this bound, but the already adopted `DTIME` definition is empty at a bound vanishing on length zero. Thus this theorem instance is vacuous; a bound such as `n+1` is the applicable normalized example. This is a phase-1 convention, not a newly discovered contradiction. |
| A14 | Enlarged-alphabet inputs outside the folding embedding | Functional correctness is unrestricted there, but `NonnegativeHeads` still applies. Safe halting on any encountered invalid input symbol, with the same initialized fold invariant beforehand, satisfies the stronger universal head condition. |

The declared renderings therefore receive distinct dispositions: accept the embedded-alphabet formulation and same-tape alphabet reduction; accept one work tape as a narrower in-model analogue while rejecting identification with the merged model; accept initialized-run nonnegative work heads as the relevant in-model direction of folding; retain the represented-head obliviousness predicate but reject its claimed halting implication and qualify its output convention. The read-write-output and initialization obligations remain open, while deferring the oracle-tape polynomial bridge is acceptable for the present phase. The class-level corollaries establish the particular alphabet and one-work-tape conclusions stated, not unrestricted equivalence of all the source's models.

Notation used in this audit: `n` is input length; `t` is a step number; `τ` is an actual first halting time; `x` is an input string; `f,g` are string functions; `T,T₁,T₂` are natural-valued budgets; `e` is a symbol embedding; `Γ` is an alphabet of nonblank symbols; `k` is the number of work tapes; `j,z` are integer cell coordinates and `i` a tape index; `φ` is the displayed folding map; `B(n)` is the padded number of original steps in the replacement oblivious construction; `a,b` are its decider and constructibility constants; `c,c₀,c₁,c₂,C` are the locally specified constant factors; `d` is a polynomial degree; `|x|` denotes string length; and the displayed run/output operators are the given initialized-run and output operations. State names `start` and `delay` refer only to the counterexample. Big-O bounds hide constants depending on the fixed machines and alphabets, not on the input.

## ===== audits/phase2-reaudit-findings.md =====

# Phase 2, round 2: external re-audit findings

Audited the supplied `phase2-reaudit-bundle.md`, which identifies its amended sources as commit `85b66f2a`, against the attached Arora-Barak textbook: PDF pp. 42-45 (Claims 1.5/1.6/1.8 and Remark 1.7), pp. 51-52 (§1.6.1), and p. 60 (Exercise 1.5 and the palindrome lower-bound attribution). References below to bundle lines identify the supplied Markdown, not repository line numbers.

**Disposition: no blocker or major found in the supplied mathematical surface; four minor findings remain.** The corrected `oblivious_of_mem_DTIME` sketch is an adequate construction outline. The folding coordinate and initialization argument are repaired, but the literal alphabet description in `nonnegative_heads` remains incomplete. These are assessments of statements and outlines, not completed proofs or a blanket approval. The six phase-2 modules still contain 11 `sorry`s; the 12 supplied Lean modules contain 28. Lean and Lake are unavailable here. No attachments or source declarations were modified.

Historical byte identity is **not verified**: the packet includes the amended source and the earlier findings, but not the earlier source bytes or a commit diff. Current formulas agree with the earlier findings' mathematical restatements. That is weaker than the byte comparison requested in the brief.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Robustness/Bidirectional.lean` · module description and `nonnegative_heads` sketch (bundle 982, 1010-1025) | Folding uses `Γ × Γ`, with an origin tag added and preserved. | Here `Γ` excludes blank. A folded cell must hold two independent `Option Γ` payloads, including a symbol paired with blank; an outer physical blank does not supply these mixed cases. For `Γ = Bool`, `Option (Γ × Γ)` has five values, whereas two independently blank payloads require nine, even before distinguishing the origin. The corrected coordinate and safe-halt argument do work; the missing representation is a local repair, not a counterexample to the theorem. | Specify, for example, `Γ' = Bool × Option Γ × Option Γ`, with the Boolean component an origin flag. Decode an untouched physical `none` as two blanks with no origin flag; use `e γ = (false, some γ, none)`. Initialize `(true, none, none)` at each origin and preserve the flag on every update. Replace the literal `Γ × Γ` description. |
| 2 | minor | `Composition.lean` · design; `ClassP/DTIME.lean` · deviations; plan §7 (bundle 702-712, 1475-1481, 517) | The convention bridges are consistently recorded as waived. | The amended composition disclaimer and decision log explicitly waive the bridges, but `DTIME.lean` still calls the output simulation a “phase-2 obligation” with an “until then” restriction. Composition's closing “costs no generality” phrase is also broader than its demonstrated buffering of already append-only computations. These are residual prose inconsistencies; no exact AB step-count transfer was found. | Synchronize the `DTIME.lean` status with the waiver. Replace the last composition sentence with a precise statement that buffering and delayed emission are available within this model; the cross-model bridge remains unestablished. Narrow “all bounds carry existential constants” to the adapted source bounds, since internal exact bounds and lockstep lemmas are legitimate exceptions. |
| 3 | minor | `Robustness/AlphabetReduction.lean` · `alphabet_reduction` sketch (bundle 835-848) | Per-step overhead is `O(k · L)`, including zero work tapes. | The all-blank block repair is correct, and the bit embedding forces positive block length. But at `k = 0` the displayed overhead vanishes even though the simulator must still read, change state, move its input head, and possibly emit. The theorem's unrestricted existential constant has no such defect. | State `O((k + 1) · L)` or give the zero-work-tape case separately. Keep the all-`none` blank code and the theorem statement. |
| 4 | minor | `AroraBarakChapter1Plan.md` · §5, phase 3 (bundle 473-475) | Phase 2 supplies a “one-work-tape, four-symbol normal form.” | `one_work_tape_binary` supplies `FinTM Bool`, whose physical tape alphabet is `Option Bool`, with three symbols. The phase-2 declaration does not provide the stated four-symbol interface. | Call it the one-work-tape binary normal form. If phase 3 actually needs a fourth symbol, name the additional embedding step. |
| 5 | note | `Robustness/Oblivious.lean` · `Oblivious`, design, theorem scope; plan §7 | Round-1 findings 1, 6, and 7 are resolved. | The prose now agrees with the predicate: only input/work-head trajectories are constrained; equal first halting times and emission schedules do not follow. The theorem explicitly covers the first assertion of Exercise 1.5 in this model and promises neither one work tape nor the exercise's combined work/output tape. | No declaration change. Any downstream use of simultaneous obliviousness, a tape restriction, or length-determined halting must receive its own stated guarantee. |
| 6 | note | `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME`, steps 1-2 | Masking the witness's input preserves its budget output, and one copy scan suffices to obtain the length. | Induction identifies the masked run on a length-`n` input with the witness's run on `List.replicate n false`. `TimeConstructible` explicitly specifies that input and therefore supplies `(T n).bits`. During copying, write one unary marker per input symbol on a fresh tape; movements are independent of the copied bit. See the construction checks below. | No mathematical repair required. State these invariants explicitly when implementing the outline, including resetting the input head before the copy phase. |
| 7 | note | `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME`, steps 3-5 | The revised construction supports the quadratic bound and obliviousness. | `B n = (a + 1) · (T n + 1)` dominates both the decider budget and `n + 1`. A fixed number of full sweeps per original step costs `O(B n)`, hence `O((B n)^2)` over `B n` steps. Setup fits the same allowance. Padding continues all physical motions after simulated halting; fixed-duration coding and final emission prevent data-dependent timing. | Adequate as an outline. Formalize the fixed layout, sweep invariants, phase transitions, and trajectories of auxiliary heads; no additional hypothesis or theorem-strength change is needed. |
| 8 | note | `Robustness/SingleTape.lean` · both simulation statements | Round-1 findings 5 and 9 are resolved. | The in-model scope is explicit and agrees with AB's distinct merged model (PDF p. 43). Tagged `Option Γ` payloads represent marked blanks; boundary tags and the unused-tape treatment of `k = 0` address the earlier omissions. AB's palindrome separation is correctly attributed (PDF p. 60). | No change required for these resolutions. |
| 9 | note | `ClassP/ModelInvariance.lean` · module and `mem_P_iff_one_work_tape`; composition and binary corollaries | Round-1 findings 4 and 12 are resolved; the forward implication has no residual mathematical defect. | With `C' = c(C + 1)^2`, `c(C(n + 1)^d + 1)^2 ≤ C'(n + 1)^(2d)` at every length, including zero. The reverse implication forgets the tape-count conjunct. Alphabet reduction preserves time up to constants; reducing work tapes supplies only the polynomial-time conclusion. The `T + 1` alphabet padding is absorbable under the computation premise, which implies `T n ≥ 1`. | No theorem change. Use the explicit pointwise inequalities below rather than an eventual-asymptotic argument. |
| 10 | note | `Composition.lean`, robustness and context docstrings; plan §5/§7; `Oracle.lean` | The waiver's restriction holds in the supplied development, and round-1 findings 11 and 13 are addressed. | The source constants `3n`, `4 log(card Γ) · T`, `5kT²`, and `4T` are quoted as source bounds, not imported as exact formal bounds. Exact internal oracle simulations and output-length lemmas are independently in-model. Alphabet reduction documents its string-output generalization and omitted constructibility hypothesis. The query-tape bridge is deferred to Chapter 3 with an explicit outstanding obligation. | No new bridge required for this packet. Apply the prose synchronization in finding 2. This scan covers the supplied modules and plan, not unseen repository files. |
| 11 | note | Audit packet · historical statement comparison | The theorem formulas at `85b66f2a` are byte-identical to those at `2917a1b9`. | The amended 11 theorem formulas match the earlier report's descriptions of hypotheses, quantifiers, bounds, embeddings, and tape-count conclusions. However, the old source is absent; a mathematical restatement cannot establish byte identity. | Supply a diff or both revisions' declaration bytes for reproducible comparison. Do not report historical byte identity as independently certified by this audit. |

The changelog is dispositioned as follows.

| Round-1 finding | Round-2 disposition |
|---|---|
| 1: frozen heads and halting | Resolved; see finding 5. |
| 2: oblivious construction | Resolved at proof-outline level; see findings 6-7 and the checks below. |
| 3: convention discharge | The major discharge overclaim is removed and the waiver is explicit; residual minor documentation mismatch is finding 2. |
| 4: model invariance | Resolved; see finding 9. |
| 5: one-work-tape scope | Resolved; see finding 8. |
| 6: output schedule | Resolved; see finding 5. |
| 7: Exercise 1.5 coverage | Resolved; see finding 5. |
| 8: blank block code | The reserved-code defect is resolved. Finding 3 concerns a separate zero-work-tape overhead expression. |
| 9: marked blank and zero tapes | Resolved; see finding 8. |
| 10: folding coordinate and detectable origin | Coordinate, fold crossing, initialization, and invalid-input handling are repaired. Explicit payload/tag typing still needs the minor correction in finding 1. |
| 11: embedded inputs and generalization | Resolved; the added deviations match the declaration and the output-prefix argument. |
| 12: constant absorption | Retained and valid; see finding 9 and the calculations below. |
| 13: stale phase-2 bridge scope | The specified phase-2 paragraph and query-tape deferral are aligned with the decision log. Findings 2 and 4 identify other stale prose. |

The following checks answer the brief's specific questions and substantiate the two outline assessments. They remain mathematical construction arguments, not machine-checked Lean proofs.

**1. Constant-input substitution preserves the output.** Let `W` be the constructibility witness and `W₀` its input-masked version. For each transition, replace its input read `r` by `r.map (fun _ => false)`. This preserves blank reads. Fix an input `x` of length `n`, and put `x₀ = List.replicate n false`.

Relate the run of `W₀` on `x` to the run of `W` on `x₀` by equality of states, numerical input positions, work heads, work-tape contents, and accumulated output. The inputs themselves differ, so literal equality of the dependent configurations is not the claim.

1. At time zero, every listed component agrees by initialization.
2. If these components agree at time `t`, the input heads are at the same numerical position in equal-length strings. At either boundary both effective reads are `none`; at every interior position both effective reads are `some false`. Work reads also agree.
3. The transition tables therefore choose identical actions. Equal-length input boundaries give equal numerical next input positions, and the same actions preserve all other components. Halted states remain paired by absorption.
4. Induction proves this relation for every time, including equality of accumulated outputs and of first halting times.

The actual witness specification, instantiated at `x₀`, is

\[
W.\mathrm{ComputesInTime}\bigl(x_0,(T(n)).\mathrm{bits},b(T(n)+1)\bigr).
\]

Consequently the masked machine produces that same output by that budget. The specification is universal over **every binary input**, so this instantiation needs no additional promise. Redirecting the emissions into a fresh work tape preserves the simulated witness by projection and costs a fixed overhead. The extra tape's trajectory is also length-dependent, since the witness's emissions now are. Merely ignoring the witness's output, or assuming that its budget alone determines its answer, would not suffice; the run relation above is the required justification.

**2. The copy scan also supplies length information.** First restore the real input head to the start of the input; the witness's ending position is length-dependent, and returning over the bounded input costs `O(n + 1)`. During the copy scan, move the input and copy heads once per logical input cell. On a separate fresh tape, append one unary marker on each of these iterations. Use the same motions for `false` and `true`, and stop on the right boundary blank. Thus the third tape contains a delimited unary segment of length `n`; the empty-input case gives a segment of length zero. Rewinding these tapes depends only on their segment lengths.

The copied bits affect writes but not motion. Unary length is already sufficient for layout construction; any later conversion to binary may use a length-dependent routine within the quadratic preparation allowance. A variable-time arithmetic routine is harmless for obliviousness here when its entire input depends only on `n`; the time bound must still be charged. This avoids silently assuming that the constructibility witness returned `n` as well as `T(n)`.

**3. Fixed layout, setup cost, and the quadratic bound.** The chosen budget satisfies

\[
\begin{aligned}
B(n)&=(a+1)(T(n)+1)=aT(n)+a+T(n)+1>aT(n),\\
B(n)&\ge T(n)+1\ge n+1.
\end{aligned}
\]

Allocate the original work-tape coordinates from `-B(n)` to `B(n)`, a virtual input segment with both boundaries, the virtual head markers, and counters. The original machine has a fixed finite number of tapes, so the layout occupies `O(B(n))` cells over a fixed finite tagged alphabet. A source head moves at most one cell per original step, so all relevant coordinates lie in this layout. Boundary tags must be structural fields preserved by simulation writes.

Preparing the layout is possible within `O(B(n)^2)`: compute the binary integer `B(n)` from the captured budget using constant multiplication, and generate its unary-sized allocation using a decrementing counter. Even allowing `O(B(n))` work per generated cell fits the stated allowance. Control scans in this phase depend on the budget and unary length, not on the copied input bits; copying payloads into fixed locations must follow that same rule.

One fixed collection of full sweeps reads marked symbols, determines the source transition in finite control, and updates payloads and head markers. Use additional full sweeps or fixed local coding phases where needed, rather than an early stop at a data-dependent marker. Keep every represented physical head, including counters and other auxiliary tapes, on a length-dependent schedule. After source halting, run the same sweeps with an inactive simulated state. Counter maintenance costs at most `O(B(n))` per macrostep. Simulate `B(n)` original steps, not `B(n)` steps of an already quadratic simulator.

Fixed-duration coding of this fixed finite alphabet retains the schedule over `Bool`. Before the final step, simulated emissions are buffered in finite control: the decider premise and append-only output imply there is exactly one final answer bit and no competing extra emissions. Emit it once, then halt at the common finishing time. Heads stay fixed thereafter, so the definition's quantification over all later times is satisfied too.

For a fixed construction-overhead constant `C`, its time is bounded by

\[
\begin{aligned}
\mathrm{time}(n)
&\le C\bigl(b(T(n)+1)+(n+1)+B(n)^2+1\bigr)\\
&\le C\bigl(b+2+(a+1)^2\bigr)(T(n)+1)^2.
\end{aligned}
\]

The second inequality uses `n ≤ T(n)` and `1 ≤ T(n)+1`, so it holds at every input length. Both the schedule and phase-ending times depend only on length. No quartic composition or assumption that an arbitrary constructibility witness is already oblivious remains.

**4. Fold initialization and the representation repair.** Use the concrete enlarged alphabet from finding 1,

\[
\Gamma'=\mathrm{Bool}\times\mathrm{Option}(\Gamma)\times\mathrm{Option}(\Gamma),
\qquad e(\gamma)=(\mathrm{false},\mathrm{some}\,\gamma,\mathrm{none}).
\]

The embedding is injective by its first payload component. An untouched physical blank decodes to `(false, none, none)`. An explicit tagged record contains an origin Boolean and two independent source-cell contents. This also makes sense for an empty `Γ`.

All work heads start at coordinate zero. Introduce one fresh initialization state whose single action writes `(true, none, none)` on **each** work tape, moves every head by zero, emits nothing, and enters the source's initial state with all component flags positive. A multi-tape action has a write/move component for every tape, so these writes are simultaneous; their cost is one transition, independent of input length. For zero tapes the write tuple is empty. No coordinate inspection or preliminary simulated activity is needed.

After initialization, physical position `p ≥ 0` stores source cells `p` and `-p-1`; its origin field is true exactly when `p = 0`. A write updates only the active payload and preserves the other payload and the origin flag. Thus a source symbol cannot manufacture or erase an origin tag.

The physical movement rules are:

| Active component | Source move | Physical movement / component change |
|---|---|---|
| Positive | right | Move right; retain positive component. |
| Positive | left, away from origin | Move left; retain positive component. |
| Positive | left, at origin | Stay; switch to negative component. |
| Negative | left | Move right; retain negative component. |
| Negative | right, away from origin | Move left; retain negative component. |
| Negative | right, at origin | Stay; switch to positive component. |
| Either | stay | Stay; retain component. |

Each row realizes the proposed coordinate

\[
\phi(z)=\begin{cases}z&z\ge0,\\-z-1&z<0,\end{cases}
\quad\text{with}\quad \phi(0)=\phi(-1)=0.
\]

An actual left move is made only from a strictly positive physical coordinate. Induction therefore gives nonnegative positions at every time, including initialization. On encountering a nonblank input symbol outside `e`'s range, use a stationary halting action before any simulated transition. Earlier activity preserves the same invariant, and subsequent halted configurations are fixed. Thus the universal `NonnegativeHeads` quantifier, including malformed enlarged-alphabet inputs, is covered. This safety argument does not require a source computation premise on malformed inputs.

The initialized tag and the two payloads are the missing typing details, not a new asymptotic construction. With them, the folding outline supports constant slowdown and the same number of work tapes.

**5. Waiver scan and polynomial corollary.** The supplied source quotes AB's exact numerical constants only while identifying its source statements or explicitly replacing their constants. In particular, the palindrome sketch derives its own padded in-model count; the oracle lockstep theorems compare machines within the shared `Cfg`/`Action` semantics. Neither transfers an AB step count across the waived convention bridges. The restriction therefore holds for the supplied files, subject to the documentation cleanup in finding 2. The restriction is not itself a proof of a semantic bridge.

For `mem_P_iff_one_work_tape`, `n + 1 ≥ 1` gives

\[
\begin{aligned}
C(n+1)^d+1 &\le (C+1)(n+1)^d,\\
c\bigl(C(n+1)^d+1\bigr)^2
&\le c(C+1)^2(n+1)^{2d}.
\end{aligned}
\]

Choose `C' = c(C + 1)^2` and degree `2d`, and apply time-bound monotonicity to the simulator. This handles `n = 0` and `d = 0` as written. No simultaneous obliviousness claim is used in this implication.

For the alphabet claim, instantiate any `DecidesInTimeVia` premise at `List.replicate n false`. If `T n = 0`, it contradicts `not_computesInTime_zero`; hence `T n ≥ 1` and

\[
c(T(n)+1)\le 2cT(n).
\]

Thus the module's alphabet-invariance assertion is consistent with the delivered padded theorem and existing monotonicity interface. It does not imply fixed-`DTIME T` invariance under the quadratic tape reduction.

Finally, the other retained estimates need no new repair: composition uses output length at most `T₁(n)` and monotonicity of `T₂`; the binary one-work-tape corollary absorbs the additive one because `(T(n)+1)^2 ≥ 1`; and the polynomial alphabet corollary uses `(n+1)^d ≤ 2^d(n^d+1)` pointwise. The string-output generalization of alphabet reduction remains supported by append-only output prefixes, including early emissions.

Notation glossary: `n` is input length; `t` is a step number; `x` is an input and `x₀` its all-false counterpart; `W` is the constructibility witness and `W₀` its input-masked variant; `T`, `T₁`, and `T₂` are time bounds; `a` and `b` are the decider and constructibility constants; `B(n)=(a+1)(T(n)+1)` is the simulation budget; `k` is the work-tape count and `L` in finding 3 is the binary block length. `Γ` is the source nonblank alphabet, `Γ'` the enlarged nonblank alphabet, and `e` the symbol embedding; `γ` is a source symbol, `z` a virtual coordinate, `p` a physical coordinate, and `φ` the folding map. `r` is an optional input read. `C` denotes a locally chosen fixed constant (construction overhead or the polynomial-decider coefficient), `c` a simulation constant, `d` a polynomial degree, and `C'=c(C+1)^2` the resulting polynomial coefficient. `Option` includes the blank value `none`; `some` marks an actual payload; `bits` denotes the specified binary representation. Big-O constants may depend on the fixed machines and alphabets, never on the input.

## ===== briefs/epoch2-batchA.md =====

# Fill campaign — Epoch 2, Batch A: the guarded-composition core

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. Twelve of the
21 audited sorries were proved in epoch 1 (externally audited clean —
`audits/epoch1-findings.md`); nine remain. This batch delivers the two
load-bearing composition theorems: **partial (guarded) sequential composition**
`exists_comp_partial` — three already-proved theorems cite it — and the timed
total-function composition `computesFunInTime_comp`, which shares its core
construction. Fill `exists_comp_partial` first, then reuse its machinery for
`computesFunInTime_comp` with time accounting on top.

Epoch 1 left you a genuine head start, but the epoch-1 audit (finding 11)
delimited it precisely — read this before designing anything:

- `TCSlib/Complexity/TuringMachine/Simulation.lean` (public, shared) has the
  emission chains, control actions, the audited input-head rewind
  (`rewind_scan`, `rewind_from_any`), and the disjoint tape-block embeddings
  `leftCfg`/`rightCfg` with lockstep `apply`/`step`/`run` lemmas.
- **Those embeddings are NOT yet a buffered-composition simulator**: they
  preserve the *native* input tape and pass emissions to the *real* output.
  Your construction additionally needs (a) a **buffer representation** — phase
  one must redirect `M₁`'s emissions to a work tape while the real output stays
  empty — and (b) a **virtual-input relation**: phase two serves `M₂`'s input
  reads from the buffer with clamped boundary semantics mirroring
  `Turing.moveInputPos`. Neither invariant exists yet; they are the heart of
  this batch.
- The audited boundary details (phase-4 audit, finding 3; epoch-1 findings,
  `exists_comp_partial` row): after phase one the buffer head rests on the
  blank immediately *right* of the written word, so the rewind's first left
  move must be unconditional (testing before moving stops at the wrong end);
  for an **empty** intermediate word the simulation starts with the
  right-boundary tag already set, the left boundary one inward move away; at a
  boundary, supply a blank read and suppress outward moves, with *which*
  boundary known from the direction of arrival, tracked in the state.
- The composite must not have completed outputs during administrative
  transitions (rewind/dispatch): both directions of the iff concern completed
  outputs, so administrative states stay live (the epoch-1 `condTM` handled
  this with a live administrative state after the simulated halt — mirror it).
- Useful proved lemmas in `Finite.lean`: `computesInTime_iff` (space-free
  unfolding), `Computes.exists_computesInTime_iff`,
  `ComputesInTime.output_unique`, `ComputesInTime.mono`, and the raw-layer
  `MultiTapeTM.output_length_le` / `output_prefix` (each step emits at most
  one symbol; output only grows) — the last two drive the buffer invariant
  and `comp`'s length bound.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `24687122`** — verify
  `git rev-parse HEAD` after checkout. Create a local branch `fill/epoch2-A`
  and commit your work there. GitHub write access is not available from this
  environment; **do not attempt to push or open a PR.**
- **Deliverable: a single zip archive** containing, at minimum:
  1. `REPORT.md` — the full report per the checklist below.
  2. The complete modified source files at their repository paths
     (e.g. `TCSlib/Complexity/TuringMachine/Composition.lean`).
  3. `epoch2-A.patch` — `git format-patch` output of your commits against
     `24687122` (`git format-patch 24687122 --stdout > epoch2-A.patch`).
  4. `epoch2-A.bundle` — `git bundle create epoch2-A.bundle 24687122..fill/epoch2-A`
     (or the full branch).
  5. `final-sweep.log` — the complete output of the final full sweep.
  6. `axioms.log` — `#print axioms` output for each filled theorem, produced
     via a scratch file *outside* the repository (imports the owned modules,
     one `#print axioms` per target; run with the same `LEAN_PATH` the check
     script assembles). Expected: `[propext, Classical.choice, Quot.sound]`
     and **no `sorryAx`** — these are self-contained constructions.
  7. `SHA256SUMS` — a hash manifest of every file in the zip.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5 (campaign + ground
  rules), `audits/epoch1-findings.md` (finding 11 and the
  `exists_comp_partial` / `computesFunInTime_comp` rows), and the docstring
  sketches on both targets.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Composition.lean` (both targets live here)
- `TCSlib/Complexity/TuringMachine/Simulation.lean` (shared gadget layer)

Placement rules: genuinely reusable infrastructure (the buffer representation,
the virtual-input serving relation and its clamping invariants) belongs in
`Simulation.lean`, **public with docstrings** — it precedes `Composition.lean`
in the import order, which also resolves Lean's no-forward-reference
constraint (epoch-1 audit, finding 11: helpers must precede their use).
Proof-specific privates may live in `Composition.lean` but must be defined
*above* the theorem that uses them. Keep `Composition.lean` under ~1000 lines
(policy §1); prefer moving generic layers to `Simulation.lean` over growing it.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned. Setup
  once from the repo root: `lake exe cache get` (several GB on first run).
- **Never run `lake build`** (banned on this branch; plan decision log). The
  repo's `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local
  interactive session; for this cloud task the maintainer-designated
  verification path is `scripts/lean_check_tree.sh` — note it was
  **strengthened after an audit finding**: it now fails on a nonzero `lean`
  exit, on `error:` diagnostics, or on a missing fresh `.olean`. Sweep recipe
  (subshell, so a failure fails the whole run):
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Bootstrap once on a fresh clone with that sweep; iterate per module
  (`Simulation` before `Composition`, then everything after `Composition` in
  the order list); finish with the full sweep. Pass = sweep exits 0, zero
  `error:` lines, and `declaration uses 'sorry'` warnings **only** at the
  out-of-scope declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only the two owned files. Every new declaration
   (public in `Simulation.lean`, or private in `Composition.lean`) is listed in
   `REPORT.md` — new public declarations become audited surface and will be
   blind-restated next round, so write real docstrings. If a helper belongs in
   another shared file (`Finite.lean`; vendored files are **frozen**): add a
   `private` copy in an owned file and record the request under "Requested
   shared lemmas".
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or attribution of any existing declaration. Docstring
   proof-sketch paragraphs may gain an appended implementation note; flag such
   updates in `REPORT.md`.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction under
   "Escalations", and continue with the other target.
4. Do not remove, weaken, or fill any sorry outside your target list.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep
   their docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets (in this order)

### 1. `Turing.FinTM.exists_comp_partial`

`∀ x w, (∃ t, M(x) ↓ w) ↔ ∃ y, (∃ t, M₁(x) ↓ y) ∧ (∃ t, M₂(y) ↓ w)` — untimed,
no totality hypotheses. Suggested architecture (the docstring sketch, plus the
audit refinements above): tapes `M₁.k + 1 + M₂.k` (buffer in the middle);
states = phase-1 controller (`M₁`'s state, lockstep, emissions redirected to
the buffer: write, move right) ⊕ live administrative rewind states ⊕ phase-2
simulator (`M₂`'s state × virtual-boundary tag). Phase-1 invariant: real
output empty, buffer holds exactly `M₁`'s emitted-so-far output contiguously
from cell 0 (use `output_prefix`/`output_length_le` style reasoning), `M₂`
block blank. Rewind per the audited procedure. Phase-2 invariant: the virtual
input relation — `M₂`'s configuration on input `y` corresponds to the
composite's, with `M₂`-input position `v` matched to the buffer head at cell
`v − 1`, boundary reads blank, outward moves suppressed. Both iff directions
by run correspondence; `output_unique` collapses the intermediate `y`; if
`M₁` diverges the composite never leaves phase 1, and if `M₂` diverges on the
unique `y` the composite never halts (administrative states are live).

### 2. `Turing.FinTM.computesFunInTime_comp`

Same construction, now with the time ledger (docstring sketch + epoch-1
findings row): phase one costs a constant per `M₁` step (≤ `T₁ n` steps);
the rewind costs at most the buffer length + 2 ≤ `T₁ n + 2` (by
`output_length_le`, `|f x| ≤ T₁ |x|`); phase two costs a constant per `M₂`
step, and `M₂` halts within `T₂ |f x| ≤ T₂ (T₁ n)` — **this is where
`Monotone T₂` is genuinely used**; bookkeeping absorbs into `c`. Conclusion:
`c * (T₁ n + T₂ (T₁ n) + 1)`. If you build 1 first, this is largely a timed
re-run of the same invariants; design them with step counts from the start.

## Out-of-scope sorries you will see (leave every one untouched)

Elsewhere only (your two files carry no other sorries): `alphabet_reduction`,
`one_work_tape`, `nonnegative_heads`, `oblivious_of_mem_DTIME` (Robustness/);
`exists_effectiveMachineCode` (Encoding.lean); `universal`, `timed_universal`
(Universal.lean). After your batch, exactly these 7 sorry warnings remain.

## REPORT.md checklist

- [ ] Targets filled (2), with how each proof relates to its sketch.
- [ ] New declarations: public (Simulation.lean — full list with one-line
      statements) and private, for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Docstring appendices added — or "none".
- [ ] Verification evidence: final full-sweep log reference (attached file),
      axiom log reference, confirmation of zero `error:` lines and the exact
      7 remaining sorry warnings.
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin); core
  `Nat.pow_pos` (not mathlib `pow_pos`); `dite_eq_right/left` don't exist —
  `split <;> simp <;> omega`; after `cases hs : cfg.state` insert `dsimp only`
  to iota-reduce; avoid bare `simp` when hypotheses use folded forms
  (`initCfg` is `@[simp]`) — prefer targeted `simp only`; `ring` needs
  `import Mathlib.Tactic.Ring`; `omega` can't see `(⟨e, h⟩ : Fin _).val` or
  un-beta-reduced lambdas — normalize with `show`/`simp only` first;
  `Nat.find` under classical needs `classical` + explicit `(p := …)`;
  SignType lemmas: `SignType.coe_one`, `neg_eq_neg_one`, `coe_neg_one`,
  `pos_eq_one`, and `SignType.zero_eq_zero` with `moveInputPos_zero`.
- Worked exemplars of the invariant style, in-repo and proved: `condTM` +
  `controlCfg_step`/`controlCfg_run`/`condTM_start` (Composition.lean — the
  closest relative of your construction: register capture, live
  administrative states, `Nat.find` first-halting-time, `rewind_from_any`,
  then branch lockstep), `pairDiagTM` (Encoding.lean, multi-phase with
  rewind), `counterTM` (TimeConstructible.lean, work-tape invariants via a
  `counterTape` shape function), `palTM` (Examples.lean, two-head phases).
- Tape-index bookkeeping: use `Fin.addCases` consistently (see
  `leftCfg`/`rightCfg` in Simulation.lean); define the three-block partition
  once and prove its projection lemmas before anything else.

## ===== briefs/epoch2-batchB.md =====

# Fill campaign — Epoch 2, Batch B: one work tape (the heavyweight)

## Context

You are filling one Lean 4 proof in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1:
`Turing.FinTM.one_work_tape` — [AB09, Claim 1.6] rendered in this model as
"one work tape suffices, quadratically". This is the single heaviest
construction of the whole campaign (the Isabelle AFP `Cook_Levin` entry sank
most of its effort into exactly this simulation), and it is deliberately a
solo batch: take the time it needs. Twelve of 21 audited sorries are already
proved and audited; the already-proved `one_work_tape_binary` directly below
your target chains it with `alphabet_reduction`, so your theorem is
load-bearing for the universal machine and Theorem 1.10.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `24687122`** — verify with
  `git rev-parse HEAD` after checkout. Create a local branch `fill/epoch2-B`
  and commit your work there. GitHub write access is not available from this
  environment; **do not attempt to push or open a PR.**
- **Deliverable: a single zip archive** containing, at minimum:
  1. `REPORT.md` — the full report per the checklist below.
  2. The complete modified source file at its repository path
     (`TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean`).
  3. `epoch2-B.patch` — `git format-patch 24687122 --stdout > epoch2-B.patch`.
  4. `epoch2-B.bundle` — `git bundle create epoch2-B.bundle 24687122..fill/epoch2-B`.
  5. `final-sweep.log` — the complete output of the final full sweep.
  6. `axioms.log` — `#print axioms Turing.FinTM.one_work_tape` (and, as a
     regression check, `#print axioms Turing.FinTM.one_work_tape_binary`),
     produced via a scratch file *outside* the repository with the check
     script's `LEAN_PATH`. Expected: `[propext, Classical.choice, Quot.sound]`,
     **no `sorryAx`** for `one_work_tape`; `one_work_tape_binary` will still
     show `sorryAx` only if `alphabet_reduction` (another batch) is unfilled
     in your tree — say so in the report.
  7. `SHA256SUMS` — a hash manifest of every file in the zip.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5,
  `audits/phase2-findings.md` and `audits/phase2-reaudit-findings.md` (the
  audited construction: this target's sketch was *corrected* by that audit —
  the tagged-payload alphabet is the mandated design), and the docstring
  sketch on the target.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean`

`one_work_tape_binary`, in the same file, is **proved — do not touch it**.
All helpers are `private` in this file, defined *above* the target theorem
(Lean has no forward references). If the file approaches ~1000 lines
(policy §1), prefer tighter decomposition over splitting: a split would
change shared structure, which is not this batch's call — escalate in
`REPORT.md` instead if you believe one is needed.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once from the repo root: `lake exe cache get` (several GB).
- **Never run `lake build`** (banned; plan decision log). The repo's
  `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; the maintainer-designated verification path is
  `scripts/lean_check_tree.sh` (strengthened after an audit finding: fails on
  nonzero `lean` exit, `error:` diagnostics, or a missing fresh `.olean`).
  Sweep recipe:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Bootstrap once with that sweep; iterate on your module, then re-check
  everything after it in the order list; finish with the full sweep. Pass =
  sweep exits 0, zero `error:` lines, sorry warnings only at the out-of-scope
  list below.

## Ground rules (binding)

1. **File ownership.** Modify only the owned file; helpers `private`; list
   every new declaration in `REPORT.md` (the next audit round restates them).
   Needed lemmas that belong in shared files (`Finite.lean`,
   `Simulation.lean`; vendored files **frozen**): add a `private` copy and
   record the request under "Requested shared lemmas".
2. **Statement freeze.** No change to any existing declaration's name,
   signature, statement, hypotheses, or attribution. Docstring sketch
   paragraphs may gain an appended implementation note; flag it.
3. **Escalation.** If the target appears false or unprovable as stated, STOP,
   do not alter the statement, and record the obstruction under "Escalations".
4. No other sorry is touched. 5. Sketches stay. 6. Precise imports; keep the
   `set_option` headers.

## The target

```
theorem one_work_tape {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) ^ 2
```

The audited construction (docstring sketch + phase-2 findings, binding
corrections included):

- **`k = 0` case first and separately**: simulate `M` directly with one unused
  work tape (a lockstep embedding — `Turing.FinTM.leftCfg`-style reasoning
  from `Simulation.lean`, or a bespoke one-step commutation; no sweeps).
- **`k ≥ 1`**: the single work tape stores the `k` tapes interleaved — cell
  `j·k + i` of the simulated layout holds cell `j` of tape `i`, centered at
  `0` in both directions.
- **Alphabet (audit-mandated form)**: cells carry a *tagged payload*
  `Option Γ` — a marked **blank** must be representable, which a bare
  `Γ × flag` product misses (phase-2 audit, round 1) — together with a
  "head here" flag and zone-boundary tags; `Γ` embeds via `e` as an unmarked
  non-blank payload. Concretely something like
  `Γ' := Option Γ ⊕ (marker structure)` or a product with `Bool` flags —
  design it, but the *tagged `Option Γ` payload* requirement is fixed.
- **Simulated step = two sweeps**: left-to-right across the visited zone
  recording the `k` marked (head-here) symbols in the state; compute `M`'s
  transition from them; right-to-left updating the marked cells and moving
  the marks. Zone boundaries grow by at most one block per simulated step:
  after `t` steps the visited zone spans `O(k · (t + 1))` cells, so one
  simulated step costs `O(k · (T n + 1))` and the total is `c · (T n + 1)²`.
- **Input and output pass through unchanged**: `M'` reads the true input tape
  (via `e` on the embedded symbols — the hypothesis is `ComputesFunInTimeVia`,
  and so is the conclusion: inputs are `x.map e`-images) and emits `M`'s
  emissions mapped through `e`.
- The constant `c` is existential — be generous; no exact-step-count transfer
  from [AB09] is ever claimed (the `5kT²` of the book is *not* imported).

Proved in-repo exemplars of the invariant style (all epoch-1, audited):
`condTM`/`controlCfg_run`/`condTM_start` in `Composition.lean` (phase
decomposition, live administrative states), `counterTM` in
`TimeConstructible.lean` (work-tape shape functions like `counterTape` — you
will want an analogous "interleaved zone" shape function), `palTM` in
`Examples.lean` (two-head coordination), and the lockstep suites in
`Simulation.lean` and `StateRenaming.lean`. Expect the zone invariant to be
the real work: state it as a configuration-shape function (simulated tapes ↦
composite work tape + head positions + zone bounds) and prove one macro-step
lemma (one simulated step = one bounded burst of composite steps preserving
the shape), then induct.

## Out-of-scope sorries you will see (leave every one untouched)

`computesFunInTime_comp`, `exists_comp_partial` (Composition.lean);
`alphabet_reduction` (AlphabetReduction.lean); `nonnegative_heads`
(Bidirectional.lean); `oblivious_of_mem_DTIME` (Oblivious.lean);
`exists_effectiveMachineCode` (Encoding.lean); `universal`, `timed_universal`
(Universal.lean). After your batch, exactly these 8 sorry warnings remain.

## REPORT.md checklist

- [ ] Target filled, with how the proof relates to the sketch (and the `k = 0`
      path taken).
- [ ] New private declarations listed, for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Docstring appendices — or "none".
- [ ] Verification evidence: final sweep log attached, axiom log attached,
      zero `error:` lines, the exact 8 remaining sorry warnings.
- [ ] Diff touches only `SingleTape.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `update_noteq`); core `Nat.pow_pos`;
  `dite_eq_right/left` don't exist — `split <;> simp <;> omega`; after
  `cases hs : cfg.state` insert `dsimp only`; avoid bare `simp` against
  folded hypotheses (`initCfg` is `@[simp]`) — targeted `simp only`; `ring`
  needs `import Mathlib.Tactic.Ring`; `omega` can't see `Fin.val ⟨e, h⟩` or
  un-beta-reduced lambdas — normalize first; SignType names:
  `SignType.coe_one`, `neg_eq_neg_one`, `coe_neg_one`, `pos_eq_one`,
  `zero_eq_zero`; `moveInputPos_zero`, `moveInputPos_pos_of_ne_right`,
  `moveInputPos_neg_of_ne_left`, `moveInputPos_neg_val` (Simulation.lean).
- Work tapes are ℤ-indexed `Option Γ'` functions updated via
  `Function.update`; blanks are `none`. `Cfg.ext` proves configuration
  equality field by field; `Cfg.ext_zero_tapes` for `k = 0` machines.
- `ComputesFunInTimeVia e f T` means: on every input `x.map e`, halt within
  `T x.length` with output `(f x).map e` — mind that the *length* in the
  bound is of `x`, and `(x.map e).length = x.length` (`List.length_map`).

## ===== briefs/epoch2-batchC.md =====

# Fill campaign — Epoch 2, Batch C: the remaining tape simulations

## Context

You are filling two Lean 4 proofs in **tcslib**'s formalization of
Arora–Barak, *Computational Complexity: A Modern Approach* (2009), Chapter 1:
`Turing.FinTM.nonnegative_heads` — [AB09, Claim 1.8] rendered as
"unidirectional (nonnegative) work-head use suffices" — and
`Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5], binary alphabet
suffices with constant-factor slowdown. Do **`nonnegative_heads` first**: it
is a near-lockstep folding simulation (one simulated step ↦ boundedly many
composite steps, no growing sweeps) and warms up the machinery;
`alphabet_reduction` is the first genuine macro-step (block-encoding)
simulation. Both sketches were corrected and certified by the phase-2
external audit — the corrected designs below are binding.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `24687122`** — verify with
  `git rev-parse HEAD` after checkout. Create a local branch `fill/epoch2-C`
  and commit your work there. GitHub write access is not available from this
  environment; **do not attempt to push or open a PR.**
- **Deliverable: a single zip archive** containing, at minimum:
  1. `REPORT.md` — the full report per the checklist below.
  2. The complete modified source files at their repository paths.
  3. `epoch2-C.patch` — `git format-patch 24687122 --stdout > epoch2-C.patch`.
  4. `epoch2-C.bundle` — `git bundle create epoch2-C.bundle 24687122..fill/epoch2-C`.
  5. `final-sweep.log` — the complete output of the final full sweep.
  6. `axioms.log` — `#print axioms` for both filled theorems (and, as a
     regression check, `Turing.FinTM.one_work_tape_binary`, which chains
     `alphabet_reduction`), via a scratch file *outside* the repository with
     the check script's `LEAN_PATH`. Expected for your two:
     `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
  7. `SHA256SUMS` — a hash manifest of every file in the zip.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5,
  `audits/phase2-findings.md` and `audits/phase2-reaudit-findings.md` (the
  corrected fold movement table and block-encoding design live there), and
  the docstring sketches on both targets.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean`
  (`nonnegative_heads`; the `NonnegativeHeads` definition is **frozen**)
- `TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean`
  (`alphabet_reduction`)

All helpers are `private`, per file, defined *above* the theorem that uses
them (Lean has no forward references). Needed lemmas that belong in shared
files (`Finite.lean`, `Simulation.lean`, `StateRenaming.lean`; vendored files
**frozen**): add a `private` copy and record the request under "Requested
shared lemmas" in `REPORT.md`.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once from the repo root: `lake exe cache get` (several GB).
- **Never run `lake build`** (banned; plan decision log). The repo's
  `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; the maintainer-designated verification path is
  `scripts/lean_check_tree.sh` (strengthened: fails on nonzero `lean` exit,
  `error:` diagnostics, or a missing fresh `.olean`). Sweep recipe:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Bootstrap once with that sweep; iterate on your modules (AlphabetReduction
  precedes SingleTape in the order; re-check everything after your earliest
  touched module); finish with the full sweep. Pass = sweep exits 0, zero
  `error:` lines, sorry warnings only at the out-of-scope list below.

## Ground rules (binding)

1. **File ownership** as above; every new declaration listed in `REPORT.md`
   (the next audit round restates them).
2. **Statement freeze.** No change to any existing declaration's name,
   signature, statement, hypotheses, or attribution — including
   `NonnegativeHeads` itself. Docstring sketch paragraphs may gain an
   appended implementation note; flag it.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, record the obstruction under "Escalations", and continue with
   the other target.
4. No other sorry is touched. 5. Sketches stay. 6. Precise imports; keep the
   `set_option` headers.

## Targets (in this order)

### 1. `Turing.FinTM.nonnegative_heads` (Bidirectional.lean)

Conclusion shape: `∃ Γ' … (e : Γ ↪ Γ') M' c, M'.NonnegativeHeads ∧
M'.k = M.k ∧ M'.ComputesFunInTimeVia e f (fun n => c * (T n + 1))`.

The audited construction (phase-2 findings; the corrections are binding):

- **Fold each work tape at the origin**: simulated cell `z` lives at folded
  coordinate `φ z = if 0 ≤ z then z else -z - 1`; each nonnegative folded
  cell carries **both** simulated cells `z` and `-z-1`.
- **Alphabet (audit-corrected)**: `Γ' = Bool × Option Γ × Option Γ` — an
  origin/track tag plus the two *independent* `Option Γ` payloads (marked
  blanks must be representable on each track separately). `Γ` embeds via `e`
  into the appropriate track with the other blank. The phase-2 round-2
  finding fixed this alphabet exactly; do not substitute a product without
  the `Option`s.
- **Movement table**: the simulated head's sign determines which track is
  active; crossing the fold (a move between `z = 0` and `z = -1`) becomes a
  **stationary** composite move that toggles the track tag at folded cell
  `0` — the phase-2 findings contain the full worked movement table
  (direction × track): mirror it case by case.
- **Detectable origin**: folded cell `0` is tagged so the simulator knows
  when it stands at the fold (the `Bool` component).
- **Safe halting off the embedding** (phase-2 audit, finding 10 / case A14):
  on input symbols outside `e`'s image — where `ComputesFunInTimeVia`
  promises nothing but `NonnegativeHeads` still quantifies — the simulator
  halts immediately on first contact, preserving nonnegativity. Check the
  `NonnegativeHeads` definition in the file and make sure your machine
  satisfies it on **every** input, not only embedded ones.
- Near-lockstep: constant composite steps per simulated step, hence the
  linear `c * (T n + 1)` bound.

In-repo precedent for the "coordinate-transported configuration" proof shape:
`MultiTapeTM.relabelState_step`/`_runFrom_init` in `StateRenaming.lean`
(state coordinate) and `Cfg.embedOracle_*` in `Oracle.lean` (tape extension)
— yours transports the *tape* coordinate through `φ` with a two-track
payload; write the configuration-shape function first
(simulated `Cfg` ↦ folded `Cfg`), prove one step-commutation lemma by the
movement table, then induct.

### 2. `Turing.FinTM.alphabet_reduction` (AlphabetReduction.lean)

Statement: given `e : Bool ↪ Γ` and `M : FinTM Γ` with
`M.ComputesFunInTimeVia e f T`, produce `M' : FinTM Bool` with
`M'.k = M.k` and `M'.ComputesFunInTime f (fun n => c * (T n + 1))`.

The audited construction (phase-2 findings):

- **Fixed-width blocks**: choose `L` with `2^L ≥ |Γ| + 1` (or any fixed-width
  scheme); each simulated `Option Γ` cell becomes an `L`-cell block of
  `Option Bool` on the corresponding work tape (`k` is preserved — block per
  tape, no merging).
- **All-blank block = logical blank** (audit-corrected): the encoding of the
  simulated blank is the block of `L` physical blanks, so untouched tape
  regions are automatically correctly encoded — do not use a nonblank code
  for blank.
- **Macro-step**: to simulate one step of `M`, sweep each work-tape block
  (`L` steps) to read the block into the state, compute `M`'s transition,
  sweep back writing the new block, and reposition to the neighboring block
  per the simulated move (`O(L)` steps in total per tape, `L` fixed) —
  constant factor, hence `c * (T n + 1)`.
- **Input tape**: `M` reads symbols of the form `some (e b)` (its inputs are
  `x.map e`); `M'` reads `some b` on the raw input `x` and translates through
  `e` inside its transition — no blocks on the read-only input tape.
  Boundary blanks pass through as blanks.
- **Output**: on the hypothesis inputs, `M`'s completed output is
  `(f x).map e`, and output is append-only, so every emitted symbol is in
  `e`'s image (`Turing.MultiTapeTM.output_prefix`); `M'` emits the
  `e`-preimage (decidable since `DecidableEq Γ` and `e` is injective). For
  totality of the machine define an arbitrary emission on non-image symbols;
  the correctness proof never meets that case — but say so explicitly in the
  invariant.
- `k = 0` degenerates to state-and-input-only translation — handle it first
  and separately if that is simpler.

## Out-of-scope sorries you will see (leave every one untouched)

`computesFunInTime_comp`, `exists_comp_partial` (Composition.lean);
`one_work_tape` (SingleTape.lean); `oblivious_of_mem_DTIME` (Oblivious.lean);
`exists_effectiveMachineCode` (Encoding.lean); `universal`, `timed_universal`
(Universal.lean). After your batch, exactly these 7 sorry warnings remain.

## REPORT.md checklist

- [ ] Targets filled (2), each with how the proof relates to its (corrected)
      sketch.
- [ ] New private declarations listed, for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Docstring appendices — or "none".
- [ ] Verification evidence: final sweep log attached, axiom log attached,
      zero `error:` lines, the exact 7 remaining sorry warnings.
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `update_noteq`); core `Nat.pow_pos`;
  `dite_eq_right/left` don't exist — `split <;> simp <;> omega`; after
  `cases hs : cfg.state` insert `dsimp only`; avoid bare `simp` against
  folded hypotheses (`initCfg` is `@[simp]`) — targeted `simp only`; `ring`
  needs `import Mathlib.Tactic.Ring`; `omega` can't see `Fin.val ⟨e, h⟩` or
  un-beta-reduced lambdas — normalize first; SignType names:
  `SignType.coe_one`, `neg_eq_neg_one`, `coe_neg_one`, `pos_eq_one`,
  `zero_eq_zero`; `moveInputPos_zero`, `moveInputPos_pos_of_ne_right`,
  `moveInputPos_neg_of_ne_left`, `moveInputPos_neg_val` (Simulation.lean).
- Work tapes are ℤ-indexed `Option Γ'` functions updated via
  `Function.update`; blanks are `none`; `Cfg.ext` / `Cfg.ext_zero_tapes`
  prove configuration equality field by field.
- `(x.map e).length = x.length` (`List.length_map`) reconciles the `Via`
  bound's length with the raw input's.
- Proved in-repo exemplars: `StateRenaming.lean` (coordinate-transport
  commutation), `counterTM`'s `counterTape` shape function
  (TimeConstructible.lean), `condTM`'s phase machinery (Composition.lean),
  the `Simulation.lean` lockstep suites.

---

# ATTACHMENT C — Lean sources (epoch-2 surface first, then the rest)

## ===== TCSlib/Complexity/TuringMachine/Simulation.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation gadgets

Generic building blocks for machine constructions, split out of
`TCSlib.Complexity.TuringMachine.Composition` at the epoch-1/epoch-2 boundary
(epoch-1 audit, findings 5 and 11, and the policy file-size standard): the
machines of the composition file, and the heavier constructions of later
epochs, are assembled from these. Everything here is public — it is shared
audited surface — and carries no finiteness assumptions beyond what each
gadget needs.

## Contents

* **Emission chains** (`Turing.FinTM.emitAction`, `emit_run`, `emit_halts`):
  states that write a fixed word to the output, one symbol per step, ignoring
  all reads, then halt.
* **Control actions** (`Turing.FinTM.controlAction`, `controlAction_apply`):
  transitions that only move the input head and change state.
* **Input-head positioning** (`Turing.FinTM.inputSymbol_at`,
  `moveInputPos_neg_val`, `rewind_scan`, `rewind_from_any`): reading at a
  position, the clamped left move, and the audited rewind-to-start procedure
  (one unconditional left move, left while reading a symbol, one right move).
* **Disjoint tape-block embeddings** (`Turing.FinTM.leftAction`/`rightAction`,
  `leftCfg`/`rightCfg`, their `apply`/`step`/`run` lemmas): run a machine on
  the left or right block of a `k + l`-tape machine, in lockstep, with the
  other block's tapes inactive. **Scope note** (epoch-1 audit, finding 11):
  these embeddings preserve the *native* input tape and pass emissions to the
  *real* output — they are not, by themselves, a buffered-composition
  simulator; buffering and virtual-input clamping need their own invariants on
  top.
* **Branch union** (`Turing.FinTM.branchTM`, `branchTM_computes`): two
  machines in disjoint tape and state blocks; the Boolean chooses only the
  initial state.
* **Buffered sequential simulator** (`Turing.FinTM.bufferedCompTM`): the
  three-block tape partition, contiguous buffer representation, virtual-input
  reads and clamping invariant, first- and second-phase run correspondence,
  and an exact `|y| + 2` rewind-and-dispatch ledger. These extend the scope of
  the native-input embeddings above without changing their statements.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
-/

namespace Turing.FinTM

/-- One step of a fixed-word emission chain, with an arbitrary state embedding.
The input and all work tapes are left untouched. -/
def emitAction {k : ℕ} {S : Type} (w : List Bool)
    (e : Fin (w.length + 1) → S) (i : Fin (w.length + 1)) : Action k Bool S :=
  if h : i.val < w.length then
    ⟨0, fun _ => (none, 0), some w[i.val], some (e ⟨i.val + 1, by omega⟩)⟩
  else
    ⟨0, fun _ => (none, 0), none, none⟩

/-- After `t` emission steps the state is the `t`-th chain state and exactly the
first `t` symbols have been appended. The induction uses no tape invariant because
emission transitions ignore all reads. -/
lemma emit_run {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    ∀ t (ht : t ≤ w.length),
      (tm.runFrom cfg t).state = some (e ⟨t, by omega⟩) ∧
      (tm.runFrom cfg t).output = cfg.output ++ w.take t := by
  intro t
  induction t with
  | zero =>
    intro ht
    exact ⟨hs, by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hout⟩ := ih (by omega)
    have hstep : tm.runFrom cfg (t + 1) =
        (emitAction w e ⟨t, by omega⟩).apply (tm.runFrom cfg t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      exact congrArg (fun a => a.apply (tm.runFrom cfg t)) (htr _ _ _)
    rw [hstep]
    simp only [emitAction, dif_pos (show t < w.length by omega), Action.apply]
    refine ⟨True.intro, ?_⟩
    rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp [List.append_assoc]

/-- One further, nonemitting step halts the fixed-word emission chain. -/
lemma emit_halts {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    (tm.runFrom cfg (w.length + 1)).state = none ∧
      (tm.runFrom cfg (w.length + 1)).output = cfg.output ++ w := by
  obtain ⟨hstate, hout⟩ := emit_run tm w e htr cfg hs w.length (le_refl _)
  rw [MultiTapeTM.runFrom_succ_eq_step']
  unfold MultiTapeTM.step
  rw [hstate]
  dsimp only
  rw [htr]
  simp [emitAction, Action.apply, hout]


/-- An action that only moves the input head and changes the state. -/
def controlAction {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    Action k Bool S := ⟨m, fun _ => (none, 0), none, q⟩

/-- Read position `i + 1` as the optional `i`-th input symbol, including the
right boundary. -/
lemma inputSymbol_at {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (i : ℕ) (hi : i ≤ x.length)
    (hp : cfg.inputPos.val = i + 1) : cfg.inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [inputSymbolInner i (by omega) h, List.getElem?_eq_getElem h]
  · have he : i = x.length := by omega
    have hz : cfg.inputPos ≠ 0 := by
      intro hz
      rw [hz] at hp
      simp at hp
    simp only [Cfg.inputSymbol, dif_neg hz, dif_pos (show cfg.inputPos.val = x.length + 1 by omega)]
    simp [he]


/-- Extend an action to the left block of a disjoint tape sum and rename states. -/
def leftAction {k : ℕ} {S S' : Type} (l : ℕ) (f : S → S')
    (a : Action k Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases a.workTapes (fun _ => (none, 0))
  output := a.output
  state := a.state.map f

/-- Extend an action to the right block, leaving the left block untouched. -/
def rightAction {l : ℕ} {S S' : Type} (k : ℕ) (f : S → S')
    (a : Action l Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases (fun _ => (none, 0)) a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a configuration in the left tape block, retaining arbitrary inactive
right tapes and head positions. The state renaming preserves halting. -/
def leftCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes tapes
  workTapePos := Fin.addCases c.workTapePos heads
  output := c.output

/-- Embed in the right block, retaining arbitrary inactive left tapes. This is also
used when the left block contains a completed controller's work. -/
def rightCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases tapes c.workTapes
  workTapePos := Fin.addCases heads c.workTapePos
  output := c.output

/-- Extending an action commutes with the left configuration embedding. -/
lemma leftCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action k Bool S) (c : Cfg k Bool S x)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (leftAction l f a).apply (leftCfg f c tapes heads) =
      leftCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]

/-- Extending an action commutes with the right configuration embedding. -/
lemma rightCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action l Bool S) (c : Cfg l Bool S x)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    (rightAction k f a).apply (rightCfg f c tapes heads) =
      rightCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]

/-- A machine whose renamed transitions use only the left block simulates one
step exactly, including the absorbing halting configuration. -/
lemma leftCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    tm'.step (leftCfg f c tapes heads) = leftCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [leftCfg, hs]
  | some q =>
    have hs' : (leftCfg f c tapes heads).state = some (f q) := by simp [leftCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (leftCfg f c tapes heads).workTapeSymbols (Fin.castAdd l i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, leftCfg]
    change (leftAction l f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact leftCfg_apply f _ c tapes heads

/-- The right-block version of the one-step correspondence; inactive tapes may
contain arbitrary data from an earlier phase. -/
lemma rightCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    tm'.step (rightCfg f c tapes heads) = rightCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [rightCfg, hs]
  | some q =>
    have hs' : (rightCfg f c tapes heads).state = some (f q) := by simp [rightCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (rightCfg f c tapes heads).workTapeSymbols (Fin.natAdd k i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, rightCfg]
    change (rightAction k f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact rightCfg_apply f _ c tapes heads

/-- Lift the left-block one-step correspondence to every finite run. -/
lemma leftCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (t : ℕ) :
    tm'.runFrom (leftCfg f c tapes heads) t = leftCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => leftCfg f c tapes heads)
    (fun c => leftCfg_step tm tm' f htr c tapes heads) c t

/-- Lift the right-block correspondence to every run, preserving arbitrary
inactive left tapes. This is the fresh-branch lockstep gadget. -/
lemma rightCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (t : ℕ) :
    tm'.runFrom (rightCfg f c tapes heads) t = rightCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => rightCfg f c tapes heads)
    (fun c => rightCfg_step tm tm' f htr c tapes heads) c t

/-- Put two machines in disjoint tape and state blocks; the Boolean chooses only
the initial state, while the transition table is independent of that choice. -/
def branchTM (M₁ M₂ : FinTM Bool) (b : Bool) : FinTM Bool where
  k := M₁.k + M₂.k
  State := M₁.State ⊕ M₂.State
  tm :=
    { q₀ := cond b (.inl M₁.tm.q₀) (.inr M₂.tm.q₀)
      tr := fun q inp work => match q with
        | .inl q => leftAction M₂.k Sum.inl
            (M₁.tm.tr q inp (fun i => work (Fin.castAdd M₂.k i)))
        | .inr q => rightAction M₁.k Sum.inr
            (M₂.tm.tr q inp (fun i => work (Fin.natAdd M₁.k i))) }

/-- Each selected branch has exactly its original time and completed output.
The proof embeds its initial blank configuration, then uses lockstep. -/
lemma branchTM_computes (M₁ M₂ : FinTM Bool) (b : Bool) (x w : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).ComputesInTime x w t ↔ (cond b M₁ M₂).ComputesInTime x w t := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr (fun _ _ _ => rfl)]
    simp only [rightCfg, Option.map_eq_none_iff]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl (fun _ _ _ => rfl)]
    simp only [leftCfg, Option.map_eq_none_iff]

/-- A control action leaves all work tapes, work heads, and output unchanged. -/
lemma controlAction_apply {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (m : SignType) (q : Option S) :
    (controlAction m q).apply cfg =
      {cfg with state := q, inputPos := moveInputPos cfg.inputPos m} := by
  refine Cfg.ext rfl rfl rfl ?_ ?_
  · funext i
    simp [controlAction, Action.apply]
  · simp [controlAction, Action.apply]

/-- The clamped left move always subtracts one from the natural input position. -/
lemma moveInputPos_neg_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos .neg).val = pos.val - 1 := by
  by_cases h : pos = 0
  · subst pos
    simp [SignType.neg_eq_neg_one]
  · rw [moveInputPos_neg_of_ne_left pos h]

/-- Starting at or to the left of the last input symbol, scan left to the left
blank, then move right and dispatch. All other configuration fields are preserved.

**Proof sketch.** Induct on the input-head position. At zero the scanned symbol is
blank, so one right move finishes. At a positive position the input symbol exists;
one left move reduces the position and the induction hypothesis finishes the run. -/
lemma rewind_scan {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (cfg : Cfg k Bool S x), cfg.state = some scan → cfg.inputPos.val ≤ x.length →
      tm.runFrom cfg (cfg.inputPos.val + 1) = {cfg with state := dest, inputPos := 1} := by
  have aux : ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      tm.runFrom cfg (j + 1) = {cfg with state := dest, inputPos := 1} := by
    intro j
    induction j with
    | zero =>
      intro cfg hs hj _
      have hz : cfg.inputPos = 0 := Fin.ext hj
      have hsym : cfg.inputSymbol = none := by
        unfold Cfg.inputSymbol
        rw [dif_pos hz]
      change tm.step cfg = _
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [htr, hsym]
      dsimp only
      rw [controlAction_apply]
      have hm : moveInputPos cfg.inputPos .pos = 1 := by
        apply Fin.ext
        rw [hz, moveInputPos_pos_of_ne_right _ (by simp)]
        simp
      rw [hm]
    | succ j ih =>
      intro cfg hs hj hlen
      have hsym : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have hstep : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        unfold MultiTapeTM.step
        rw [hs]
        dsimp only
        rw [htr, hsym]
        dsimp only
        rw [controlAction_apply]
      have hp : (moveInputPos cfg.inputPos .neg).val = j := by
        rw [moveInputPos_neg_val]
        omega
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ih _ rfl hp (by omega)
  intro cfg hs hp
  exact aux cfg.inputPos.val cfg hs rfl hp

/-- From any valid input position, take the mandatory first left move and then
scan left. This returns to position `1`, even for an empty input or a start at a
boundary. No work tape or output is changed. -/
lemma rewind_from_any {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t, tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_⟩
  rw [MultiTapeTM.runFrom_add]
  have hfirst : tm.runFrom cfg 1 = c := rfl
  rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
  simp only [c, hstep]

/-- Assemble the left work block, one buffer tape, and the right work block.
All three projections use the same nested `Fin.addCases` partition. -/
def tapeBlocks {α : Type} {k l : ℕ} (left : Fin k → α) (buffer : α)
    (right : Fin l → α) : Fin (k + (1 + l)) → α :=
  Fin.addCases left (Fin.addCases (fun _ => buffer) right)

/-- The left projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_left {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin k) :
    tapeBlocks a b c (Fin.castAdd (1 + l) i) = a i := by simp [tapeBlocks]

/-- The buffer projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_buffer {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin 1) :
    tapeBlocks a b c (Fin.natAdd k (Fin.castAdd l i)) = b := by
  simp [tapeBlocks]

/-- The right projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_right {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin l) :
    tapeBlocks a b c (Fin.natAdd k (Fin.natAdd 1 i)) = c i := by simp [tapeBlocks]

/-- A word stored contiguously from cell zero, blank at every other integer cell. -/
def bufferTape (w : List Bool) (z : ℤ) : Option Bool :=
  if 0 ≤ z then w[z.toNat]? else none

/-- An empty buffer is blank everywhere. -/
@[simp] lemma bufferTape_nil : bufferTape [] = fun _ => none := by
  funext z
  simp [bufferTape]

/-- The buffer cell at any nonnegative natural position reads the corresponding
optional word entry, so position `w.length` is the right blank. -/
@[simp] lemma bufferTape_nat (w : List Bool) (i : ℕ) :
    bufferTape w i = w[i]? := by simp [bufferTape]

/-- Cell minus one is the left blank, including for an empty word. -/
@[simp] lemma bufferTape_left (w : List Bool) : bufferTape w (-1) = none := by
  simp [bufferTape]

/-- Appending one emitted bit changes just the old right-blank cell.

**Proof sketch.** At that cell the appended singleton is read. At a smaller
nonnegative cell, list lookup stays in the old prefix. Larger cells and all
negative cells remain blank. -/
lemma bufferTape_append (w : List Bool) (b : Bool) :
    bufferTape (w ++ [b]) = Function.update (bufferTape w) (w.length : ℤ) (some b) := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z
    simp [bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hgt : w.length < z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · simp [bufferTape, h0]

/-- A boundary tag constrains only boundary positions: false at the left blank,
true at the right blank. Interior positions admit either direction-of-arrival tag. -/
def VirtualTag {n : ℕ} (p : Fin (n + 2)) (b : Bool) : Prop :=
  (p.val = 0 → b = false) ∧ (p.val = n + 1 → b = true)

/-- Suppress an outward move at a blank whose boundary is identified by the tag.
The real buffer head otherwise takes the simulated input movement. -/
def virtualMove (b : Bool) (inp : Option Bool) (m : SignType) : SignType :=
  if inp = none ∧ ((b = false ∧ m = .neg) ∨ (b = true ∧ m = .pos)) then 0 else m

/-- Record the last nonstationary buffer movement. A stationary move preserves
its boundary tag, so repeated outward attempts remain clamped. -/
def virtualNextTag (b : Bool) (m : SignType) : Bool :=
  match m with
  | .neg => false
  | .zero => b
  | .pos => true

/-- Buffer reads at virtual position minus one equal native input reads. -/
lemma bufferTape_inputSymbol {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) : bufferTape w ((c.inputPos.val : ℤ) - 1) = c.inputSymbol := by
  by_cases h0 : c.inputPos = 0
  · simp [Cfg.inputSymbol, h0]
  · have hp : 0 < c.inputPos.val := by
      have : c.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      omega
    have he : (c.inputPos.val : ℤ) - 1 = ((c.inputPos.val - 1 : ℕ) : ℤ) := by omega
    rw [he, bufferTape_nat]
    have h := inputSymbol_at c (c.inputPos.val - 1)
      (by have := c.inputPos.isLt; omega) (by omega)
    exact h.symm

/-- The virtual movement and arrival tag exactly implement native clamping.

**Proof sketch.** Split into left boundary, right boundary, and interior. The
buffer is blank exactly at the two boundaries in this range. The tag specifies
which outward direction to suppress. The three movement cases then give the
position equation and preserve the boundary-tag invariant, even on empty input. -/
lemma virtualMove_correct {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) (b : Bool) (hb : VirtualTag c.inputPos b) (m : SignType) :
    (c.inputPos.val : ℤ) - 1 + (virtualMove b c.inputSymbol m : ℤ) =
      ((moveInputPos c.inputPos m).val : ℤ) - 1 ∧
    VirtualTag (moveInputPos c.inputPos m)
      (virtualNextTag b (virtualMove b c.inputSymbol m)) := by
  have hp := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have he : c.inputPos = 0 := Fin.ext h0
    have hbf := hb.1 h0
    subst b
    cases m <;>
      simp [virtualMove, virtualNextTag, Cfg.inputSymbol, he, VirtualTag,
        moveInputPos, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
        SignType.pos_eq_one]
  · have hne : c.inputPos ≠ 0 := fun h => h0 (congrArg Fin.val h)
    by_cases hr : c.inputPos.val = w.length + 1
    · have hbt := hb.2 hr
      subst b
      have he : c.inputPos = ⟨w.length + 1, by omega⟩ := Fin.ext hr
      have hs : c.inputSymbol = none := by simp [Cfg.inputSymbol, he]
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | pos =>
        simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.pos_eq_one]
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, hr, SignType.neg_eq_neg_one]
        omega
    · have hs : c.inputSymbol = some (w[c.inputPos.val - 1]'(by omega)) :=
        inputSymbolInner _ (by omega) (by omega)
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.neg_eq_neg_one]
        constructor <;> omega
      | pos =>
        rw [moveInputPos_pos_of_ne_right _ hr]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.pos_eq_one]

/-- Run the first machine into the middle buffer, rewind it, then run the second
machine with virtual input. The first component's halting state and the rewind
state are live administrative states. Phase two alone can halt or emit output. -/
def bufferedCompTM (M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := M₁.k + (1 + M₂.k)
  State := Option M₁.State ⊕ (Unit ⊕ (M₂.State × Bool))
  tm :=
    { q₀ := .inl (some M₁.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M₁.tm.tr q inp (fun i => work (Fin.castAdd (1 + M₂.k) i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none =>
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
            none, some (.inr (.inl ()))⟩
        | .inr (.inl ()) =>
          if work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = none then
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos) (fun _ => (none, 0)),
              none, some (.inr (.inr (M₂.tm.q₀, true)))⟩
          else
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
              none, some (.inr (.inl ()))⟩
        | .inr (.inr (q, b)) =>
          let v := work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1)))
          let a := M₂.tm.tr q v (fun i => work (Fin.natAdd M₁.k (Fin.natAdd 1 i)))
          let m := virtualMove b v a.inputTape
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, m) a.workTapes,
            a.output, a.state.map (fun q => .inr (.inr (q, virtualNextTag b m)))⟩ }

/-- Embed phase one with its exact emitted prefix on the buffer and the buffer
head on its right blank. The real output and the second work block are empty. -/
def bufferedFirstCfg (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inl c.state)
  inputPos := c.inputPos
  workTapes := tapeBlocks c.workTapes (bufferTape c.output) (fun _ _ => none)
  workTapePos := tapeBlocks c.workTapePos c.output.length (fun _ => 0)
  output := []

/-- The initialized composite is the embedded initialized first machine. -/
lemma bufferedFirstCfg_init (M₁ M₂ : FinTM Bool) (x : List Bool) :
    (bufferedCompTM M₁ M₂).tm.initCfg x = bufferedFirstCfg M₁ M₂ (M₁.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]

/-- One live first-phase transition preserves the complete buffer invariant,
including an emission on the simulated halting transition.

**Proof sketch.** The first work block and native input move in lockstep. A
nonemitting transition leaves the buffer fixed; an emission updates precisely its
right blank by `bufferTape_append` and moves that head one step. The second block
and real output stay empty, and a simulated halt remains an administrative state. -/
lemma bufferedFirstCfg_step (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedFirstCfg M₁ M₂ (M₁.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (bufferedFirstCfg M₁ M₂ c).state = some (.inl (some q)) := by
      simp [bufferedFirstCfg, hq]
    rw [hs']
    dsimp only [bufferedCompTM]
    have hr : (fun i => (bufferedFirstCfg M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (1 + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [bufferedFirstCfg, Cfg.workTapeSymbols]
    have hi : (bufferedFirstCfg M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    let a := M₁.tm.tr q c.inputSymbol c.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M₁.k + (1 + M₂.k)) Bool _).apply _ = bufferedFirstCfg M₁ M₂ (a.apply c)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [bufferedFirstCfg, Action.apply, ho, bufferTape_append]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [bufferedFirstCfg, Action.apply, ho]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · simp [bufferedFirstCfg, Action.apply]

/-- First-phase lockstep holds up to and including the first halting transition.
The hypothesis deliberately excludes steps after the simulated halt. -/
lemma bufferedFirstCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (t : ℕ)
    (h : ∀ s, s < t → (M₁.tm.runFrom c s).state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) t =
      bufferedFirstCfg M₁ M₂ (M₁.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      bufferedFirstCfg_step M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Embed a configuration on virtual input `y` while the physical input remains
`x`. The buffer head represents virtual position minus one. The left block and
native input head retain arbitrary inactive contents from phase one. -/
def bufferedSecondCfg (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := c.state.map (fun q => .inr (.inr (q, b)))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) c.workTapes
  workTapePos := tapeBlocks heads ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := c.output

/-- One second-phase step simulates one native step, with a valid new arrival
tag. The statement includes the absorbing halting case.

**Proof sketch.** Buffer reads agree with virtual input reads. The clamping lemma
proves the head equation and preserves the tag. All second-machine work actions
and emissions are unchanged, while the buffer and first block are read-only. -/
lemma bufferedSecondCfg_step (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) :
    ∃ b', VirtualTag (M₂.tm.step c).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.step (bufferedSecondCfg M₁ M₂ c b p tapes heads) =
        bufferedSecondCfg M₁ M₂ (M₂.tm.step c) b' p tapes heads := by
  cases hq : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [bufferedSecondCfg, hq]
  | some q =>
    let a := M₂.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := virtualMove b c.inputSymbol a.inputTape
    have hm := virtualMove_correct c b hb a.inputTape
    have hc : M₂.tm.step c = a.apply c := by
      simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag b m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs : (bufferedSecondCfg M₁ M₂ c b p tapes heads).state =
          some (.inr (.inr (q, b))) := by simp [bufferedSecondCfg, hq]
      have hv : (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = c.inputSymbol := by
        simp [bufferedSecondCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.natAdd 1 i))) = c.workTapeSymbols := by
        funext i
        simp [bufferedSecondCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [bufferedCompTM]
      rw [hv, hr, hq]
      change (Action.apply _ _) = bufferedSecondCfg M₁ M₂ (a.apply c) _ p tapes heads
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [bufferedSecondCfg, Action.apply, a]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [bufferedSecondCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [bufferedSecondCfg, Action.apply, a]

/-- Every second-phase run has a matching virtual run at the same time and a
valid arrival tag. This preserves completed outputs and absorbing halting. -/
lemma bufferedSecondCfg_run (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (t : ℕ) :
    ∃ b', VirtualTag (M₂.tm.runFrom c t).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.runFrom (bufferedSecondCfg M₁ M₂ c b p tapes heads) t =
        bufferedSecondCfg M₁ M₂ (M₂.tm.runFrom c t) b' p tapes heads := by
  induction t with
  | zero => exact ⟨b, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b', hb', he⟩ := ih
    obtain ⟨b'', hb'', he'⟩ := bufferedSecondCfg_step M₁ M₂ _ b' hb' p tapes heads
    refine ⟨b'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The rewind scan configuration, with buffer head at `j - 1` and all second
machine tapes still blank. The scan state is always live, including at `j = 0`. -/
def bufferedScanCfg (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (j : ℕ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inr (.inl ()))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) (fun _ _ => none)
  workTapePos := tapeBlocks heads ((j : ℤ) - 1) (fun _ => 0)
  output := []

/-- Scanning from virtual position `j ≤ |y|` takes exactly `j + 1` transitions
to reach the second machine's initialized configuration with arrival tag true.

**Proof sketch.** At zero the buffer head is at the left blank, so move right
and dispatch. At successor `j + 1`, cell `j` contains a symbol; one left move
reduces to `j`. For an empty word, dispatch reaches its right blank with the
correct true tag, and its left blank remains one inward move away. -/
lemma bufferedScanCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) : ∀ j, j ≤ y.length →
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedScanCfg M₁ M₂ y p tapes heads j) (j + 1) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
      tapeBlocks_buffer, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
  | succ j ih =>
    intro hj
    have hread : bufferTape y (((j + 1 : ℕ) : ℤ) - 1) = some y[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedScanCfg M₁ M₂ y p tapes heads (j + 1)) =
        bufferedScanCfg M₁ M₂ y p tapes heads j := by
      simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
        tapeBlocks_buffer, hread, Option.some_ne_none, if_false]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro z
          refine Fin.addCases ?_ ?_ z <;> intro z <;> simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (by omega)

/-- From a completed first-phase configuration, rewind and dispatch cost exactly
`|output| + 2` steps. The first move is unconditional from the right blank.

**Proof sketch.** That first left move reaches scan position `|output|`. Apply
the scan invariant for the remaining `|output| + 1` transitions. The real output
stays empty and the native input head and first work block stay fixed. -/
lemma bufferedFirstCfg_rewind (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state = none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) (c.output.length + 2) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg c.output) true c.inputPos c.workTapes c.workTapePos := by
  have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedScanCfg M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos c.output.length := by
    simp only [MultiTapeTM.step, bufferedFirstCfg, hs, bufferedCompTM]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply, sub_eq_add_neg]
  rw [show c.output.length + 2 = (c.output.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact bufferedScanCfg_run M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos _ (le_refl _)

/-- Any completed first computation reaches the second phase within
`t₁ + |y| + 2` steps, with a fresh second work block and virtual input `y`.

**Proof sketch.** Choose the first halting time, which is at most `t₁`.
First-phase lockstep reaches its completed configuration, and determinism
identifies the output with `y`. The exact rewind lemma supplies `|y| + 2` more
steps, retaining the first block and parked native input head. -/
lemma bufferedComp_start (M₁ M₂ : FinTM Bool) (x y : List Bool) (t₁ : ℕ)
    (h₁ : M₁.ComputesInTime x y t₁) :
    ∃ (a : ℕ) (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
      (heads : Fin M₁.k → ℤ), a ≤ t₁ + y.length + 2 ∧
      (bufferedCompTM M₁ M₂).tm.runFrom ((bufferedCompTM M₁ M₂).tm.initCfg x) a =
        bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  classical
  have hh : ∃ t, (M₁.tm.runFrom (M₁.tm.initCfg x) t).state = none :=
    ⟨t₁, ((computesInTime_iff M₁ x y t₁).mp h₁).1⟩
  let t := Nat.find hh
  let c := M₁.tm.runFrom (M₁.tm.initCfg x) t
  have hs : c.state = none := Nat.find_spec hh
  have ht : t ≤ t₁ := Nat.find_min' hh ((computesInTime_iff M₁ x y t₁).mp h₁).1
  have hc : M₁.ComputesInTime x c.output t :=
    (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = y := hc.output_unique h₁
  refine ⟨t + (y.length + 2), c.inputPos, c.workTapes, c.workTapePos, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run M₁ M₂ _ t (fun s hs => Nat.find_min hh hs)]
  have hf := bufferedFirstCfg_rewind M₁ M₂ c hs
  cases ho
  exact hf

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Composition.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Composition of Turing machine computations

Basic computability combinators for the bundled machines: the identity and constant
functions are linear-time computable, and time-bounded computability is closed under
composition. Composition is the load-bearing lemma of the whole development — the
universal machine (phase 3) and the `HALT` reduction (phase 4) are built from it — and
it is the part [AB09] never spells out, dispatching it with "high-level descriptions"
of machines. The Isabelle AFP `Cook_Levin` entry spends a large fraction of its effort
exactly here.

## Design

Composition is stated at the *specification* level (`ComputesFunInTime`), not as an
operator on raw machines: the composed machine is existentially produced. Internally
(proof obligation, not API) the construction simulates `M₁` with its emissions
redirected to a fresh work tape, then simulates `M₂` reading that tape in place of its
input tape.

**Convention obligation status** (phase-1 audit finding 4; phase-2 audit finding 3):
this file does *not* formally discharge the append-only vs read-write output-tape
bridge. Every statement here — hypotheses and conclusions alike — lives in the
append-only model, and [AB09]'s read-write-output machine is not formalized in this
development, so no simulation between the two conventions can even be stated yet. The
obligation is recorded in the plan's decision log as **waived**, with the compensating
restriction that no exact-step-count transfer from [AB09] is ever claimed: every bound
*adapted from the source* carries an existential constant (purely internal results,
such as the oracle lockstep lemmas, are legitimately exact but never cross a
convention), and every result is self-contained in-model. A formal bridge (a
read-write-output machine variant plus a simulation theorem) will be added if and only
if a downstream result needs it. What this file *does* provide is the buffer-and-flush
technique — an emission can be deferred to a work tape and flushed at the end — which
is what delayed or revisable output looks like *within this model*; whether the
append-only convention matches [AB09]'s read-write one remains formally unestablished,
per the waiver.

The generic simulation gadgets this file's machines are assembled from — emission
chains, control actions, disjoint tape-block embeddings with their lockstep run
lemmas, the input-head rewind, and the two-machine branch union — live in
`TCSlib.Complexity.TuringMachine.Simulation` (split out at the epoch-1/epoch-2
boundary, per the epoch-1 audit findings 5 and 11 and the policy file-size
standard); this file keeps only its concrete machines and their theorems.

## Main results

* Time-bounded combinators (all over the binary alphabet):
  `Turing.FinTM.computesFunInTime_id`, `Turing.FinTM.computesFunInTime_const`,
  `Turing.FinTM.computesFunInTime_ifEq`, `Turing.FinTM.computesFunInTime_comp`.
* **Partial (guarded) combinators** — the phase-4 API mandated by the phase-3 audit
  (round 2, finding 10 and Argument F: the total-function composition cannot take
  the partially computing universal evaluator as a component):
  `Turing.FinTM.exists_comp_partial` composes two arbitrary machines at the level of
  their halting relations, with the intermediate output buffered on a work tape;
  `Turing.FinTM.exists_cond` branches between two machines on a decided predicate.
  Both are stated untimed; time-bounded refinements are deliberately deferred until
  a result needs them.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
* [Balbach22] F. J. Balbach, *The Cook-Levin theorem*, Archive of Formal Proofs
  (Isabelle), 2022 — the composition-combinator architecture this file follows in
  spirit.
-/

namespace Turing.FinTM

/-- The one-state copy machine: emits each input bit moving right, and halts on the
boundary blank. -/
private def idTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some b => ⟨SignType.pos, fun i => i.elim0, some b, some ()⟩
        | none => ⟨SignType.zero, fun i => i.elim0, none, none⟩ }

/-- Run invariant of the copy machine: after `t ≤ n` steps it is live, its input head
sits at position `t + 1`, and it has emitted exactly the first `t` input bits. -/
private lemma idTM_run (x : List Bool) : ∀ t, t ≤ x.length →
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).state = some () ∧
    (((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) = t + 1) ∧
    (idTM.tm.runFrom (idTM.tm.initCfg x) t).output = x.take t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hpos, hout⟩ := ih (Nat.le_of_succ_le ht)
    have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (t + 1) =
        (idTM.tm.tr () (some (x[t]'(by omega)))
          ((idTM.tm.runFrom (idTM.tm.initCfg x) t).workTapeSymbols)).apply
          (idTM.tm.runFrom (idTM.tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show ((idTM.tm.runFrom (idTM.tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- The identity function is computable in linear time: the copy machine halts within
`n + 1` steps having emitted its input verbatim (invariant `idTM_run`, then one
halting step on the boundary blank). -/
theorem computesFunInTime_id :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id fun n => c * (n + 1) := by
  refine ⟨idTM, 1, fun x => ?_⟩
  obtain ⟨hstate, hpos, hout⟩ := idTM_run x x.length (le_refl _)
  have h0 : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputPos ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hsym : (idTM.tm.runFrom (idTM.tm.initCfg x) x.length).inputSymbol = none := by
    unfold Cfg.inputSymbol
    rw [dif_neg h0, dif_pos (by omega)]
  have hrun1 : idTM.tm.runFrom (idTM.tm.initCfg x) (x.length + 1) =
      (idTM.tm.tr () none
        ((idTM.tm.runFrom (idTM.tm.initCfg x) x.length).workTapeSymbols)).apply
        (idTM.tm.runFrom (idTM.tm.initCfg x) x.length) := by
    rw [MultiTapeTM.runFrom_succ_eq_step']
    unfold MultiTapeTM.step
    rw [hstate]
    dsimp only
    rw [hsym]
  have hbase : idTM.ComputesInTime x x (x.length + 1) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [hrun1]
      simp [idTM, Action.apply]
    · rw [hrun1]
      simp only [idTM, Action.apply]
      rw [hout]
      simp
  exact hbase.mono (le_of_eq (one_mul _).symm)

/-- The zero-work-tape machine whose states form the emission chain for `w`. -/
private def constTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm := { q₀ := 0, tr := fun i _ _ => emitAction w id i }

/-- Every constant function is computable in linear time (in fact in time `|w| + 1`,
which the stated bound dominates once `c ≥ |w| + 1`).

**Proof sketch.** A zero-work-tape machine with `|w| + 1` states `s₀, …, s_{|w|}`:
state `sᵢ` emits the `i`-th symbol of `w` and moves to `s_{i+1}`, ignoring the input;
`s_{|w|}` halts. -/
theorem computesFunInTime_const (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) fun n => c * (n + 1) := by
  refine ⟨constTM w, w.length + 1, fun x => ?_⟩
  obtain ⟨hs, ho⟩ := emit_halts (constTM w).tm w id (fun _ _ _ => rfl)
    ((constTM w).tm.initCfg x) rfl
  have hbase : (constTM w).ComputesInTime x w (w.length + 1) := by
    exact ⟨_, hs, by simpa only [MultiTapeTM.initCfg, Cfg.init, List.nil_append] using ho, rfl⟩
  exact hbase.mono (Nat.le_mul_of_pos_right _ (by omega))

/-- The hardcoded comparator, followed by the chosen fixed-word emission chain. -/
private def ifEqTM (w₀ u v : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w₀.length + 1) ⊕ (Fin (u.length + 1) ⊕ Fin (v.length + 1))
  tm :=
    { q₀ := .inl 0
      tr := fun q inp _ => match q with
        | .inl i =>
          if h : i.val < w₀.length then
            if inp = some w₀[i.val] then
              controlAction .pos (some (.inl ⟨i.val + 1, by omega⟩))
            else controlAction 0 (some (.inr (.inr 0)))
          else if inp = none then controlAction 0 (some (.inr (.inl 0)))
            else controlAction 0 (some (.inr (.inr 0)))
        | .inr (.inl i) => emitAction u (fun j => .inr (.inl j)) i
        | .inr (.inr i) => emitAction v (fun j => .inr (.inr j)) i }

/-- Once the comparator has chosen its output chain, that chain emits the selected
word and halts, independently of the input-head position. -/
private lemma ifEq_finish (w₀ u v x : List Bool) (b : Bool)
    (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x)
    (hs : cfg.state = some (.inr (cond b (.inl 0) (.inr 0)))) (ho : cfg.output = []) :
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).state = none ∧
    ((ifEqTM w₀ u v).tm.runFrom cfg ((cond b u v).length + 1)).output = cond b u v := by
  cases b
  · simpa only [Bool.cond_false, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm v (fun j => .inr (.inr j))
        (fun _ _ _ => rfl) cfg hs
  · simpa only [Bool.cond_true, ho, List.nil_append] using
      emit_halts (ifEqTM w₀ u v).tm u (fun j => .inr (.inl j))
        (fun _ _ _ => rfl) cfg hs

/-- Comparison invariant: the first `i` symbols match, and the head is at `i + 1`.

**Proof sketch.** Induct on the number of remaining comparison symbols. A matching
symbol advances the invariant. A mismatch selects the second emission chain. With
no symbols remaining, the boundary blank selects the first chain and an extra
symbol selects the second. The emission-chain lemma supplies the remaining time. -/
private lemma ifEq_run (w₀ u v x : List Bool) : ∀ (r i : ℕ) (hlen : w₀.length = i + r), i ≤ x.length → x.take i = w₀.take i →
    ∀ (cfg : Cfg 0 Bool (ifEqTM w₀ u v).State x),
      cfg.state = some (.inl ⟨i, by omega⟩) → cfg.inputPos.val = i + 1 → cfg.output = [] →
      ∃ t, t ≤ r + max u.length v.length + 2 ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).state = none ∧
        ((ifEqTM w₀ u v).tm.runFrom cfg t).output = if x = w₀ then u else v := by
  intro r
  induction r with
  | zero =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : ¬i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases he : x = w₀
    · subst x
      have hb : w₀[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inl 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inl 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v w₀ true _ hs' ho'
      refine ⟨u.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_true, if_pos rfl] using hf
    · have hx : i < x.length := by
        by_contra hh
        have hxt : x.take i = x := List.take_of_length_le (by omega)
        have hwt : w₀.take i = w₀ := List.take_of_length_le (by omega)
        exact he (by rw [← hxt, ← hwt]; exact hprefix)
      have hb : x[i]? = some x[i] := List.getElem?_eq_getElem hx
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_neg hi, hb, Option.some_ne_none, ite_false]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf
  | succ r ih =>
    intro i hlen hix hprefix cfg hs hp ho
    have hi : i < w₀.length := by omega
    have hsym := inputSymbol_at cfg i hix hp
    by_cases hm : x[i]? = some w₀[i]
    · obtain ⟨hx, hbit⟩ := List.getElem?_eq_some_iff.mp hm
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction .pos (some (.inl ⟨i + 1, by omega⟩))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, hm, ite_true]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state =
          some (.inl ⟨i + 1, by omega⟩) := by rw [hstep]; rfl
      have hp' : ((ifEqTM w₀ u v).tm.step cfg).inputPos.val = (i + 1) + 1 := by
        rw [hstep]
        change (moveInputPos cfg.inputPos .pos).val = i + 1 + 1
        rw [moveInputPos_pos_of_ne_right _ (by omega)]
        simp only
        omega
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hprefix' : x.take (i + 1) = w₀.take (i + 1) := by
        rw [List.take_succ, List.take_succ, hprefix, hm, List.getElem?_eq_getElem hi]
      obtain ⟨t, ht, htstate, htout⟩ := ih (i + 1) (by omega) (by omega) hprefix'
        ((ifEqTM w₀ u v).tm.step cfg) hs' hp' ho'
      refine ⟨t + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      exact ⟨htstate, htout⟩
    · have he : x ≠ w₀ := by
        intro he
        subst x
        exact hm (List.getElem?_eq_getElem hi)
      have hstep : (ifEqTM w₀ u v).tm.step cfg =
          (controlAction 0 (some (.inr (.inr 0)))).apply cfg := by
        unfold MultiTapeTM.step
        rw [hs]
        simp only [ifEqTM, hsym, dif_pos hi, if_neg hm]
      have hs' : ((ifEqTM w₀ u v).tm.step cfg).state = some (.inr (.inr 0)) := by
        rw [hstep]
        rfl
      have ho' : ((ifEqTM w₀ u v).tm.step cfg).output = [] := by
        simp [hstep, controlAction, Action.apply, ho]
      have hf := ifEq_finish w₀ u v x false _ hs' ho'
      refine ⟨v.length + 1 + 1, by omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step]
      simpa only [Bool.cond_false, if_neg he] using hf

/-- Testing equality with a fixed string is computable in linear time: for any fixed
`w₀ u v`, the function `w ↦ u` if `w = w₀` and `w ↦ v` otherwise. (Instantiated by
the `HALT` reduction as the postprocessor `w ↦ if w = [true] then [false] else
[true]`; see `TCSlib.Complexity.Uncomputability.Halting`.)

**Proof sketch.** Hardcode `w₀`, `u`, and `v` in the states. The machine walks the
input left to right comparing it against `w₀` symbol by symbol (`|w₀| + 1`
comparison states); on the first mismatch — including the input ending early (blank
read) or running long (a symbol where `w₀` is exhausted) — it switches to an
emission chain for `v`, and after matching all of `w₀` and then reading the boundary
blank it switches to an emission chain for `u` (at most `|u| + |v| + 2` further
states, one emitted symbol per step). Every run halts within
`|w₀| + max |u| |v| + 3` steps — a constant, absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_ifEq (w₀ u v : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun w => if w = w₀ then u else v) fun n => c * (n + 1) := by
  refine ⟨ifEqTM w₀ u v, w₀.length + max u.length v.length + 3, fun x => ?_⟩
  obtain ⟨t, ht, hs, ho⟩ := ifEq_run w₀ u v x w₀.length 0 (by omega) (by omega) rfl
    ((ifEqTM w₀ u v).tm.initCfg x) rfl (by simp) rfl
  have hbase : (ifEqTM w₀ u v).ComputesInTime x (if x = w₀ then u else v) t :=
    ⟨_, hs, ho, rfl⟩
  exact hbase.mono (Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (by omega)))

/-- **Composition.** If `f` is computable within `T₁` and `g` within a monotone `T₂`,
then `g ∘ f` is computable within `c · (T₁ n + T₂ (T₁ n) + 1)`.

The inner bound `T₂ (T₁ n)` is valid because the intermediate string is no longer than
the time that produced it: `|f x| ≤ T₁ |x|` by `Turing.MultiTapeTM.output_length_le`.
Monotonicity of `T₂` is genuinely needed to convert that length bound into a time
bound.

**Proof sketch.** Build `M` with `M₁.k + M₂.k + 1` work tapes over `Bool`. Phase one
simulates `M₁` step for step on the true input, with `M₁`'s emissions written instead
onto the dedicated intermediate tape (constant overhead per step; this is the
append-only-output buffering discussed in the module docstring). Phase two rewinds the
intermediate tape head (at most `T₁ n` steps) and simulates `M₂` step for step, with
`M₂`'s input-head reads served from the intermediate tape and `M₂`'s emissions going to
the real output tape. Phase two costs constant overhead per step of `M₂`, which halts
within `T₂ |f x| ≤ T₂ (T₁ n)` steps. Bookkeeping (phase switching, boundary detection
on the intermediate tape) is absorbed into `c`.

**Implementation note (epoch 2).** The shared `bufferedCompTM` has
`M₁.k + (1 + M₂.k)` tapes and uses one physical step per simulated step.
The first halting time is at most `T₁ |x|`; rewind and dispatch take exactly
`|f x| + 2` steps, including the unconditional first left move. Consequently
`2 * T₁ |x| + T₂ (T₁ |x|) + 2` suffices, and the theorem uses `c = 2`. -/
theorem computesFunInTime_comp {M₁ M₂ : FinTM Bool} {f g : List Bool → List Bool}
    {T₁ T₂ : ℕ → ℕ}
    (h₁ : M₁.ComputesFunInTime f T₁) (h₂ : M₂.ComputesFunInTime g T₂)
    (hT₂ : Monotone T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (g ∘ f) fun n => c * (T₁ n + T₂ (T₁ n) + 1) := by
  refine ⟨bufferedCompTM M₁ M₂, 2, fun x => ?_⟩
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    bufferedComp_start M₁ M₂ x (f x) (T₁ x.length) (h₁ x)
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((computesInTime_iff _ _ _ _).mp (h₁ x)).2
    simpa only [ho] using M₁.tm.output_length_le x (T₁ x.length)
  -- This is the only use of monotonicity: transfer the intermediate length bound.
  have htime : T₂ (f x).length ≤ T₂ (T₁ x.length) := hT₂ hlen
  obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg (f x)) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ (f x).length)
  have hc := (computesInTime_iff _ _ _ _).mp (h₂ (f x))
  have hbase : (bufferedCompTM M₁ M₂).ComputesInTime x (g (f x))
      (a + T₂ (f x).length) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  exact hbase.mono (by dsimp only; omega)

/-- **Partial (guarded) sequential composition** — the phase-4 API obligation
identified by the phase-3 audit (round 2, finding 10 and Argument F):
`Turing.FinTM.computesFunInTime_comp` requires both components to compute *total*
functions, so it cannot take a partially computing machine — such as the universal
evaluator — as a component. This lemma composes two arbitrary machines at the level
of their halting relations, with **no totality or time hypotheses**: `M` behaves on
`x` exactly as `M₂` behaves on `M₁`'s completed output — halting, completed outputs,
and divergence all correspond.

Statement notes. The intermediate string `y` is existentially quantified, but by
`Turing.FinTM.ComputesInTime.output_unique` at most one `y` satisfies the first
conjunct, so the right-hand side reads "`M₁` halts on `x` (necessarily with a unique
`y`), and then `M₂` halts on `y` with `w`". If `M₁` diverges on `x`, or halts but
`M₂` diverges on its output, both sides are empty — `M` diverges. A time-bounded
refinement is deliberately not stated; it will be added if and when a result needs
it.

**Proof sketch** (buffered intermediate output, per the audit's design). `M` carries
`M₁`'s and `M₂`'s work tapes plus a fresh *buffer* tape. Phase one simulates `M₁` on
the true input step for step, with each emission of `M₁` written to the buffer tape
(write, move right) instead of the output tape; the append-only output discipline
makes the buffer region a verbatim copy of `M₁`'s output, contiguous from the
initial head cell. If `M₁` never halts, neither does `M`. On `M₁`'s halting
transition, `M` rewinds the buffer head to the leftmost written cell — the head
rests on the blank immediately *right* of the written word, so the rewind's first
left move is unconditional (testing the current cell before moving would stop at the
wrong end; phase-4 audit, finding 3), then left while reading a symbol, then one
step right. Phase two simulates `M₂` with its *input-tape
reads served from the buffer*: the buffer holds exactly `y` with blank cells on both
sides, and `M` maintains `M₂`'s virtual input position on it, mirroring the clamped
input-head semantics of `Turing.moveInputPos` at both boundaries — the same
virtual-boundary emulation as the universal machine's sketch
(`TCSlib.Complexity.TuringMachine.Universal`); a blank read identifies a boundary,
and *which* boundary is determined by the direction of arrival, tracked in the
state — for an empty intermediate word the simulation starts with the right-boundary
tag already set, the left boundary one inward move away (phase-4 audit, finding 3).
`M₂`'s work-tape actions go to its own fresh tapes and its emissions to the
real output tape, untouched during phase one. `M` halts exactly when the simulated
`M₂` halts; step-for-step run correspondence in each phase gives both directions of
the iff.

**Implementation note (epoch 2).** The buffer and virtual-input invariants are
public in `Simulation.lean`. The arrival tag is constrained only at boundaries;
stationary moves preserve it, including suppressed outward moves. Dispatch always
sets it to true, which is already the right-boundary tag when the word is empty.
A simulated phase-one halt remains live through the exact `|y| + 2` rewind.
For the forward implication, phase-one divergence contradicts a completed run;
otherwise extend that completed run beyond the verified phase-two start using
absorbing halting, and recover the second completed computation by lockstep. -/
theorem exists_comp_partial (M₁ M₂ : FinTM Bool) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ y : List Bool,
          (∃ t, M₁.ComputesInTime x y t) ∧ ∃ t, M₂.ComputesInTime y w t := by
  classical
  refine ⟨bufferedCompTM M₁ M₂, fun x w => ?_⟩
  constructor
  · rintro ⟨t, ht⟩
    -- A divergent first component would keep every composite configuration live.
    have hh : ∃ s, (M₁.tm.runFrom (M₁.tm.initCfg x) s).state = none := by
      by_contra h
      have hr := bufferedFirstCfg_run M₁ M₂ (M₁.tm.initCfg x) t
        (fun s _ hs => h ⟨s, hs⟩)
      rw [← bufferedFirstCfg_init] at hr
      have hc := ((computesInTime_iff _ _ _ _).mp ht).1
      rw [hr] at hc
      simp only [bufferedFirstCfg, Option.some_ne_none] at hc
    obtain ⟨s, hs⟩ := hh
    let y := (M₁.tm.runFrom (M₁.tm.initCfg x) s).output
    have hy : M₁.ComputesInTime x y s := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
    obtain ⟨a, p, tapes, heads, _, ha⟩ := bufferedComp_start M₁ M₂ x y s hy
    -- Extend a completed run past the verified administrative prefix.
    have hc := (computesInTime_iff _ x w (a + t)).mp (ht.mono (by omega))
    rw [MultiTapeTM.runFrom_add, ha] at hc
    obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
      (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    rw [hr] at hc
    refine ⟨y, ⟨s, hy⟩, t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  · rintro ⟨y, ⟨s, hs⟩, ⟨t, ht⟩⟩
    obtain ⟨a, p, tapes, heads, _, ha⟩ := bufferedComp_start M₁ M₂ x y s hs
    obtain ⟨b, _, hr⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg y) true
      (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
    have hc := (computesInTime_iff _ _ _ _).mp ht
    refine ⟨a + t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    rw [MultiTapeTM.runFrom_add, ha, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩

/-- A finite controller runs `D` with its first emission captured in a register,
rewinds, then enters the selected branch on disjoint fresh tapes. A simulated halt
is represented by a live control state so that dispatch occurs only after `D` halts.
An empty register at dispatch halts safely. -/
private def condTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := D.k + (M₁.k + M₂.k)
  State := (Option D.State × Option Bool) ⊕ (Option Bool ⊕ (M₁.State ⊕ M₂.State))
  tm :=
    { q₀ := .inl (some D.tm.q₀, none)
      tr := fun q inp work => match q with
        | .inl (some q, reg) =>
          let a := D.tm.tr q inp (fun i => work (Fin.castAdd (M₁.k + M₂.k) i))
          ⟨a.inputTape, Fin.addCases a.workTapes (fun _ => (none, 0)), none,
            some (.inl (a.state, reg.or a.output))⟩
        | .inl (none, reg) => controlAction .neg (some (.inr (.inl reg)))
        | .inr (.inl reg) => match inp with
          | some _ => controlAction .neg (some (.inr (.inl reg)))
          | none => controlAction .pos
              (reg.map (fun b => .inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
        | .inr (.inr q) => rightAction D.k (fun s => .inr (.inr s))
            ((branchTM M₁ M₂ false).tm.tr q inp (fun i => work (Fin.natAdd D.k i))) }

/-- Embed a controller configuration with its output suppressed and the first
output symbol stored in the finite register. All branch tapes remain blank. -/
private def controlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) : Cfg (condTM D M₁ M₂).k Bool (condTM D M₁ M₂).State x where
  state := some (.inl (c.state, c.output.head?))
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes (fun _ _ => none)
  workTapePos := Fin.addCases c.workTapePos (fun _ => 0)
  output := []

/-- Before the simulated controller halts, one composite step exactly updates its
configuration and the first-emission register. The head-of-append identity makes
this invariant valid even without any assumption on the controller's output. -/
private lemma controlCfg_step (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (hs : c.state ≠ none) :
    (condTM D M₁ M₂).tm.step (controlCfg D M₁ M₂ c) =
      controlCfg D M₁ M₂ (D.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (controlCfg D M₁ M₂ c).state = some (.inl (some q, c.output.head?)) := by
      simp [controlCfg, hq]
    rw [hs']
    dsimp only [condTM]
    have hr : (fun i => (controlCfg D M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (M₁.k + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [controlCfg, Cfg.workTapeSymbols]
    have hi : (controlCfg D M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    refine Cfg.ext ?_ rfl ?_ ?_ ?_
    · simp [controlCfg, Action.apply, List.head?_append, Option.head?_toList]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg, Action.apply]
    · simp [controlCfg, Action.apply]

/-- Controller lockstep holds through its first halting step. Subsequent composite
steps perform the rewind, so no claim of lockstep after halting is made. -/
private lemma controlCfg_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (h : ∀ s, s < t → (D.tm.runFrom c s).state ≠ none) :
    (condTM D M₁ M₂).tm.runFrom (controlCfg D M₁ M₂ c) t =
      controlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      controlCfg_step D M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- A completed singleton controller computation reaches the selected branch's
fresh initial configuration after a finite prefix.

**Proof sketch.** Choose the first halting time of `D` and use controller lockstep.
Output uniqueness identifies its completed output with `[b]`, so the register is
`some b`, including when that bit was emitted early. Rewind from the resulting
input position; the branch tapes and real output have remained untouched. -/
private lemma condTM_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool)
    (hD : ∃ t, D.ComputesInTime x [b] t) :
    ∃ (t : ℕ) (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
        rightCfg (fun q => .inr (.inr q)) ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads := by
  classical
  obtain ⟨tD, hDc⟩ := hD
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨tD, ((computesInTime_iff D x [b] tD).mp hDc).1⟩
  let t := Nat.find hh
  let cf := D.tm.runFrom (D.tm.initCfg x) t
  have hstop : cf.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x cf.output t :=
    (computesInTime_iff D x cf.output t).mpr ⟨hstop, rfl⟩
  have hout : cf.output = [b] := hc.output_unique hDc
  have hi : (condTM D M₁ M₂).tm.initCfg x = controlCfg D M₁ M₂ (D.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [controlCfg]
  have hrun : (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) t =
      controlCfg D M₁ M₂ cf := by
    rw [hi]
    exact controlCfg_run D M₁ M₂ (D.tm.initCfg x) t (fun s hs => Nat.find_min hh hs)
  obtain ⟨r, hr⟩ := rewind_from_any (condTM D M₁ M₂).tm
    (.inl (none, some b)) (.inr (.inl (some b)))
    (some (.inr (.inr (branchTM M₁ M₂ b).tm.q₀)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (controlCfg D M₁ M₂ cf) (by simp [controlCfg, hstop, hout])
  refine ⟨t + r, cf.workTapes, cf.workTapePos, ?_⟩
  rw [MultiTapeTM.runFrom_add, hrun, hr]
  rfl

/-- **Branching on a decided predicate** — the second phase-4 combinator (phase-3
audit, round 2, Argument F, step 2 of the `HALT → UC` reduction): given a total
decider `D` for `p` and two branch machines, some machine behaves on every input
exactly as the branch selected by `p` does *on that same input*. The input tape is
read-only, so both branches see the original input.

**Proof sketch.** `D` computes the singleton output `[p x]` on every input, and
output is append-only, so along any run `D` emits exactly one symbol; simulate `D`
with that single emission recorded in a state register instead of emitted (no buffer
tape needed). On `D`'s halting transition, rewind the true input head to its initial
position: one step left, then left while reading a symbol, then one step right —
from any position this ends at input position `1`, the initial position, the clamp
at position `0` making the walk safe (including on empty input). Then transfer
control to a disjoint copy of `M₁` or `M₂` according to the register. The branches'
work tapes are fresh tapes `D` never touched, the output tape is untouched by phase
one, and the input head is back at its initial position, so the selected branch's
run is reproduced verbatim; determinism (`Turing.FinTM.ComputesInTime.output_unique`)
identifies `D`'s completed output with `[p x]`, so the selected branch is
`cond (p x) M₁ M₂`.

The implementation retains the first emission, with the exact invariant that the
register is the head of the simulated output. A live administrative state follows
the simulated halt before the first left move. For the forward implication, extend
any completed composite run beyond the verified branch-start prefix using absorbing
halting, then apply branch lockstep; the reverse implication concatenates that
prefix with the selected branch run. -/
theorem exists_cond (D M₁ M₂ : FinTM Bool) (p : List Bool → Bool)
    (hD : D.Computes fun x => [p x]) :
    ∃ M : FinTM Bool, ∀ x w : List Bool,
      (∃ t, M.ComputesInTime x w t) ↔
        ∃ t, (cond (p x) M₁ M₂).ComputesInTime x w t := by
  refine ⟨condTM D M₁ M₂, fun x w => ?_⟩
  obtain ⟨a, tapes, heads, ha⟩ := condTM_start D M₁ M₂ x (p x) (hD x)
  have hr (t : ℕ) :
      (condTM D M₁ M₂).tm.runFrom ((condTM D M₁ M₂).tm.initCfg x) (a + t) =
        rightCfg (fun q => .inr (.inr q))
          ((branchTM M₁ M₂ (p x)).tm.runFrom ((branchTM M₁ M₂ (p x)).tm.initCfg x) t)
          tapes heads := by
    rw [MultiTapeTM.runFrom_add, ha]
    exact rightCfg_run (branchTM M₁ M₂ (p x)).tm (condTM D M₁ M₂).tm
      (fun q => .inr (.inr q)) (fun _ _ _ => rfl) _ tapes heads t
  constructor
  · rintro ⟨t, ht⟩
    have hc := (computesInTime_iff (condTM D M₁ M₂) x w (a + t)).mp
      (ht.mono (by omega))
    rw [hr t] at hc
    have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x w t :=
      (computesInTime_iff _ x w t).mpr
        ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
    exact ⟨t, (branchTM_computes M₁ M₂ (p x) x w t).mp hb⟩
  · rintro ⟨t, ht⟩
    have hb := (computesInTime_iff (branchTM M₁ M₂ (p x)) x w t).mp
      ((branchTM_computes M₁ M₂ (p x) x w t).mpr ht)
    refine ⟨a + t, (computesInTime_iff _ x w (a + t)).mpr ?_⟩
    rw [hr t]
    exact ⟨by simpa only [rightCfg, Option.map_eq_none_iff] using hb.1, hb.2⟩

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.Sigma.Basic
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to one work tape

[AB09, Claim 1.6]: `k` work tapes are simulated by a single work tape with a quadratic
slowdown.

## Deviations from [AB09]

* [AB09]'s Claim 1.6 merges input, work, *and output* into one single tape (the
  standard model of Sipser's text). Our model structurally always has a separate
  read-only input tape and write-only output tape, so the faithful in-model rendering
  is **one work tape**: the interesting content — interleaving `k` tapes on one, with
  marked head positions and full sweeps — is identical, while the merged-single-tape
  model itself is out of scope (it is a different structure, not an instance of
  `MultiTapeTM`).
* [AB09] states the slowdown as `5k T(n)²`; we existentialize the constant and use
  `(T n + 1)²`.
* The retained structure is a genuinely different model from [AB09]'s merged one, not
  a notational variant: with a separate input tape, palindromes are decidable in
  linear time (`TCSlib.Complexity.ClassP.Examples`), while the merged single-tape
  model has an `Ω(n²)` lower bound for them ([AB09], chapter notes, citing Maass).
  Accordingly, the theorems below are *in-model analogues* of Claim 1.6, and no
  identification with the merged model is claimed anywhere in this development
  (phase-2 audit, finding 5).

## Main results

* `Turing.FinTM.one_work_tape` — [AB09, Claim 1.6] over an enlarged alphabet.
* `Turing.FinTM.one_work_tape_binary` — combined with alphabet reduction
  ([AB09, Claim 1.5]): one work tape *and* binary alphabet, still quadratic.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.6, p. 17; Remark 1.7.)
-/

namespace Turing.FinTM


/-- Add one unused work tape to a machine with no work tapes. -/
private def unusedTapeTM {Γ : Type} (M : FinTM Γ) (hk : M.k = 0) : FinTM Γ where
  k := 1
  State := M.State
  tm :=
    { q₀ := M.tm.q₀
      tr := fun q inp _ =>
        let a := M.tm.tr q inp (fun i => (Fin.cast hk i).elim0)
        ⟨a.inputTape, fun _ => (none, 0), a.output, a.state⟩ }

/-- The unused tape is blank and its head stays at the origin. -/
private def unusedTapeCfg {Γ : Type} (M : FinTM Γ) {x : List Γ}
    (c : Cfg M.k Γ M.State x) : Cfg 1 Γ M.State x :=
  ⟨c.state, c.inputPos, fun _ _ => none, fun _ => 0, c.output⟩

/-- The zero-tape embedding commutes with a single transition, including halt. -/
private lemma unusedTape_step {Γ : Type} (M : FinTM Γ) (hk : M.k = 0)
    {x : List Γ} (c : Cfg M.k Γ M.State x) :
    (unusedTapeTM M hk).tm.step (unusedTapeCfg M c) =
      unusedTapeCfg M (M.tm.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp only [unusedTapeCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (Fin.cast hk i).elim0) = c.workTapeSymbols := by
      funext i
      exact (Fin.cast hk i).elim0
    dsimp only [unusedTapeCfg]
    rw [hs]
    dsimp only [unusedTapeTM]
    rw [hw]
    apply Cfg.ext <;> rfl

/-- The zero-tape path is a lockstep simulation; no sweep or initialization is needed. -/
private lemma unusedTape_computes {Γ : Type} (M : FinTM Γ) (hk : M.k = 0)
    (f : List Γ → List Γ) (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    (unusedTapeTM M hk).ComputesFunInTime f T := by
  intro x
  have hr := MultiTapeTM.runFrom_comm_of_step (unusedTapeCfg M)
    (unusedTape_step M hk) (M.tm.initCfg x) (T x.length)
  have hi : unusedTapeCfg M (M.tm.initCfg x) = (unusedTapeTM M hk).tm.initCfg x := rfl
  rw [hi] at hr
  obtain ⟨hs, ho⟩ := (computesInTime_iff M x (f x) (T x.length)).mp (hM x)
  apply (computesInTime_iff _ _ _ _).mpr
  rw [hr]
  exact ⟨hs, ho⟩

/-- A finite tape zipper; the left list is stored nearest-cell first. -/
private def sweepTape {A : Type} (z : ℤ) (l r : List (Option A))
    (p : ℤ) : Option A :=
  if p < z then (l[(z - 1 - p).toNat]?).join else (r[(p - z).toNat]?).join

/-- Read the current cell of a zipper. -/
private lemma sweepTape_read {A : Type} (z : ℤ) (l r : List (Option A)) :
    sweepTape z l r z = r.head?.join := by
  simp only [sweepTape, lt_self_iff_false, ↓reduceIte, sub_self, Int.toNat_zero]
  cases r <;> rfl

/-- A write followed by a right move transfers one cell to the left stack.
**Proof sketch.** At the written coordinate both sides read the new symbol.
Strictly to its left or right, the old and new list indices differ by one,
exactly compensating for the cons or tail operation. -/
private lemma sweepTape_right {A : Type} (z : ℤ) (l r : List (Option A))
    (a b : Option A) :
    Function.update (sweepTape z l (a :: r)) z b =
      sweepTape (z + 1) (b :: l) r := by
  funext p
  by_cases hp : p = z
  · subst p
    simp [sweepTape]
  · rw [Function.update_of_ne hp]
    by_cases h : p < z
    · have h' : p < z + 1 := by omega
      have he : (z + 1 - 1 - p).toNat = (z - 1 - p).toNat + 1 := by omega
      simp only [sweepTape, if_pos h, if_pos h', he, List.getElem?_cons_succ]
    · have h' : ¬p < z + 1 := by omega
      have he : (p - z).toNat = (p - (z + 1)).toNat + 1 := by omega
      simp only [sweepTape, if_neg h, if_neg h', he, List.getElem?_cons_succ]

/-- A configuration at a sweep frontier, with arbitrary native input and output. -/
private def sweepCfg {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    Cfg 1 A S x := ⟨q, p, fun _ => sweepTape z l r, fun _ => z, out⟩

/-- A sweep's local write, with the native input and output left stationary. -/
private def sweepAct {A S : Type} (q : S) (a : Option A) (d : SignType) :
    Action 1 A S := ⟨0, fun _ => (some a, d), none, some q⟩

/-- The one-cell tape identity lifts to configurations. -/
private lemma sweepCfg_right {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (a b : Option A) :
    (sweepAct q' b .pos).apply (sweepCfg q p z l (a :: r) out) =
      sweepCfg (some q') p (z + 1) (b :: l) r out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i
    exact sweepTape_right z l r a b
  · funext i
    rfl
  · exact List.append_nil _

/-- A finite-state left-to-right transduction, recording both its final state
and its rewritten word. -/
private def sweepFold {R C : Type} (visit : R → C → R × C) (s : R) :
    List C → R × List C
  | [] => (s, [])
  | a :: as =>
    let v := visit s a
    let rest := sweepFold visit v.1 as
    (rest.1, v.2 :: rest.2)

/-- A local transition rule realizes a complete finite forward sweep.
**Proof sketch.** Induct on the unprocessed word. One machine step writes the
transduced first cell and moves it to the reversed left stack; the induction
hypothesis processes the tail. Input position and output are preserved at every
step, and the number of transitions is exactly the word length. -/
private lemma sweep_run {A S R C : Type} (tm : MultiTapeTM 1 A S)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .pos)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (sweepCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) as.length =
    sweepCfg (some (state (sweepFold visit s as).1)) p (z + as.length)
      (((sweepFold visit s as).2.map (fun a => some (symbol a))).reverse ++ l) r out := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil,
      MultiTapeTM.runFrom_zero, sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (sweepCfg (some (state s)) p z l
        (some (symbol a) :: (as.map (fun a => some (symbol a)) ++ r)) out).workTapeSymbols =
        fun _ => some (symbol a) := by
      funext i
      exact sweepTape_read z l _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [hr, htr]
    rw [sweepCfg_right, ih]
    simp only [sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- The same zipper viewed while scanning toward decreasing coordinates. -/
private def sweepRevCfg {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    Cfg 1 A S x :=
  ⟨q, p, fun _ w => sweepTape (-z) l r (-w), fun _ => z, out⟩

/-- Reflection converts the forward zipper identity into a left-moving step. -/
private lemma sweepRevCfg_left {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (a b : Option A) :
    (sweepAct q' b .neg).apply (sweepRevCfg q p z l (a :: r) out) =
      sweepRevCfg (some q') p (z - 1) (b :: l) r out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i w
    have h := congrFun (sweepTape_right (-z) l r a b) (-w)
    have he : -(z - 1) = -z + 1 := by omega
    change Function.update (fun w => sweepTape (-z) l (a :: r) (-w)) z b w =
      sweepTape (-(z - 1)) (b :: l) r (-w)
    simpa only [Function.update_apply, neg_inj, he] using h
  · funext i
    rfl
  · exact List.append_nil _

/-- The finite transduction lemma for the return sweep, with the exact cost. -/
private lemma sweep_run_reverse {A S R C : Type} (tm : MultiTapeTM 1 A S)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .neg)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (sweepRevCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) as.length =
    sweepRevCfg (some (state (sweepFold visit s as).1)) p (z - as.length)
      (((sweepFold visit s as).2.map (fun a => some (symbol a))).reverse ++ l) r out := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil,
      MultiTapeTM.runFrom_zero, sweepFold, Int.natCast_zero, sub_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (sweepRevCfg (some (state s)) p z l
        (some (symbol a) :: (as.map (fun a => some (symbol a)) ++ r)) out).workTapeSymbols =
        fun _ => some (symbol a) := by
      funext i
      exact sweepTape_read (-z) l _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [hr, htr, sweepRevCfg_left, ih]
    simp only [sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega

/-- Turning round exchanges the two finite stacks. -/
private lemma sweepTape_turn {A : Type} (z : ℤ) (l r : List (Option A)) :
    sweepTape z l r = fun w => sweepTape (-(z - 1)) r l (-w) := by
  funext w
  by_cases h : w < z
  · have h' : ¬ -w < -(z - 1) := by omega
    have he : -w - -(z - 1) = z - 1 - w := by omega
    simp only [sweepTape, if_pos h, if_neg h', he]
  · have h' : -w < -(z - 1) := by omega
    have he : -(z - 1) - 1 - -w = w - z := by omega
    simp only [sweepTape, if_neg h, if_pos h', he]

/-- Concatenating two scans threads the finite control between them. -/
private lemma sweepFold_append {R C : Type} (visit : R → C → R × C)
    (s : R) (as bs : List C) :
    sweepFold visit s (as ++ bs) =
      let first := sweepFold visit s as
      let second := sweepFold visit first.1 bs
      (second.1, first.2 ++ second.2) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, sweepFold, ih]

/-- A transducer whose state is a table, changing only the entry named by a cell. -/
private def indexedVisit {I V C : Type} [DecidableEq I]
    (visit : I → V → C → V × C) (s : I → V) (a : I × C) :
    (I → V) × (I × C) :=
  let v := visit a.1 (s a.1) a.2
  (Function.update s a.1 v.1, (a.1, v.2))

/-- On a block with distinct tape indices, each local rule sees the original
table entry. This is the block invariant for both sweeps.
**Proof sketch.** Induct on the index list. The first update does not affect
any remaining index because the list has no duplicates. For the final table,
split an arbitrary queried index into the first index, a tail member, or neither. -/
private lemma indexedFold {I V C : Type} [DecidableEq I]
    (visit : I → V → C → V × C) (cell : I → C) (is : List I) (hi : is.Nodup)
    (s : I → V) :
    sweepFold (indexedVisit visit) s (is.map (fun i => (i, cell i))) =
      (fun i => if i ∈ is then (visit i (s i) (cell i)).1 else s i,
        is.map (fun i => (i, (visit i (s i) (cell i)).2))) := by
  induction is generalizing s with
  | nil => simp [sweepFold]
  | cons i is ih =>
    obtain ⟨hin, ht⟩ := List.nodup_cons.mp hi
    simp only [List.map_cons, sweepFold, indexedVisit]
    rw [ih ht]
    apply Prod.ext
    · funext j
      by_cases hj : j = i
      · subst j
        simp [hin]
      · simp only [Function.update_of_ne hj, List.mem_cons]
        by_cases hm : j ∈ is <;> simp [hj, hm]
    · dsimp only
      congr 1
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := by rintro rfl; exact hin hj
      simp only [Function.update_of_ne hji]

/-- Each simulated tape contributes exactly one cell to an interleaved block. -/
private lemma indexedFold_block {k : ℕ} {V C : Type}
    (visit : Fin k → V → C → V × C) (cell : Fin k → C) (s : Fin k → V) :
    sweepFold (indexedVisit visit) s ((List.finRange k).map (fun i => (i, cell i))) =
      (fun i => (visit i (s i) (cell i)).1,
        (List.finRange k).map (fun i => (i, (visit i (s i) (cell i)).2))) := by
  simpa only [List.mem_finRange, ↓reduceIte] using
    indexedFold visit cell (List.finRange k) (List.nodup_finRange k) s

/-- A cell stores a tape index, an optional payload, the head flag, and the
left-neighbor head flag recorded by the forward sweep. -/
private abbrev SweepCell (Γ : Type) (k : ℕ) := Fin k × (Option Γ × Bool × Bool)

/-- The forward rule reads marked payloads and records the preceding head flag. -/
private def readVisit {Γ : Type} {k : ℕ} :
    (Fin k → Option Γ × Bool) → SweepCell Γ k →
      (Fin k → Option Γ × Bool) × SweepCell Γ k :=
  indexedVisit fun _ s a => ((if a.2.1 then a.1 else s.1, a.2.1),
    (a.1, a.2.1, s.2))

/-- The return rule writes the old head's payload and determines the new head
from the old flags at its left, current, and right neighbors. -/
private def writeVisit {Γ S : Type} {k : ℕ} (act : Action k Γ S) :
    (Fin k → Bool) → SweepCell Γ k → (Fin k → Bool) × SweepCell Γ k :=
  indexedVisit fun i right a =>
    (a.2.1, (if a.2.1 then (act.workTapes i).1.getD a.1 else a.1,
      (match (act.workTapes i).2 with
        | .neg => right
        | .zero => a.2.1
        | .pos => a.2.2), false))

/-- The ghost head flag at a source coordinate. -/
private def headAt {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (i : Fin k) (j : ℤ) : Bool := decide (c.workTapePos i = j)

/-- One interleaved block; `read = true` includes the recorded left flag. -/
private def tapeRow {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (read : Bool) : List (SweepCell Γ k) :=
  (List.finRange k).map fun i =>
    (i, c.workTapes i j, headAt c i j, if read then headAt c i (j - 1) else false)

/-- The forward control immediately before reading block `j`. -/
private def readState {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) : Fin k → Option Γ × Bool := fun i =>
  (if c.workTapePos i < j then c.workTapeSymbols i else none, headAt c i (j - 1))

/-- Reading a whole block advances the control invariant by one coordinate. -/
private lemma read_row {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) :
    sweepFold readVisit (readState c j) (tapeRow c j false) =
      (readState c (j + 1), tapeRow c j true) := by
  unfold readVisit tapeRow
  rw [indexedFold_block]
  apply Prod.ext
  · funext i
    dsimp only [readState]
    apply Prod.ext
    · dsimp only
      by_cases he : c.workTapePos i = j
      · simp [headAt, he, Cfg.workTapeSymbols]
      · have hlt : c.workTapePos i < j + 1 ↔ c.workTapePos i < j := by omega
        simp [headAt, he, hlt]
    · simp [headAt]
  · rfl

/-- The return sweep's block rule is valid in reverse tape-index order too. -/
private lemma indexedFold_block_reverse {k : ℕ} {V C : Type}
    (visit : Fin k → V → C → V × C) (cell : Fin k → C) (s : Fin k → V) :
    sweepFold (indexedVisit visit) s (((List.finRange k).map (fun i => (i, cell i))).reverse) =
      (fun i => (visit i (s i) (cell i)).1,
        ((List.finRange k).map (fun i => (i, (visit i (s i) (cell i)).2))).reverse) := by
  rw [← List.map_reverse, ← List.map_reverse]
  simpa only [List.mem_reverse, List.mem_finRange, ↓reduceIte] using
    indexedFold visit cell (List.finRange k).reverse
      (by simpa using List.nodup_finRange k) s

/-- A return-sweep block performs exactly the source action on that coordinate.
**Proof sketch.** A payload changes only at its old head. A new head at `j`
comes from `j+1`, `j`, or `j-1`, according to its movement; these are exactly
the right-control, current-cell, and stored-left flags. -/
private lemma write_row {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (act : Action k Γ S) (j : ℤ) :
    sweepFold (writeVisit act) (fun i => headAt c i (j + 1)) (tapeRow c j true).reverse =
      (fun i => headAt c i j, (tapeRow (act.apply c) j false).reverse) := by
  unfold writeVisit tapeRow
  rw [indexedFold_block_reverse]
  apply Prod.ext
  · rfl
  · dsimp only
    congr 1
    apply List.map_congr_left
    intro i _
    refine Prod.ext (by rfl) ?_
    apply Prod.ext
    · dsimp only
      by_cases he : c.workTapePos i = j
      · cases hw : (act.workTapes i).1 <;>
          simp [headAt, he, Action.apply, hw, Function.update_apply]
      · have he' : j ≠ c.workTapePos i := Ne.symm he
        cases hw : (act.workTapes i).1 <;> simp [headAt, he, he', Action.apply, hw]
    · dsimp only
      refine Prod.ext ?_ (by rfl)
      dsimp only
      cases hm : (act.workTapes i).2 <;>
        simp only [headAt, Action.apply, hm, SignType.cast]
      all_goals simp only [↓reduceIte, decide_eq_decide]; omega

/-- Consecutive interleaved blocks, in ascending coordinate order. -/
private def tapeZone {C : Type} (row : ℤ → List C) (j : ℤ) : ℕ → List C
  | 0 => []
  | n + 1 => row j ++ tapeZone row (j + 1) n

/-- The forward sweep processes any consecutive block interval. -/
private lemma read_zone {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (n : ℕ) :
    sweepFold readVisit (readState c j) (tapeZone (fun z => tapeRow c z false) j n) =
      (readState c (j + n), tapeZone (fun z => tapeRow c z true) j n) := by
  induction n generalizing j with
  | zero => simp [tapeZone, sweepFold]
  | succ n ih =>
    simp only [tapeZone, sweepFold_append, read_row, ih]
    congr 2
    omega

/-- The return sweep processes the same interval in reverse order. -/
private lemma write_zone {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (act : Action k Γ S) (j : ℤ) (n : ℕ) :
    sweepFold (writeVisit act) (fun i => headAt c i (j + n))
      (tapeZone (fun z => tapeRow c z true) j n).reverse =
      (fun i => headAt c i j,
        (tapeZone (fun z => tapeRow (act.apply c) z false) j n).reverse) := by
  induction n generalizing j with
  | zero => simp [tapeZone, sweepFold]
  | succ n ih =>
    have he : j + (n + 1 : ℕ) = j + 1 + n := by omega
    simp only [tapeZone, List.reverse_append, sweepFold_append, he, ih]
    rw [write_row]

/-- One blank cell can be made explicit at the end of the zipper. -/
private lemma sweepTape_nil {A : Type} (z : ℤ) (l : List (Option A)) :
    sweepTape z l [] = sweepTape z l [none] := by
  funext p
  unfold sweepTape
  split
  · rfl
  · cases (p - z).toNat <;> rfl

/-- The forward write identity also applies beyond the stored zone. -/
private lemma sweepCfg_right_any {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .pos).apply (sweepCfg q p z l r out) =
      sweepCfg (some q') p (z + 1) (b :: l) r.tail out := by
  cases r with
  | cons a r => exact sweepCfg_right q q' p z l r out a b
  | nil =>
    have hc : sweepCfg q p z l ([] : List (Option A)) out =
        sweepCfg q p z l [none] out := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i
      exact sweepTape_nil z l
    rw [hc]
    exact sweepCfg_right q q' p z l [] out none b

/-- The backward write identity also applies beyond the stored zone. -/
private lemma sweepRevCfg_left_any {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .neg).apply (sweepRevCfg q p z l r out) =
      sweepRevCfg (some q') p (z - 1) (b :: l) r.tail out := by
  cases r with
  | cons a r => exact sweepRevCfg_left q q' p z l r out a b
  | nil =>
    have hc : sweepRevCfg q p z l ([] : List (Option A)) out =
        sweepRevCfg q p z l [none] out := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i w
      exact congrFun (sweepTape_nil (-z) l) (-w)
    rw [hc]
    exact sweepRevCfg_left q q' p z l [] out none b

/-- A fixed finite sequence of writes, in either direction, takes its exact
length. The hypothesis is the local controller rule, and has no global-run premise. -/
private lemma sweep_generate {A S : Type} {x : List A}
    (tm : MultiTapeTM 1 A S) (w : List A)
    (cfg : Fin (w.length + 1) → ℤ → List (Option A) → List (Option A) → Cfg 1 A S x)
    (d : ℤ)
    (hstep : ∀ (i : ℕ) (hi : i < w.length) z l r,
      tm.step (cfg ⟨i, by omega⟩ z l r) =
        cfg ⟨i + 1, by omega⟩ (z + d) (some w[i] :: l) r.tail)
    (z : ℤ) (l r : List (Option A)) (n : ℕ) (hn : n ≤ w.length) :
    tm.runFrom (cfg 0 z l r) n =
      cfg ⟨n, by omega⟩ (z + d * n) ((w.take n).map some |>.reverse |>.append l)
        (r.drop n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), hstep n (by omega)]
    have hz : z + d * n + d = z + d * (n + 1 : ℕ) := by push_cast; ring
    rw [hz, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, ← List.drop_one, List.drop_drop]
    rfl

/-- An enlarged symbol is input/output data, an internal cell, or a boundary. -/
private abbrev SweepAlphabet (Γ : Type) (k : ℕ) := Γ ⊕ Option (SweepCell Γ k)

/-- Encode a source symbol as an unmarked data symbol. -/
private def sweepEmbed (Γ : Type) (k : ℕ) : Γ ↪ SweepAlphabet Γ k :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- A nonblank internal boundary, distinct from every payload (including blank). -/
private def sweepBoundary {Γ : Type} {k : ℕ} : SweepAlphabet Γ k := .inr none

/-- Tag a complete internal cell. -/
private def sweepSymbol {Γ : Type} {k : ℕ} (c : SweepCell Γ k) : SweepAlphabet Γ k :=
  .inr (some c)

/-- Interpret the unchanged native input alphabet. -/
private def sweepInput {Γ : Type} {k : ℕ} : Option (SweepAlphabet Γ k) → Option Γ
  | some (.inl a) => some a
  | _ => none

/-- Finite controller phases; unbounded coordinates never enter the state. -/
private inductive SweepState (Γ S : Type) (k : ℕ) where
  | init : Fin (k + 1) → SweepState Γ S k
  | back : SweepState Γ S k
  | growLeft : S → Fin (k + 1) → SweepState Γ S k
  | read : S → (Fin k → Option Γ × Bool) → SweepState Γ S k
  | growRight : S → (Fin k → Option Γ × Bool) → Fin (k + 1) → SweepState Γ S k
  | write : S → Option Γ → (Fin k → Option Γ) → (Fin k → Bool) → SweepState Γ S k

/-- Enumerate the finite control through its finite sum/product representation. -/
private instance sweepStateFintype (Γ S : Type) [Fintype Γ] [Fintype S] (k : ℕ) :
    Fintype (SweepState Γ S k) := derive_fintype% _

/-- Equality of controller states is decidable through the same representation. -/
private instance sweepStateDecidableEq (Γ S : Type) [DecidableEq Γ] [DecidableEq S] (k : ℕ) :
    DecidableEq (SweepState Γ S k) :=
  -- The nested sum/sigma representation exceeds the default instance-size bound.
  set_option synthInstance.maxSize 8192 in
  (proxy_equiv% (SweepState Γ S k)).symm.decidableEq

/-- A stationary-input/output action that preserves the cell it scans. -/
private def sweepMove {A S : Type} (q : Option S) (d : SignType) : Action 1 A S :=
  ⟨0, fun _ => (none, d), none, q⟩

/-- The finite controller for the two sweeps and their boundary extensions.
The forward sweep records left-neighbor flags in the cells. The backward sweep
keeps right-neighbor flags in its control, so it needs no extra scan. -/
private def sweepTM {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) : FinTM (SweepAlphabet Γ M.k) where
  k := 1
  State := SweepState Γ M.State M.k
  tm :=
    { q₀ := .init 0
      tr := fun q inp work =>
        match q with
        | .init i =>
          if h : i.val < M.k then
            sweepAct (.init ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨i.val, h⟩, none, true, false))) .pos
          else
            sweepAct .back (some sweepBoundary) .neg
        | .back =>
          match work 0 with
          | none => sweepAct (.growLeft M.tm.q₀ 0) (some sweepBoundary) .zero
          | some a => sweepAct .back (some a) .neg
        | .growLeft q i =>
          if h : i.val < M.k then
            sweepAct (.growLeft q ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨M.k - 1 - i.val, by omega⟩, none, false, false))) .neg
          else
            sweepAct (.read q (fun _ => (none, false))) (some sweepBoundary) .pos
        | .read q s =>
          match work 0 with
          | some (.inr (some c)) =>
            let v := readVisit s c
            sweepAct (.read q v.1) (some (sweepSymbol v.2)) .pos
          | _ => sweepMove (some (.growRight q s 0)) .zero
        | .growRight q s i =>
          if h : i.val < M.k then
            sweepAct (.growRight q s ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨i.val, h⟩, none, false, (s ⟨i.val, h⟩).2))) .pos
          else
            let a := M.tm.tr q (sweepInput inp) (fun i => (s i).1)
            ⟨a.inputTape, fun _ => (some (some sweepBoundary), .neg),
              a.output.map Sum.inl,
              some (.write q (sweepInput inp) (fun i => (s i).1) (fun _ => false))⟩
        | .write q inp reads right =>
          let a := M.tm.tr q inp reads
          match work 0 with
          | some (.inr (some c)) =>
            let v := writeVisit a right c
            sweepAct (.write q inp reads v.1) (some (sweepSymbol v.2)) .neg
          | _ => sweepMove (a.state.map (fun q => .growLeft q 0)) .zero }

/-- Source heads and nonblank cells stay within the elapsed-time interval.
**Proof sketch.** Heads start at zero and move by at most one per step.
A write can only change the cell under an old head, so it cannot create a
nonblank cell outside the larger interval at the next time. -/
private lemma source_bounds {Γ : Type} (M : FinTM Γ) (x : List Γ) (t : ℕ) :
    (∀ i, -(t : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ t) ∧
    (∀ i z, z < -(t : ℤ) ∨ (t : ℤ) < z →
      (M.tm.runFrom (M.tm.initCfg x) t).workTapes i z = none) := by
  induction t with
  | zero => simp [MultiTapeTM.initCfg, Cfg.init]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    constructor
    · intro i
      have hp := M.tm.workTapePos_step_le (M.tm.runFrom (M.tm.initCfg x) t) i
      rw [abs_le] at hp
      have := ih.1 i
      push_cast
      omega
    · intro i z hz
      have hz' : z < -(t : ℤ) ∨ (t : ℤ) < z := by omega
      have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i := by
        have := ih.1 i
        omega
      unfold MultiTapeTM.step
      cases hs : (M.tm.runFrom (M.tm.initCfg x) t).state with
      | none => exact ih.2 i z hz'
      | some q =>
        dsimp only [Action.apply]
        cases hw : ((M.tm.tr q (M.tm.runFrom (M.tm.initCfg x) t).inputSymbol
          (M.tm.runFrom (M.tm.initCfg x) t).workTapeSymbols).workTapes i).1
        · exact ih.2 i z hz'
        · dsimp only
          rw [Function.update_of_ne hne]
          exact ih.2 i z hz'

/-- The initialized interleaving has `k` marked blank cells. -/
private def blankRow {Γ : Type} (k : ℕ) (mark : Bool) : List (SweepCell Γ k) :=
  (List.finRange k).map fun i => (i, none, mark, false)

/-- A row outside both the source heads and the written support is blank. -/
private lemma tapeRow_blank {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (hp : ∀ i, c.workTapePos i ≠ j)
    (ht : ∀ i, c.workTapes i j = none) :
    tapeRow c j false = blankRow k false := by
  unfold tapeRow blankRow
  apply List.map_congr_left
  intro i _
  simp [headAt, hp i, ht i]

/-- The size of each block is the number of source tapes. -/
private lemma tapeRow_length {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (b : Bool) : (tapeRow c j b).length = k := by
  simp [tapeRow]

/-- Zone length is the block count times the source tape count. -/
private lemma tapeZone_length {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (n : ℕ) (b : Bool) :
    (tapeZone (fun z => tapeRow c z b) j n).length = n * k := by
  induction n generalizing j with
  | zero => simp [tapeZone]
  | succ n ih =>
    simp only [tapeZone, List.length_append, tapeRow_length, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- Split a zone at a block boundary. -/
private lemma tapeZone_append {C : Type} (row : ℤ → List C) (j : ℤ) (n m : ℕ) :
    tapeZone row j (n + m) = tapeZone row j n ++ tapeZone row (j + n) m := by
  induction n generalizing j with
  | zero => simp [tapeZone]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [tapeZone, ih, List.append_assoc]
    rw [show j + 1 + (n : ℤ) = j + (n + 1 : ℕ) by omega]

/-- The native input position is unchanged numerically by symbol embedding. -/
private def sweepPos {Γ : Type} {x : List Γ} (k : ℕ) (p : Fin (x.length + 2)) :
    Fin ((x.map (sweepEmbed Γ k)).length + 2) :=
  ⟨p.val, by simpa only [List.length_map] using p.isLt⟩

/-- Input-head movement commutes with the unchanged-length symbol embedding. -/
private lemma sweepPos_move {Γ : Type} {x : List Γ} (k : ℕ)
    (p : Fin (x.length + 2)) (d : SignType) :
    moveInputPos (sweepPos k p) d = sweepPos k (moveInputPos p d) := by
  apply Fin.ext
  simp only [moveInputPos, sweepPos, List.length_map]
  split <;> rfl

/-- The input read by an encoded configuration is the encoded source read. -/
private lemma sweepInput_read {Γ S S' : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (d : Cfg 1 (SweepAlphabet Γ k) S' (x.map (sweepEmbed Γ k)))
    (hp : d.inputPos = sweepPos k c.inputPos) :
    sweepInput d.inputSymbol = c.inputSymbol := by
  have hzero : sweepPos k c.inputPos = 0 ↔ c.inputPos = 0 := by
    simp only [Fin.ext_iff, sweepPos, Fin.val_zero]
  have hv : (sweepPos k c.inputPos).val = c.inputPos.val := rfl
  simp only [Cfg.inputSymbol, hp, hzero, hv, List.length_map]
  split
  · rfl
  · split
    · rfl
    · simp only [List.getElem_map, sweepEmbed, Function.Embedding.coeFn_mk, sweepInput]

/-- Canonical configurations at the left boundary between simulated steps. -/
private def sweepStart {Γ : Type} [Fintype Γ] [DecidableEq Γ] (M : FinTM Γ)
    {x : List Γ} (c : Cfg M.k Γ M.State x) (j : ℤ) (n : ℕ) (z : ℤ) :
    Cfg 1 (SweepAlphabet Γ M.k) (SweepState Γ M.State M.k)
      (x.map (sweepEmbed Γ M.k)) :=
  sweepRevCfg (c.state.map (fun q => .growLeft q 0)) (sweepPos M.k c.inputPos) z
    ((tapeZone (fun j => tapeRow c j false) j n).map (fun a => some (sweepSymbol a)) ++
      [some sweepBoundary]) [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k))

/-- Replacing the current cell preserves both tails of the zipper. -/
private lemma sweepTape_write {A : Type} (z : ℤ) (l r : List (Option A)) (b : Option A) :
    Function.update (sweepTape z l r) z b = sweepTape z l (b :: r.tail) := by
  funext p
  by_cases hp : p = z
  · subst p
    simp [sweepTape_read]
  · rw [Function.update_of_ne hp]
    by_cases h : p < z
    · simp only [sweepTape, if_pos h]
    · have he : (p - z).toNat = (p - z - 1).toNat + 1 := by omega
      simp only [sweepTape, if_neg h, he, List.getElem?_cons_succ]
      cases r <;> rfl

/-- Write a boundary and turn from a forward scan into a backward scan. -/
private lemma sweep_turn_left {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b emit : Option A) (di : SignType) :
    (⟨di, fun _ => (some b, .neg), emit, q'⟩ : Action 1 A S).apply
      (sweepCfg q p z l r out) =
    sweepRevCfg q' (moveInputPos p di) (z - 1) (b :: r.tail) l (out ++ emit.toList) := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i w
  change Function.update (sweepTape z l r) z b w = _
  rw [sweepTape_write, sweepTape_turn]
  rfl

/-- Write the left boundary and turn toward the first forward-scan cell. -/
private lemma sweep_turn_right {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .pos).apply (sweepRevCfg q p z l r out) =
      sweepCfg (some q') p (z + 1) (b :: r.tail) l out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ rfl (List.append_nil _)
  funext i w
  have h := congrFun (sweepTape_write (-z) l r b) (-w)
  have ht := congrFun (sweepTape_turn (z + 1) (b :: r.tail) l) w
  have he : z + 1 - 1 = z := by omega
  rw [he] at ht
  change Function.update (fun w => sweepTape (-z) l r (-w)) z b w =
    sweepTape (z + 1) (b :: r.tail) l w
  rw [ht]
  simpa only [Function.update_apply, neg_inj] using h

/-- Initialization writes the marked origin block in exactly `k` steps. -/
private lemma sweep_init_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepCfg (some (.init 0)) p z l r out) M.k =
      sweepCfg (some (.init ⟨M.k, by omega⟩)) p (z + M.k)
        (((blankRow M.k true).map (fun a => some (sweepSymbol a))).reverse ++ l)
        (r.drop M.k) out := by
  let w := (blankRow (Γ := Γ) M.k true).map sweepSymbol
  have hw : w.length = M.k := by simp [w, blankRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepCfg (some (.init ⟨i.val, by simpa [hw] using i.isLt⟩)) p z l r out)
    1 (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_map] using h
  · have hik : i < M.k := by omega
    change (sweepTM M).tm.step (sweepCfg (some (.init ⟨i, by omega⟩)) p z l r out) = _
    change ((sweepTM M).tm.tr (.init ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨i, hik⟩, none, true, false) := by
      simp [w, blankRow]
    rw [he]
    exact sweepCfg_right_any _ _ p z l r out _

/-- Growing the left boundary writes exactly one reversed blank block. -/
private lemma sweep_grow_left_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (q : M.State) {x : List (SweepAlphabet Γ M.k)}
    (p : Fin (x.length + 2)) (out : List (SweepAlphabet Γ M.k))
    (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepRevCfg (some (.growLeft q 0)) p z l r out) M.k =
      sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
        ((blankRow M.k false).map (fun a => some (sweepSymbol a)) ++ l)
        (r.drop M.k) out := by
  let w := ((blankRow (Γ := Γ) M.k false).map sweepSymbol).reverse
  have hw : w.length = M.k := by simp [w, blankRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepRevCfg (some (.growLeft q ⟨i.val, by simpa [hw] using i.isLt⟩))
      p z l r out) (-1) (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_reverse, List.map_map, sub_eq_add_neg] using h
  · have hik : i < M.k := by omega
    change (sweepTM M).tm.step (sweepRevCfg (some (.growLeft q ⟨i, by omega⟩)) p z l r out) = _
    change ((sweepTM M).tm.tr (.growLeft q ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨M.k - 1 - i, by omega⟩, none, false, false) := by
      simp [w, blankRow, List.getElem_reverse]
    rw [he]
    exact sweepRevCfg_left_any _ _ p z l r out _

/-- The right guard block records the flags from the last scanned block. -/
private def rightRow {Γ : Type} {k : ℕ} (s : Fin k → Option Γ × Bool) :
    List (SweepCell Γ k) := (List.finRange k).map fun i => (i, none, false, (s i).2)

/-- Growing the right boundary writes one guard block, retaining the collected reads. -/
private lemma sweep_grow_right_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (q : M.State) (s : Fin M.k → Option Γ × Bool)
    {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepCfg (some (.growRight q s 0)) p z l r out) M.k =
      sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        (((rightRow s).map (fun a => some (sweepSymbol a))).reverse ++ l)
        (r.drop M.k) out := by
  let w := (rightRow s).map sweepSymbol
  have hw : w.length = M.k := by simp [w, rightRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepCfg (some (.growRight q s ⟨i.val, by simpa [hw] using i.isLt⟩))
      p z l r out) 1 (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_map] using h
  · have hik : i < M.k := by omega
    change ((sweepTM M).tm.tr (.growRight q s ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨i, hik⟩, none, false, (s ⟨i, hik⟩).2) := by
      simp [w, rightRow]
    rw [he]
    exact sweepCfg_right_any _ _ p z l r out _

/-- A sweep with the identity rule only changes the physical scan frontier. -/
private lemma sweepFold_id {R C : Type} (s : R) (as : List C) :
    sweepFold (fun s a => (s, a)) s as = (s, as) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [sweepFold, ih]

/-- Writing without moving in a backward-facing zipper. -/
private lemma sweepRevCfg_write {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .zero).apply (sweepRevCfg q p z l r out) =
      sweepRevCfg (some q') p z l (b :: r.tail) out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i w
    have h := congrFun (sweepTape_write (-z) l r b) (-w)
    change Function.update (fun w => sweepTape (-z) l r (-w)) z b w = _
    simpa only [Function.update_apply, neg_inj] using h
  · funext i
    exact add_zero z

/-- Initialization builds the marked origin block and both boundaries.
**Proof sketch.** Write `k` marked blank cells, write the right boundary and
turn left, traverse the same `k` cells without altering them, then write the
left boundary. All four phases preserve the native input and output. -/
private lemma sweep_init {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List Γ) :
    (sweepTM M).tm.runFrom ((sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k))) (2 * M.k + 2) =
      sweepStart M (M.tm.initCfg x) 0 1 (-1) := by
  let p := sweepPos M.k (M.tm.initCfg x).inputPos
  let B := (blankRow (Γ := Γ) M.k true).map (fun a => some (sweepSymbol a))
  have hlen : (blankRow (Γ := Γ) M.k true).length = M.k := by simp [blankRow]
  have hp : p = 1 := by apply Fin.ext; simp [p, sweepPos]
  have hinit : (sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k)) =
      sweepCfg (some (.init 0)) p 0 [] [] [] := by
    refine Cfg.ext rfl hp.symm ?_ rfl rfl
    funext i z
    simp [sweepCfg, sweepTape]
  have hturn : (sweepTM M).tm.step
      (sweepCfg (some (.init ⟨M.k, by omega⟩)) p M.k B.reverse [] []) =
      sweepRevCfg (some .back) p ((M.k : ℤ) - 1) [some sweepBoundary] B.reverse [] := by
    change ((sweepTM M).tm.tr (.init ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    simpa only [sweepAct, SignType.zero_eq_zero, moveInputPos_zero, List.tail_nil,
      Option.toList_none, List.append_nil] using
      sweep_turn_left (S := SweepState Γ M.State M.k)
        (some (.init ⟨M.k, by omega⟩)) (some .back) p (M.k : ℤ)
        B.reverse [] [] (some sweepBoundary) none .zero
  have hback := sweep_run_reverse (sweepTM M).tm (fun _ : Unit => SweepState.back)
    sweepSymbol (fun s a => (s, a)) (by intro s a inp; rfl) p []
    (blankRow (Γ := Γ) M.k true).reverse () ((M.k : ℤ) - 1) [some sweepBoundary] []
  have hback' : (sweepTM M).tm.runFrom
      (sweepRevCfg (some .back) p ((M.k : ℤ) - 1) [some sweepBoundary] B.reverse []) M.k =
      sweepRevCfg (some .back) p (-1) (B ++ [some sweepBoundary]) [] [] := by
    simpa [B, List.map_reverse, hlen, sweepFold_id] using hback
  have hlast : (sweepTM M).tm.step
      (sweepRevCfg (some .back) p (-1) (B ++ [some sweepBoundary]) [] []) =
      sweepRevCfg (some (.growLeft M.tm.q₀ 0)) p (-1)
        (B ++ [some sweepBoundary]) [some sweepBoundary] [] := by
    have hr : (sweepRevCfg (some (SweepState.back (Γ := Γ) (S := M.State) (k := M.k)))
        p (-1) (B ++ [some sweepBoundary]) [] []).workTapeSymbols = fun _ => none := by
      funext i
      simp [Cfg.workTapeSymbols, sweepRevCfg, sweepTape]
    change ((sweepTM M).tm.tr .back _ _).apply _ = _
    rw [hr]
    exact sweepRevCfg_write _ _ _ _ _ _ _ _
  rw [show 2 * M.k + 2 = (M.k + 1) + M.k + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step', hinit, sweep_init_block]
  simp only [zero_add, List.append_nil, List.drop_nil]
  rw [hturn, hback', hlast]
  congr 1
  simp [tapeZone, tapeRow, blankRow, headAt, B]

/-- A stationary phase change preserves a forward-facing tape. -/
private lemma sweepCfg_stay {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepMove q' .zero).apply (sweepCfg q p z l r out) = sweepCfg q' p z l r out := by
  apply Cfg.ext <;> simp [sweepMove, sweepCfg, Action.apply]

/-- A stationary phase change preserves a backward-facing tape. -/
private lemma sweepRevCfg_stay {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepMove q' .zero).apply (sweepRevCfg q p z l r out) = sweepRevCfg q' p z l r out := by
  apply Cfg.ext <;> simp [sweepMove, sweepRevCfg, Action.apply]

/-- The first half of a simulated step grows the left guard and collects all
marked source symbols. Its exact cost includes both phase changes.
**Proof sketch.** The head lower bound makes the new left block blank and gives
the empty initial read table. Write that block, place the new boundary, and turn.
The forward transduction processes all blocks through the old right edge,
recording the marked symbols and left-neighbor flags. A stationary boundary
transition enters the right-extension phase. Concatenate these four runs. -/
private lemma sweep_prepare {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (hs : c.state = some q) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, a ≤ c.workTapePos i)
    (hl : ∀ i, c.workTapes i (a - 1) = none) :
    (sweepTM M).tm.runFrom (sweepStart M c a n z)
      (M.k + 1 + (n + 1) * M.k + 1) =
    sweepCfg (some (.growRight q (readState c (a + n)) 0)) (sweepPos M.k c.inputPos)
      (z - M.k + 1 + ((n + 1) * M.k : ℕ))
      (((tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)).map
        (fun b => some (sweepSymbol b))).reverse ++ [some sweepBoundary])
      [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)) := by
  let p := sweepPos M.k c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let D := (tapeZone (fun j => tapeRow c j false) a n).map (fun b => some (sweepSymbol b))
  let F := tapeZone (fun j => tapeRow c j false) (a - 1) (n + 1)
  let R := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)
  have hf : F = blankRow M.k false ++ tapeZone (fun j => tapeRow c j false) a n := by
    dsimp [F]
    rw [tapeZone, show a - 1 + 1 = a by omega,
      tapeRow_blank c (a - 1) (fun i => by have := hp i; omega) hl]
  have hr0 : readState c (a - 1) = fun _ => (none, false) := by
    funext i
    have h := hp i
    simp only [readState, headAt]
    rw [if_neg (by omega)]
    simp [show c.workTapePos i ≠ a - 1 - 1 by omega]
  have hdrop : ([some (sweepBoundary (Γ := Γ) (k := M.k))] : List _).drop M.k = [] := by
    apply List.drop_eq_nil_of_le
    simpa using hk
  have hturn : (sweepTM M).tm.step
      (sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
        ((blankRow M.k false).map (fun b => some (sweepSymbol b)) ++ (D ++ [some sweepBoundary]))
        [] out) =
      sweepCfg (some (.read q (readState c (a - 1)))) p (z - M.k + 1)
        [some sweepBoundary] (F.map (fun b => some (sweepSymbol b)) ++ [some sweepBoundary]) out := by
    change ((sweepTM M).tm.tr (.growLeft q ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    rw [sweep_turn_right]
    simp only [hr0, hf, List.map_append, List.append_assoc, D, List.tail_nil]
  have hread := sweep_run (sweepTM M).tm (fun s => SweepState.read q s) sweepSymbol readVisit
    (by intro s b inp; rfl) p out F (readState c (a - 1)) (z - M.k + 1)
    [some sweepBoundary] [some sweepBoundary]
  have hfold : sweepFold readVisit (readState c (a - 1)) F =
      (readState c (a + n), R) := by
    simpa [F, R, show a - 1 + (n + 1 : ℕ) = a + n by omega] using
      read_zone c (a - 1) (n + 1)
  have hflen : F.length = (n + 1) * M.k := tapeZone_length c _ _ _
  rw [hfold, hflen] at hread
  have hend : (sweepTM M).tm.step
      (sweepCfg (some (.read q (readState c (a + n)))) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out) =
      sweepCfg (some (.growRight q (readState c (a + n)) 0)) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out := by
    have hsym : (sweepCfg (some (SweepState.read q (readState c (a + n)))) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out).workTapeSymbols = fun _ => some sweepBoundary := by
      funext i
      exact sweepTape_read _ _ _
    change ((sweepTM M).tm.tr (.read q (readState c (a + n))) _ _).apply _ = _
    rw [hsym]
    exact sweepCfg_stay _ _ _ _ _ _ _
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step']
  unfold sweepStart
  rw [hs]
  dsimp only [Option.map]
  rw [sweep_grow_left_block, hdrop]
  change (sweepTM M).tm.step ((sweepTM M).tm.runFrom
    ((sweepTM M).tm.step (sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
      ((blankRow M.k false).map (fun b => some (sweepSymbol b)) ++ (D ++ [some sweepBoundary]))
      [] out)) ((n + 1) * M.k)) = _
  rw [hturn, hread]
  exact hend

/-- The second half grows the right guard, executes the native input/output
action once, rewrites the zone, and enters the next boundary configuration.
**Proof sketch.** The head upper bound identifies the completed read table with
the source's scanned symbols. Append a blank right block carrying the last
block's head flags, then place its boundary and perform the source input/output
action while turning left. The reverse transduction applies the source action
to every block. At the left boundary, install the next source state (or halt),
and identify the resulting zipper with the enlarged canonical zone. -/
private lemma sweep_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, c.workTapePos i < a + n)
    (hr : ∀ i, c.workTapes i (a + n) = none) :
    (sweepTM M).tm.runFrom
      (sweepCfg (some (.growRight q (readState c (a + n)) 0)) (sweepPos M.k c.inputPos) z
        (((tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)).map
          (fun b => some (sweepSymbol b))).reverse ++ [some sweepBoundary])
        [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)))
      (M.k + 1 + (n + 2) * M.k + 1) =
    sweepStart M ((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c) (a - 1) (n + 2)
      (z + M.k - 1 - ((n + 2) * M.k : ℕ)) := by
  let act := M.tm.tr q c.inputSymbol c.workTapeSymbols
  let p := sweepPos M.k c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let s := readState c (a + n)
  let R := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)
  let W := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 2)
  let V := tapeZone (fun j => tapeRow (act.apply c) j false) (a - 1) (n + 2)
  let put : SweepCell Γ M.k → Option (SweepAlphabet Γ M.k) := fun b => some (sweepSymbol b)
  let p' := sweepPos M.k (act.apply c).inputPos
  let out' := (act.apply c).output.map (sweepEmbed Γ M.k)
  have hrs : (fun i => (s i).1) = c.workTapeSymbols := by
    funext i
    simp only [s, readState, if_pos (hp i)]
  have hrow : rightRow s = tapeRow c (a + n) true := by
    unfold rightRow tapeRow
    apply List.map_congr_left
    intro i _
    have hh : c.workTapePos i ≠ a + n := by have := hp i; omega
    simp [s, readState, hr i, headAt, hh]
  have hwhole : W = R ++ rightRow s := by
    rw [hrow]
    dsimp [W, R]
    rw [show n + 2 = (n + 1) + 1 by omega, tapeZone_append]
    simp only [tapeZone, List.append_nil]
    rw [show a - 1 + (n + 1 : ℕ) = a + n by omega]
  have hbuf : (((rightRow s).map put).reverse.append ((R.map put).reverse ++ [some sweepBoundary])) =
      (W.map put).reverse ++ [some sweepBoundary] := by
    rw [hwhole]
    simp [List.map_append, List.reverse_append, List.append_assoc]
  have hdrop : ([some (sweepBoundary (Γ := Γ) (k := M.k))] : List _).drop M.k = [] := by
    apply List.drop_eq_nil_of_le
    simpa using hk
  have hturn : (sweepTM M).tm.step
      (sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        ((W.map put).reverse ++ [some sweepBoundary]) [] out) =
      sweepRevCfg (some (.write q c.inputSymbol c.workTapeSymbols (fun _ => false)))
        p' (z + M.k - 1) [some sweepBoundary] ((W.map put).reverse ++ [some sweepBoundary]) out' := by
    have hin := sweepInput_read c
      (sweepCfg (some (SweepState.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        ((W.map put).reverse ++ [some sweepBoundary]) [] out) rfl
    change ((sweepTM M).tm.tr (.growRight q s ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    rw [hin, hrs]
    change (⟨act.inputTape, fun _ => (some (some sweepBoundary), .neg),
      act.output.map Sum.inl, some (.write q c.inputSymbol c.workTapeSymbols (fun _ => false))⟩ :
      Action 1 (SweepAlphabet Γ M.k) (SweepState Γ M.State M.k)).apply _ = _
    rw [sweep_turn_left]
    have hm : moveInputPos p act.inputTape = p' := sweepPos_move _ _ _
    rw [hm]
    have ho : out ++ (act.output.map Sum.inl).toList = out' := by
      dsimp [out, out', Action.apply]
      cases act.output <;> simp [sweepEmbed, List.map_append]
    rw [ho]
    rfl
  have hzero : (fun i => headAt c i (a - 1 + (n + 2 : ℕ))) = fun _ => false := by
    funext i
    have hh : c.workTapePos i ≠ a - 1 + (n + 2 : ℕ) := by have := hp i; omega
    simpa only [headAt, decide_eq_false_iff_not] using hh
  have hfold : sweepFold (writeVisit act) (fun _ => false) W.reverse =
      (fun i => headAt c i (a - 1), V.reverse) := by
    have h := write_zone c act (a - 1) (n + 2)
    rw [hzero] at h
    exact h
  have hwlen : W.length = (n + 2) * M.k := tapeZone_length c _ _ _
  have hwrite := sweep_run_reverse (sweepTM M).tm
    (fun right => SweepState.write q c.inputSymbol c.workTapeSymbols right)
    sweepSymbol (writeVisit act) (by intro right b inp; rfl) p' out'
    W.reverse (fun _ => false) (z + M.k - 1) [some sweepBoundary] [some sweepBoundary]
  simp only [List.length_reverse, hwlen, hfold, List.map_reverse, List.reverse_reverse] at hwrite
  have hlast : (sweepTM M).tm.step
      (sweepRevCfg (some (.write q c.inputSymbol c.workTapeSymbols (fun i => headAt c i (a - 1))))
        p' (z + M.k - 1 - ((n + 2) * M.k : ℕ))
        (V.map put ++ [some sweepBoundary]) [some sweepBoundary] out') =
      sweepStart M (act.apply c) (a - 1) (n + 2)
        (z + M.k - 1 - ((n + 2) * M.k : ℕ)) := by
    have hsym : (sweepRevCfg
        (some (SweepState.write q c.inputSymbol c.workTapeSymbols (fun i => headAt c i (a - 1))))
        p' (z + M.k - 1 - ((n + 2) * M.k : ℕ))
        (V.map put ++ [some sweepBoundary]) [some sweepBoundary] out').workTapeSymbols =
        fun _ => some sweepBoundary := by
      funext i
      exact sweepTape_read _ _ _
    change ((sweepTM M).tm.tr (.write q c.inputSymbol c.workTapeSymbols _) _ _).apply _ = _
    rw [hsym]
    exact sweepRevCfg_stay _ _ _ _ _ _ _
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step', sweep_grow_right_block, hdrop]
  change (sweepTM M).tm.step ((sweepTM M).tm.runFrom
    ((sweepTM M).tm.step (sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
      ((rightRow s).map put |>.reverse |>.append ((R.map put).reverse ++ [some sweepBoundary]))
      [] out)) ((n + 2) * M.k)) = _
  rw [hbuf, hturn, hwrite]
  exact hlast

/-- One source transition is one bounded burst, preserving the complete zone
shape and growing it by one block at each end. -/
private lemma sweep_step {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (hs : c.state = some q) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, a ≤ c.workTapePos i ∧ c.workTapePos i < a + n)
    (hl : ∀ i, c.workTapes i (a - 1) = none)
    (hr : ∀ i, c.workTapes i (a + n) = none) :
    (sweepTM M).tm.runFrom (sweepStart M c a n z) ((2 * n + 5) * M.k + 4) =
      sweepStart M (M.tm.step c) (a - 1) (n + 2) (z - M.k) := by
  rw [show (2 * n + 5) * M.k + 4 =
    (M.k + 1 + (n + 1) * M.k + 1) + (M.k + 1 + (n + 2) * M.k + 1) by ring,
    MultiTapeTM.runFrom_add, sweep_prepare M hk c q hs a n z (fun i => (hp i).1) hl,
    sweep_finish M hk c q a n _ (fun i => (hp i).2) hr]
  have hz : z - M.k + 1 + ((n + 1) * M.k : ℕ) + M.k - 1 - ((n + 2) * M.k : ℕ) =
      z - M.k := by push_cast; ring
  rw [hz]
  simp only [MultiTapeTM.step, hs]

/-- Exact transition count after a given number of source steps. -/
private def sweepTime (k : ℕ) : ℕ → ℕ
  | 0 => 2 * k + 2
  | t + 1 => sweepTime k t + ((4 * t + 7) * k + 4)

/-- Summing the exact per-step costs gives a quadratic polynomial. -/
private lemma sweepTime_eq (k t : ℕ) :
    sweepTime k t = 2 * k * t ^ 2 + (5 * k + 4) * t + (2 * k + 2) := by
  induction t with
  | zero => simp [sweepTime]
  | succ t ih => rw [sweepTime, ih]; ring

/-- A single constant bounds initialization and all sweeps, at every input size. -/
private lemma sweepTime_le (k t : ℕ) : sweepTime k t ≤ (9 * k + 6) * (t + 1) ^ 2 := by
  have hpow : 1 ≤ (t + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  have ht : t ≤ (t + 1) ^ 2 :=
    (Nat.le_succ _).trans (by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have ht2 : t ^ 2 ≤ (t + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) _
  rw [sweepTime_eq]
  calc
    2 * k * t ^ 2 + (5 * k + 4) * t + (2 * k + 2)
        ≤ 2 * k * (t + 1) ^ 2 + (5 * k + 4) * (t + 1) ^ 2 +
          (2 * k + 2) * (t + 1) ^ 2 := by
            exact Nat.add_le_add
              (Nat.add_le_add (Nat.mul_le_mul_left _ ht2) (Nat.mul_le_mul_left _ ht))
              (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * k + 2) hpow)
    _ = (9 * k + 6) * (t + 1) ^ 2 := by ring

/-- Up to the source's first halt, initialized runs agree at every macro boundary.
**Proof sketch.** Initialization gives time zero. At each live source state,
the elapsed-time support bound justifies fresh blank guards; the macro-step
lemma advances both the source configuration and the zone radius by one. -/
private lemma sweep_run_to_halt {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) (x : List Γ) (τ : ℕ)
    (hlive : ∀ t < τ, (M.tm.runFrom (M.tm.initCfg x) t).state ≠ none) :
    ∀ t ≤ τ,
      (sweepTM M).tm.runFrom ((sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k))) (sweepTime M.k t) =
        sweepStart M (M.tm.runFrom (M.tm.initCfg x) t) (-(t : ℤ)) (2 * t + 1)
          (-(t : ℤ) * M.k - 1) := by
  intro t
  induction t with
  | zero => intro _; simpa [sweepTime] using sweep_init M x
  | succ t ih =>
    intro ht
    obtain ⟨q, hs⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
    obtain ⟨hp, hc⟩ := source_bounds M x t
    have hpos : ∀ i, -(t : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
        (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i < -(t : ℤ) + (2 * t + 1 : ℕ) := by
      intro i
      have := hp i
      constructor <;> omega
    have hleft : ∀ i, (M.tm.runFrom (M.tm.initCfg x) t).workTapes i (-(t : ℤ) - 1) = none := by
      intro i
      exact hc i _ (by left; omega)
    have hright : ∀ i, (M.tm.runFrom (M.tm.initCfg x) t).workTapes i
        (-(t : ℤ) + (2 * t + 1 : ℕ)) = none := by
      intro i
      exact hc i _ (by right; omega)
    rw [sweepTime, MultiTapeTM.runFrom_add, ih (by omega)]
    rw [show (4 * t + 7) * M.k + 4 = (2 * (2 * t + 1) + 5) * M.k + 4 by ring]
    rw [sweep_step M hk _ q hs _ _ _ hpos hleft hright,
      ← MultiTapeTM.runFrom_succ_eq_step']
    have ha : -(t : ℤ) - 1 = -(t + 1 : ℕ) := by omega
    have hn : 2 * t + 1 + 2 = 2 * (t + 1) + 1 := by omega
    have hz : -(t : ℤ) * M.k - 1 - M.k = -(t + 1 : ℕ) * M.k - 1 := by push_cast; ring
    rw [ha, hn, hz]

/-- **One work tape suffices** [AB09, Claim 1.6]: a `Γ`-machine computing `f` within
`T` is simulated by a machine with a single work tape, over an enlarged finite
alphabet, within `c · (T n + 1)²`.

**Proof sketch.** For `k = 0`, simulate `M` directly with one unused work tape.
For `k ≥ 1`, the single work tape of `M'` stores the `k` tapes of `M` interleaved:
cell `j·k + i` of the simulated layout holds cell `j` of tape `i` (centered at `0` in
both directions). The alphabet is enlarged to cells carrying a *tagged payload*
`Option Γ` — so a marked blank is representable, which a bare `Γ × flag` product
would miss — together with a "head here" flag and zone-boundary tags; `Γ` embeds via
`e` as an unmarked non-blank payload. To simulate one step of `M`, `M'` sweeps its work tape once
left-to-right across the visited zone recording the `k` marked symbols in its state,
computes `M`'s transition, and sweeps back right-to-left updating the marked cells and
moving the marks. After `t` steps of `M` the visited zone spans `O(k · (t + 1))`
cells, so each simulated step costs `O(k · (T n + 1))` and the total is
`c · (T n + 1)²`. Input reads and output emissions pass through unchanged.

**Implementation note.** The forward pass records the preceding block's head
flags in the cells; the return pass carries the following block's flags in its
finite control. This implements both movement directions using exactly the two
stated sweeps. Each macro-step extends the zone by one blank block at each end.
For positive `k`, initialization costs `2k + 2` transitions and source step `t`
costs `(4t + 7)k + 4`; `sweepTime_le` supplies the constant `9k + 6`.
The zero-tape branch is a separate lockstep embedding with constant `1`. -/
theorem one_work_tape {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) ^ 2 := by
  by_cases hk : M.k = 0
  · refine ⟨Γ, inferInstance, inferInstance, Function.Embedding.refl Γ,
      unusedTapeTM M hk, 1, rfl, ?_⟩
    intro x
    simpa only [Function.Embedding.coe_refl, List.map_id, one_mul] using
      ((unusedTape_computes M hk f T hM) x).mono
        (show T x.length ≤ (T x.length + 1) ^ 2 from
          (Nat.le_succ _).trans (by
            rw [pow_two]
            exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  · refine ⟨SweepAlphabet Γ M.k, inferInstance, inferInstance, sweepEmbed Γ M.k,
      sweepTM M, 9 * M.k + 6, rfl, ?_⟩
    intro x
    obtain ⟨hhalt, hout⟩ := (computesInTime_iff M x (f x) (T x.length)).mp (hM x)
    have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T x.length, hhalt⟩
    let τ := Nat.find hex
    have hτ : (M.tm.runFrom (M.tm.initCfg x) τ).state = none := Nat.find_spec hex
    have ht : τ ≤ T x.length := Nat.find_min' hex hhalt
    have hlive : ∀ t < τ, (M.tm.runFrom (M.tm.initCfg x) t).state ≠ none :=
      fun _ h => Nat.find_min hex h
    have hrun := sweep_run_to_halt M (Nat.pos_of_ne_zero hk) x τ hlive τ (le_refl _)
    have houtτ : (M.tm.runFrom (M.tm.initCfg x) τ).output = f x := by
      have h := M.tm.runFrom_output_eq_of_halt (M.tm.initCfg x) ht hτ
      exact h.symm.trans hout
    have hc : (sweepTM M).ComputesInTime (x.map (sweepEmbed Γ M.k))
        ((f x).map (sweepEmbed Γ M.k)) (sweepTime M.k τ) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [hrun]
      constructor
      · change (M.tm.runFrom (M.tm.initCfg x) τ).state.map (fun q => SweepState.growLeft q 0) = none
        rw [hτ]
        rfl
      · change (M.tm.runFrom (M.tm.initCfg x) τ).output.map (sweepEmbed Γ M.k) = _
        rw [houtτ]
    exact hc.mono ((sweepTime_le M.k τ).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right ht 1) 2)))

/-- One work tape and the binary alphabet suffice simultaneously: the composition of
[AB09, Claim 1.6] with [AB09, Claim 1.5], possible because alphabet reduction
preserves the number of work tapes.

**Proof sketch.** Apply `Turing.FinTM.one_work_tape` to `M` with `Γ = Bool`,
obtaining a one-work-tape machine over some `Γ'` that computes `f` via an embedding
`Bool ↪ Γ'` within `c₁ · (T n + 1)²` — exactly the hypothesis of
`Turing.FinTM.alphabet_reduction`, which keeps `k = 1` and returns to the binary
alphabet within `c₂ · (c₁ · (T n + 1)² + 1) ≤ c · (T n + 1)²`. -/
theorem one_work_tape_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTime f fun n => c * (T n + 1) ^ 2 := by
  obtain ⟨Γ', instF, instD, e, M₁, c₁, hk₁, h₁⟩ := one_work_tape M f T hM
  haveI := instF
  haveI := instD
  obtain ⟨c₂, M₂, hk₂, h₂⟩ :=
    alphabet_reduction e M₁ f (fun n => c₁ * (T n + 1) ^ 2) h₁
  refine ⟨M₂, c₂ * (c₁ + 1), by rw [hk₂, hk₁], fun x => (h₂ x).mono ?_⟩
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc c₂ * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ c₂ * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl c₂) (Nat.add_le_add_left hpow _)
    _ = c₂ * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bidirectional versus unidirectional tapes

[AB09, Claim 1.8]: tapes that are infinite in both directions are simulated by tapes
infinite in one direction only, with constant-factor slowdown.

## Deviations from [AB09]

Our vendored model's tapes are *already* bidirectional (`ℤ`-indexed) — that choice is
what lets initialization dispense with start markers. So the faithful in-model
rendering of Claim 1.8 runs in the only meaningful direction: every machine is
simulated, with constant-factor slowdown and the same number of work tapes, by one
whose work heads **never visit a negative cell** (`Turing.FinTM.NonnegativeHeads`),
i.e. by a machine that uses its tapes unidirectionally. The simulating machine "folds"
each tape at the origin, following [AB09]'s proof, over the enlarged non-blank
alphabet `Bool × Option Γ × Option Γ` — an origin flag plus two *independent*,
possibly blank, payloads. (A bare `Γ × Γ` cannot represent a symbol paired with a
blank neighbor; phase-2 re-audit, finding 1.)

## Main results

* `Turing.FinTM.NonnegativeHeads` — the unidirectional-use predicate.
* `Turing.FinTM.nonnegative_heads` — [AB09, Claim 1.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.8, p. 18.)
-/

namespace Turing.FinTM

/-- A machine uses its work tapes unidirectionally: in every initialized run, no work
head ever visits a negative cell. -/
def NonnegativeHeads {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (input : List Γ) (t : ℕ) (i : Fin M.k),
    0 ≤ (M.tm.runFrom (M.tm.initCfg input) t).workTapePos i

private abbrev FoldSymbol (Γ : Type) := Bool × Option Γ × Option Γ

private def foldEmbedding {Γ : Type} : Γ ↪ FoldSymbol Γ where
  toFun a := (false, some a, none)
  inj' := by intro a b h; exact Option.some.inj (congrArg (fun x => x.2.1) h)

private def foldPos (z : ℤ) : ℤ := if 0 ≤ z then z else -z - 1

private def foldSide (z : ℤ) : Bool := decide (0 ≤ z)

private def foldPack {Γ : Type} (v : FoldSymbol Γ) : Option (FoldSymbol Γ) :=
  match v with
  | (false, none, none) => none
  | _ => some v

private def foldUnpack {Γ : Type} (v : Option (FoldSymbol Γ)) : FoldSymbol Γ :=
  v.getD (false, none, none)

private lemma foldUnpack_pack {Γ : Type} (v : FoldSymbol Γ) :
    foldUnpack (foldPack v) = v := by
  rcases v with ⟨b, a, c⟩
  cases b <;> cases a <;> cases c <;> rfl

private def foldTape {Γ : Type} (t : ℤ → Option Γ) (p : ℤ) : Option (FoldSymbol Γ) :=
  if 0 ≤ p then foldPack (decide (p = 0), t p, t (-p - 1)) else none

private def foldMove (side origin : Bool) (d : SignType) : SignType × Bool :=
  match side, d with
  | true, .pos => (.pos, true)
  | true, .neg => if origin then (.zero, false) else (.neg, true)
  | false, .neg => (.pos, false)
  | false, .pos => if origin then (.zero, true) else (.neg, false)
  | _, .zero => (.zero, side)

private lemma foldPos_nonneg (z : ℤ) : 0 ≤ foldPos z := by
  unfold foldPos
  split <;> omega

private lemma foldMove_correct (z : ℤ) (d : SignType) :
    foldPos z + ((foldMove (foldSide z) (decide (foldPos z = 0)) d).1 : ℤ) =
        foldPos (z + (d : ℤ)) ∧
      (foldMove (foldSide z) (decide (foldPos z = 0)) d).2 =
        foldSide (z + (d : ℤ)) := by
  by_cases hz : 0 ≤ z <;> cases d <;>
    simp [foldMove, foldSide, foldPos, hz, SignType.cast] <;>
    (try split_ifs) <;> (try simp_all) <;> omega

private def foldRead {Γ : Type} (side : Bool) (w : Option (FoldSymbol Γ)) : Option Γ :=
  if side then (foldUnpack w).2.1 else (foldUnpack w).2.2

private lemma foldRead_tape {Γ : Type} (t : ℤ → Option Γ) (z : ℤ) :
    foldRead (foldSide z) (foldTape t (foldPos z)) = t z := by
  unfold foldRead
  rw [foldTape, if_pos (foldPos_nonneg z), foldUnpack_pack]
  unfold foldSide foldPos
  split_ifs <;> simp_all

private def foldWrite {Γ : Type} (side : Bool) (w : Option (FoldSymbol Γ))
    (a : Option Γ) : Option (FoldSymbol Γ) :=
  let v := foldUnpack w
  foldPack (v.1, if side then a else v.2.1, if side then v.2.2 else a)

/-- Updating a virtual cell changes only its active folded payload. At the folded
coordinate, split on the virtual head's sign; away from it neither paired virtual
coordinate equals the updated cell. Canonical packing preserves physical blanks. -/
private lemma foldTape_update {Γ : Type} [DecidableEq Γ]
    (t : ℤ → Option Γ) (z : ℤ) (a : Option Γ) :
    Function.update (foldTape t) (foldPos z)
        (foldWrite (foldSide z) (foldTape t (foldPos z)) a) =
      foldTape (Function.update t z a) := by
  funext p
  unfold foldWrite
  rw [foldTape, if_pos (foldPos_nonneg z), foldUnpack_pack]
  by_cases hp : p = foldPos z
  · subst p
    rw [Function.update_self]
    unfold foldTape
    rw [if_pos (foldPos_nonneg z)]
    have hn : -z - 1 ≠ z := by omega
    by_cases hz : 0 ≤ z
    · simp [foldSide, foldPos, hz, Function.update_apply, hn]
    · simp [foldSide, foldPos, hz, Function.update_apply, hn]
  · rw [Function.update_of_ne hp]
    unfold foldTape
    split_ifs with h
    · have h₁ : p ≠ z := by unfold foldPos at hp; split_ifs at hp <;> omega
      have h₂ : -p - 1 ≠ z := by unfold foldPos at hp; split_ifs at hp <;> omega
      rw [Function.update_of_ne h₁, Function.update_of_ne h₂]
    · rfl

private def foldAction {Γ S : Type} {k : ℕ} (side : Fin k → Bool)
    (work : Fin k → Option (FoldSymbol Γ)) (a : Action k Γ S) :
    Action k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) where
  inputTape := a.inputTape
  workTapes i :=
    ((a.workTapes i).1.map (foldWrite (side i) (work i)),
      (foldMove (side i) (foldUnpack (work i)).1 (a.workTapes i).2).1)
  output := a.output.map foldEmbedding
  state := a.state.map fun q => some (q, fun i =>
    (foldMove (side i) (foldUnpack (work i)).1 (a.workTapes i).2).2)

private def foldCfg {Γ S : Type} {k : ℕ} {x : List Γ} (c : Cfg k Γ S x) :
    Cfg k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) (x.map foldEmbedding) where
  state := c.state.map fun q => some (q, fun i => foldSide (c.workTapePos i))
  inputPos := ⟨c.inputPos.val, by simp only [List.length_map]; exact c.inputPos.isLt⟩
  workTapes i := foldTape (c.workTapes i)
  workTapePos i := foldPos (c.workTapePos i)
  output := c.output.map foldEmbedding

private lemma foldCfg_input {Γ S : Type} {k : ℕ} {x : List Γ} (c : Cfg k Γ S x) :
    (foldCfg c).inputSymbol = c.inputSymbol.map foldEmbedding := by
  unfold Cfg.inputSymbol
  simp only [foldCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

private lemma foldCfg_origin {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (i : Fin k) :
    (foldUnpack ((foldCfg c).workTapeSymbols i)).1 =
      decide (foldPos (c.workTapePos i) = 0) := by
  simp only [Cfg.workTapeSymbols, foldCfg, foldTape, if_pos (foldPos_nonneg _),
    foldUnpack_pack]

/-- Folding an action preserves the full configuration representation. The tape
identity updates precisely one of the two independent payloads, and the movement
identity covers both stationary crossings of the fold. -/
private lemma foldCfg_apply {Γ S : Type} [DecidableEq Γ] {k : ℕ} {x : List Γ}
    (a : Action k Γ S) (c : Cfg k Γ S x) :
    (foldAction (fun i => foldSide (c.workTapePos i)) (foldCfg c).workTapeSymbols a).apply
      (foldCfg c) = foldCfg (a.apply c) := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · change a.state.map _ = a.state.map _
    congr 1
    funext q
    congr 2
    funext i
    rw [foldCfg_origin]
    exact (foldMove_correct (c.workTapePos i) (a.workTapes i).2).2
  · apply Fin.ext
    simp [foldCfg, foldAction, Action.apply, moveInputPos]
    split <;> rfl
  · funext i
    cases hw : (a.workTapes i).1 with
    | none => simp [foldAction, Action.apply, foldCfg, hw]
    | some w =>
      simpa only [foldAction, Option.map_some, foldCfg, Action.apply, hw, Cfg.workTapeSymbols] using
        foldTape_update (c.workTapes i) (c.workTapePos i) w
  · funext i
    change foldPos (c.workTapePos i) +
      ((foldMove (foldSide (c.workTapePos i))
        (foldUnpack ((foldCfg c).workTapeSymbols i)).1 (a.workTapes i).2).1 : ℤ) = _
    rw [foldCfg_origin]
    exact (foldMove_correct (c.workTapePos i) (a.workTapes i).2).1
  · simp [foldAction, foldCfg, Action.apply, List.map_append, Option.toList_map]

private def foldDecode {Γ : Type} : FoldSymbol Γ → Option Γ
  | (false, some a, none) => some a
  | _ => none

private def foldHalt {Γ S : Type} {k : ℕ} : Action k Γ S :=
  ⟨0, fun _ => (none, 0), none, none⟩

private def foldInitAction {Γ S : Type} {k : ℕ} (q : S) :
    Action k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) :=
  ⟨0, fun _ => (some (some (true, none, none)), 0), none,
    some (some (q, fun _ => true))⟩

/-- Initialize every origin, halting on the same transition if the first input
read is already outside the embedding. No simulated transition precedes the check. -/
private def foldStartAction {Γ S : Type} {k : ℕ} (q : S)
    (inp : Option (FoldSymbol Γ)) : Action k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) :=
  match inp with
  | none => foldInitAction q
  | some v => match foldDecode v with
    | none => { foldInitAction q with state := none }
    | some _ => foldInitAction q

private lemma foldStartAction_embed {Γ S : Type} {k : ℕ} (q : S) (inp : Option Γ) :
    foldStartAction (k := k) q (inp.map foldEmbedding) = foldInitAction q := by
  cases inp <;> rfl

private def foldTM {Γ : Type} [Fintype Γ] [DecidableEq Γ] (M : FinTM Γ) :
    FinTM (FoldSymbol Γ) where
  k := M.k
  State := Option (M.State × (Fin M.k → Bool))
  tm :=
    { q₀ := none
      tr := fun q inp work => match q with
        | none => foldStartAction M.tm.q₀ inp
        | some (q, side) =>
          match inp with
          | none => foldAction side work (M.tm.tr q none (fun i => foldRead (side i) (work i)))
          | some v => match foldDecode v with
            | none => foldHalt
            | some a => foldAction side work
                (M.tm.tr q (some a) (fun i => foldRead (side i) (work i))) }

/-- One-step commutation follows from the action correspondence after transporting
the input read and reading each active folded payload. Halting is absorbing on both
sides; valid embedded symbols always pass the input decoder. -/
private lemma foldCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) {x : List Γ} (c : Cfg M.k Γ M.State x) :
    (foldTM M).tm.step (foldCfg c) = foldCfg (M.tm.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp only [foldCfg, hs, Option.map_none]; rfl
  | some q =>
    have hs' : (foldCfg c).state = some (some (q, fun i => foldSide (c.workTapePos i))) := by
      simp only [foldCfg, hs, Option.map_some]
    rw [hs']
    dsimp only
    rw [foldCfg_input]
    have hw : (fun i => foldRead (foldSide (c.workTapePos i))
        ((foldCfg c).workTapeSymbols i)) = c.workTapeSymbols := by
      funext i
      exact foldRead_tape _ _
    cases hi : c.inputSymbol with
    | none =>
      dsimp only [Option.map, foldTM]
      rw [hw]
      exact foldCfg_apply _ c
    | some a =>
      dsimp only [Option.map, foldTM, foldDecode, foldEmbedding]
      rw [hw]
      exact foldCfg_apply _ c

private lemma foldCfg_init {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List Γ) :
    (foldTM M).tm.step ((foldTM M).tm.initCfg (x.map foldEmbedding)) =
      foldCfg (M.tm.initCfg x) := by
  unfold MultiTapeTM.step
  change (foldStartAction M.tm.q₀ _).apply _ = _
  have hi := foldCfg_input (M.tm.initCfg x)
  change ((foldTM M).tm.initCfg (x.map foldEmbedding)).inputSymbol = _ at hi
  rw [hi, foldStartAction_embed]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [foldInitAction, foldCfg]
  · funext i p
    simp [foldInitAction, foldCfg, foldTape, foldPack, Function.update_apply]
    split_ifs <;> simp_all
  · funext i
    simp [foldInitAction, foldCfg, foldPos]

private lemma foldCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List Γ) (t : ℕ) :
    (foldTM M).tm.runFrom ((foldTM M).tm.initCfg (x.map foldEmbedding)) (t + 1) =
      foldCfg (M.tm.runFrom (M.tm.initCfg x) t) := by
  induction t with
  | zero => simpa only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero] using foldCfg_init M x
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih, foldCfg_step,
      MultiTapeTM.runFrom_succ_eq_step']

private lemma foldWrite_origin {Γ : Type} (s : Bool) (w : Option (FoldSymbol Γ))
    (a : Option Γ) : (foldUnpack (foldWrite s w a)).1 = (foldUnpack w).1 := by
  simp only [foldWrite, foldUnpack_pack]

private lemma foldMove_nonneg (p : ℤ) (hp : 0 ≤ p) (side : Bool) (d : SignType) :
    0 ≤ p + ((foldMove side (decide (p = 0)) d).1 : ℤ) := by
  by_cases h : p = 0 <;> cases side <;> cases d <;>
    simp [foldMove, h, SignType.cast] <;> omega

/-- After initialization the initial control state is unreachable, all physical
heads are nonnegative, and the origin field is correct at every nonnegative cell.
This invariant quantifies over arbitrary enlarged-alphabet inputs. -/
private def foldSafe {Γ S : Type} {k : ℕ} {x : List (FoldSymbol Γ)}
    (c : Cfg k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) x) : Prop :=
  c.state ≠ some none ∧
    (∀ i, 0 ≤ c.workTapePos i) ∧
      ∀ i p, 0 ≤ p → (foldUnpack (c.workTapes i p)).1 = decide (p = 0)

/-- A translated action preserves origin fields and cannot move left from zero.
The next control state is either halted or a source state, never initialization. -/
private lemma foldAction_safe {Γ S : Type} {k : ℕ} {x : List (FoldSymbol Γ)}
    (c : Cfg k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) x)
    (hc : foldSafe c) (side : Fin k → Bool) (a : Action k Γ S) :
    foldSafe ((foldAction side c.workTapeSymbols a).apply c) := by
  refine ⟨?_, ?_, ?_⟩
  · cases ha : a.state <;> simp [foldAction, Action.apply, ha]
  · intro i
    change 0 ≤ c.workTapePos i +
      ((foldMove (side i) (foldUnpack (c.workTapeSymbols i)).1 (a.workTapes i).2).1 : ℤ)
    rw [show (foldUnpack (c.workTapeSymbols i)).1 = decide (c.workTapePos i = 0)
      from hc.2.2 i _ (hc.2.1 i)]
    exact foldMove_nonneg _ (hc.2.1 i) _ _
  · intro i p hp
    cases hw : (a.workTapes i).1 with
    | none => simpa only [Action.apply, foldAction, hw, Option.map_none] using hc.2.2 i p hp
    | some w =>
      simp only [Action.apply, foldAction, hw, Option.map_some]
      by_cases he : p = c.workTapePos i
      · subst p
        rw [Function.update_self, foldWrite_origin]
        exact hc.2.2 i _ hp
      · rw [Function.update_of_ne he]
        exact hc.2.2 i p hp

private lemma foldHalt_safe {Γ S : Type} {k : ℕ} {x : List (FoldSymbol Γ)}
    (c : Cfg k (FoldSymbol Γ) (Option (S × (Fin k → Bool))) x)
    (hc : foldSafe c) : foldSafe (foldHalt.apply c) := by
  simpa [foldSafe, foldHalt, Action.apply] using hc.2

/-- Every post-initialization transition preserves safety. Valid input reads use
the folding action; a non-image symbol selects a stationary halt. -/
private lemma foldSafe_step {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) {x : List (FoldSymbol Γ)}
    (c : Cfg (foldTM M).k (FoldSymbol Γ) (foldTM M).State x) (hc : foldSafe c) :
    foldSafe ((foldTM M).tm.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => exact hc
  | some q =>
    cases q with
    | none => exact False.elim (hc.1 hs)
    | some q =>
      rcases q with ⟨q, side⟩
      dsimp only [foldTM]
      cases hi : c.inputSymbol with
      | none => exact foldAction_safe c hc side _
      | some v =>
        dsimp only
        cases hd : foldDecode v with
        | none => exact foldHalt_safe c hc
        | some a => exact foldAction_safe c hc side _

private lemma foldSafe_init {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List (FoldSymbol Γ)) :
    foldSafe ((foldTM M).tm.step ((foldTM M).tm.initCfg x)) := by
  have hsafe : ∀ (st : Option (foldTM M).State), st ≠ some none →
      foldSafe (({ foldInitAction M.tm.q₀ with state := st }).apply
        ((foldTM M).tm.initCfg x)) := by
    intro st hst
    refine ⟨hst, fun i => by simp [foldInitAction], ?_⟩
    intro i p hp
    by_cases h : p = 0
    · subst p
      simp [foldInitAction, foldUnpack]
    · simp [foldInitAction, foldUnpack, h]
  unfold MultiTapeTM.step
  change foldSafe ((foldStartAction M.tm.q₀ _).apply _)
  unfold foldStartAction
  split
  · exact hsafe _ (by simp)
  · split <;> exact hsafe _ (by simp)

private lemma foldTM_nonnegative {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) : (foldTM M).NonnegativeHeads := by
  intro x t i
  cases t with
  | zero => simp
  | succ t =>
    have hs : ∀ t, foldSafe ((foldTM M).tm.runFrom
        ((foldTM M).tm.step ((foldTM M).tm.initCfg x)) t) := by
      intro t
      induction t with
      | zero => exact foldSafe_init M x
      | succ t ih =>
        rw [MultiTapeTM.runFrom_succ_eq_step']
        exact foldSafe_step M _ ih
    rw [MultiTapeTM.runFrom_succ_eq_step]
    exact (hs t).2.1 i

/-- **Unidirectional tapes suffice** [AB09, Claim 1.8]: a `Γ`-machine computing `f`
within `T` is simulated, with the same number of work tapes and constant-factor
slowdown, by a machine over an enlarged alphabet whose work heads never visit negative
cells.

**Proof sketch.** Fold each tape at the origin along the coordinate
`φ z = if 0 ≤ z then z else -z - 1` (note `φ 0 = φ (-1) = 0`; this is *not* the
absolute value): physical cell `p ≥ 0` holds the two *independent* payloads —
simulated cell `p` and simulated cell `-p - 1`, each possibly blank — over the
enlarged non-blank alphabet `Γ' = Bool × Option Γ × Option Γ`, whose Boolean
component is an origin flag; `e γ = (false, some γ, none)` (injective via its first
payload), and an untouched physical blank decodes as two blanks with no flag. The
simulator's state tracks, per tape, which component the simulated head is in. Because
a transition cannot read a head coordinate, the origin is made *detectable* by a
fresh initialization state whose single action writes `(true, none, none)` at cell
`0` of every work tape simultaneously (one transition, length-independent); every
later write updates only the active payload, preserving the other payload and the
flag. Moves translate directly except at the fold: crossing between simulated cells `0`
and `-1` flips the component *without* issuing a physical move (the physical
coordinate stays `0`); each simulated step costs a constant number of physical steps,
giving `c · (T n + 1)` — [AB09] gets `4T`. Physical head positions are values of `φ`,
hence nonnegative; on enlarged-alphabet inputs containing symbols outside the range
of `e` — where no functional behavior is promised but `NonnegativeHeads` still
quantifies — the simulator halts safely on first contact, preserving nonnegativity
(phase-2 audit, finding 10 and case A14). The folding invariant transfers computation
and halting on embedded inputs.

**Implementation note (epoch 2, batch C).** The private configuration map uses
canonical packing: an untagged pair of blanks is a physical blank. Initialization
costs one step and the subsequent simulation is lockstep, so the displayed constant
can be chosen as one. Safety is proved separately for every enlarged-alphabet input,
including malformed symbols, without using the computation premise. An invalid
first symbol causes halting during the initialization transition itself. -/
theorem nonnegative_heads {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.NonnegativeHeads ∧ M'.k = M.k ∧
        M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) := by
  refine ⟨FoldSymbol Γ, inferInstance, inferInstance, foldEmbedding, foldTM M, 1,
    foldTM_nonnegative M, rfl, ?_⟩
  intro x
  rw [computesInTime_iff]
  dsimp only
  rw [one_mul, foldCfg_run]
  obtain ⟨hs, ho⟩ := (computesInTime_iff M x (f x) (T x.length)).1 (hM x)
  simp only [foldCfg, hs, ho, Option.map_none, and_self]

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Alphabet reduction

[AB09, Claim 1.5]: a machine over any finite alphabet `Γ` is simulated by a machine
over the binary alphabet with only a constant-factor slowdown (the constant depending
on `|Γ|`), and with the same number of work tapes. This is the theorem that justifies
defining `DTIME` over binary-alphabet machines (see
`TCSlib.Complexity.ClassP.DTIME`).

## Deviations from [AB09]

* [AB09] states the slowdown as `4 log |Γ| · T(n)`; we existentialize the constant and
  pad with `+ 1` (empty input), consistently with the rest of the development.
* [AB09]'s statement fixes input and output over `{0,1}` with only the *work* alphabet
  reduced. In our model a machine has one alphabet for all tapes, so "computing a
  binary function" for a `Γ`-machine is expressed via a symbol embedding `e : Bool ↪ Γ`
  (`Turing.FinTM.ComputesFunInTimeVia`): the simulator reads genuine binary input
  directly (its table composes with `e`), block-encodes work-tape symbols in
  `⌈log₂ |Γ|⌉` bits, and decodes each emitted symbol `e b` back to the bit `b`.
  Emitted symbols are always in the range of `e` because the append-only output equals
  the final output string, which is `(f x).map e` — early emissions included, since an
  irrevocable emission remains a prefix of the final output.
* [AB09]'s Claim 1.5 hypothesizes a time-constructible `T`; the simulation does not
  need it, so we drop the hypothesis. The statement also generalizes Boolean output to
  string output.

## Main results

* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16.)
-/

namespace Turing.FinTM

noncomputable section

private abbrev ArBlock (N : ℕ) := Fin (N + 1) → Option Bool

private def arCell (N : ℕ) (p : ℤ) : ℤ := p / ((N : ℤ) + 1)

private def arIndex (N : ℕ) (p : ℤ) : Fin (N + 1) :=
  ⟨(p % ((N : ℤ) + 1)).toNat, by
    have h₁ := Int.emod_nonneg p (show (N : ℤ) + 1 ≠ 0 by omega)
    have h₂ := Int.emod_lt_of_pos p (show 0 < (N : ℤ) + 1 by omega)
    omega⟩

private def arPos (N : ℕ) (z : ℤ) (j : ℕ) : ℤ := ((N : ℤ) + 1) * z + j

private lemma arCoords (N : ℕ) (z : ℤ) (j : Fin (N + 1)) :
    arCell N (arPos N z j.val) = z ∧ arIndex N (arPos N z j.val) = j := by
  have hj := j.isLt
  have h := (Int.ediv_emod_unique (show 0 < (N : ℤ) + 1 by omega)).2
    (show (j.val : ℤ) + ((N : ℤ) + 1) * z = arPos N z j.val ∧
      0 ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (N : ℤ) + 1 from
      ⟨by simp [arPos, add_comm], by omega, by omega⟩)
  refine ⟨h.1, Fin.ext ?_⟩
  simp only [arIndex, h.2, Int.toNat_natCast]

private lemma arPos_coords (N : ℕ) (p : ℤ) :
    arPos N (arCell N p) (arIndex N p).val = p := by
  have h := Int.emod_nonneg p (show (N : ℤ) + 1 ≠ 0 by omega)
  simp only [arPos, arCell, arIndex, Int.toNat_of_nonneg h]
  exact Int.mul_ediv_add_emod p ((N : ℤ) + 1)

private lemma arPos_eq {N : ℕ} (z z' : ℤ) (j j' : Fin (N + 1)) :
    arPos N z j.val = arPos N z' j'.val ↔ z = z' ∧ j = j' := by
  constructor
  · intro h
    have h₁ := congrArg (arCell N) h
    have h₂ := congrArg (arIndex N) h
    rw [(arCoords N z j).1, (arCoords N z' j').1] at h₁
    rw [(arCoords N z j).2, (arCoords N z' j').2] at h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

private def arTape {N : ℕ} (F : ℤ → ArBlock N) (p : ℤ) : Option Bool :=
  F (arCell N p) (arIndex N p)

private lemma arTape_at {N : ℕ} (F : ℤ → ArBlock N) (z : ℤ) (j : Fin (N + 1)) :
    arTape F (arPos N z j.val) = F z j := by
  simp only [arTape, (arCoords N z j).1, (arCoords N z j).2]

private lemma arTape_ext {N : ℕ} (u v : ℤ → Option Bool)
    (h : ∀ z (j : Fin (N + 1)), u (arPos N z j.val) = v (arPos N z j.val)) : u = v := by
  funext p
  simpa only [arPos_coords] using h (arCell N p) (arIndex N p)

private lemma arTape_update {N : ℕ} (F : ℤ → ArBlock N) (z : ℤ)
    (j : Fin (N + 1)) (b : Option Bool) :
    Function.update (arTape F) (arPos N z j.val) b =
      arTape (fun z' j' => if z' = z ∧ j' = j then b else F z' j') := by
  apply arTape_ext (N := N)
  intro z' j'
  simp only [Function.update_apply, arTape_at, arPos_eq]

/-- A fixed-width one-hot code for nonblank symbols, with an all-blank code for
logical blank. Testing the position assigned to a symbol proves injectivity. -/
private def arCode {Γ : Type} [Fintype Γ] : Option Γ ↪ ArBlock (Fintype.card Γ) where
  toFun a j := a.map fun x => decide (j.val = (Fintype.equivFin Γ x).val)
  inj' := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => have := congrFun h 0; simp at this
    | some a =>
      cases b with
      | none => have := congrFun h 0; simp at this
      | some b =>
        have ha := (Fintype.equivFin Γ a).isLt
        have h₁ := congrFun h ⟨(Fintype.equivFin Γ a).val, by omega⟩
        have h₂ : (Fintype.equivFin Γ a).val = (Fintype.equivFin Γ b).val := by simpa using h₁
        exact congrArg some ((Fintype.equivFin Γ).injective (Fin.ext h₂))

private def arDecode {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N) :
    ArBlock N → Option Γ := Function.invFun E

private lemma arDecode_code {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N) (a : Option Γ) :
    arDecode E (E a) = a := Function.leftInverse_invFun E.injective a

private def arBit {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (a : Γ) : Bool :=
  decide (a = e true)

private lemma arBit_embed {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) :
    arBit e (e b) = b := by
  cases b <;> simp [arBit, e.injective.eq_iff]

private abbrev ArPending (Γ S : Type) (k : ℕ) :=
  Option S × (Fin k → Option Γ) × (Fin k → SignType)

private abbrev ArState (Γ S : Type) (k N : ℕ) :=
  (S × Fin (N + 2) × (Fin k → ArBlock N)) ⊕
    (ArPending Γ S k × (Fin (N + 1) ⊕ Fin (N + 2)))

private def arReady {Γ S : Type} {k N : ℕ} (q : S) : ArState Γ S k N :=
  .inl (q, 0, fun _ _ => none)

private def arPending {Γ S : Type} {k : ℕ} (read : Fin k → Option Γ)
    (a : Action k Γ S) : ArPending Γ S k :=
  (a.state, fun i => (a.workTapes i).1.getD (read i), fun i => (a.workTapes i).2)

/-- A block cycle reads right, writes left, and then moves a whole block in each
source direction. Even with zero work tapes the finite controller performs the same
positive number of steps. Input motion and the possible emission occur only once,
at the transition between reading and writing. -/
private def arTM {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) : FinTM Bool where
  k := M.k
  State := ArState Γ M.State M.k N
  decEqState := Classical.decEq _
  tm :=
    { q₀ := arReady M.tm.q₀
      tr := fun q inp work => match q with
        | .inl (q, j, buf) =>
          if h : j.val < N + 1 then
            ⟨0, fun _ => (none, .pos), none,
              some (.inl (q, ⟨j.val + 1, by omega⟩,
                fun i => Function.update (buf i) ⟨j.val, h⟩ (work i)))⟩
          else
            let a := M.tm.tr q (inp.map e) (fun i => arDecode E (buf i))
            ⟨a.inputTape, fun _ => (none, .neg), a.output.map (arBit e),
              some (.inr (arPending (fun i => arDecode E (buf i)) a, .inl ⟨N, by omega⟩))⟩
        | .inr (a, .inl j) =>
          if h : j.val = 0 then
            ⟨0, fun i => (some (E (a.2.1 i) j), 0), none,
              some (.inr (a, .inr ⟨N + 1, by omega⟩))⟩
          else
            ⟨0, fun i => (some (E (a.2.1 i) j), .neg), none,
              some (.inr (a, .inl ⟨j.val - 1, by omega⟩))⟩
        | .inr (a, .inr r) =>
          if h : r.val = 0 then
            ⟨0, fun _ => (none, 0), none, a.1.map arReady⟩
          else
            ⟨0, fun i => (none, a.2.2 i), none,
              some (.inr (a, .inr ⟨r.val - 1, by omega⟩))⟩ }

/-- Canonical macro-boundary representation. Output is mapped through the total
bit decoder; under the computation premise `arEmission_in_image` additionally shows
that every emission is in the bit embedding's image, so its default case is unused. -/
private def arCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e)) :
    Cfg k Bool (ArState Γ S k N) x where
  state := c.state.map arReady
  inputPos := ⟨c.inputPos.val, by simpa only [List.length_map] using c.inputPos.isLt⟩
  workTapes i := arTape (fun z => E (c.workTapes i z))
  workTapePos i := arPos N (c.workTapePos i) 0
  output := c.output.map (arBit e)

private lemma arCfg_input {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e)) :
    (arCfg E e c).inputSymbol.map e = c.inputSymbol := by
  unfold Cfg.inputSymbol
  simp only [arCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

private def arBuffer {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) (j : ℕ) : Fin k → ArBlock N :=
  fun i b => if b.val < j then E (read i) b else none

private lemma arBuffer_zero {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) : arBuffer E read 0 = fun _ _ => none := by
  funext i b
  simp [arBuffer]

private lemma arBuffer_full {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) : arBuffer E read (N + 1) = fun i => E (read i) := by
  funext i b
  simp only [arBuffer, if_pos b.isLt]

private lemma arBuffer_update {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) (j : Fin (N + 1)) :
    (fun i => Function.update (arBuffer E read j.val i) j (E (read i) j)) =
      arBuffer E read (j.val + 1) := by
  funext i b
  by_cases h : b = j
  · subst b
    simp [arBuffer]
  · have hv : b.val ≠ j.val := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h, arBuffer]
    split_ifs <;> first | rfl | omega

private def arReadCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (j : Fin (N + 2)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e c with
    state := some (.inl (q, j, arBuffer E c.workTapeSymbols j.val))
    workTapePos := fun i => arPos N (c.workTapePos i) j.val }

private lemma arReadCfg_zero {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (hc : c.state = some q) : arReadCfg E e c q 0 = arCfg E e c := by
  simp [arReadCfg, arCfg, hc, arReady, arBuffer_zero]

private lemma arReadCfg_symbols {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (j : Fin (N + 2)) (hj : j.val < N + 1) :
    (arReadCfg E e c q j).workTapeSymbols = fun i => E (c.workTapeSymbols i) ⟨j.val, hj⟩ := by
  funext i
  exact arTape_at (fun z => E (c.workTapes i z)) (c.workTapePos i) ⟨j.val, hj⟩

private lemma arReadCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State)
    (j : Fin (N + 2)) (hj : j.val < N + 1) :
    (arTM E e M).tm.step (arReadCfg E e c q j) =
      arReadCfg E e c q ⟨j.val + 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : j.val < N + 1 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_pos hj]
  rw [arReadCfg_symbols E e c q j hj]
  refine Cfg.ext ?_ ?_ rfl ?_ ?_
  · have hb := arBuffer_update E c.workTapeSymbols ⟨j.val, hj⟩
    dsimp only at hb
    simp only [Action.apply, arReadCfg, hb]
  · simp [arReadCfg, arCfg, Action.apply]
  · funext i
    simp [arReadCfg, arPos, Action.apply, SignType.cast]
    omega
  · simp [arReadCfg, arCfg, Action.apply]

private lemma arReadCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State) (hc : c.state = some q) :
    ∀ j (hj : j ≤ N + 1), (arTM E e M).tm.runFrom (arCfg E e c) j =
      arReadCfg E e c q ⟨j, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; exact (arReadCfg_zero E e c q hc).symm
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact arReadCfg_step E e M c q ⟨j, by omega⟩ (by dsimp only; omega)

private def arTail {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) (r : ℕ) : ℤ → ArBlock N :=
  fun z j => if z = p ∧ r ≤ j.val then E w j else E (t z) j

private lemma arTail_full {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) :
    arTail E t p w (N + 1) = fun z => E (t z) := by
  funext z j
  have := j.isLt
  simp [arTail, show ¬N + 1 ≤ j.val by omega]

private lemma arTail_zero {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) :
    arTail E t p w 0 = fun z => E (Function.update t p w z) := by
  funext z j
  simp only [arTail, Nat.zero_le, and_true, Function.update_apply]
  split <;> rfl

/-- One leftward write extends the completed suffix by one bit. Distinct blocks
remain unchanged; within this block the only new index is the written index. -/
private lemma arTail_update {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) (j : Fin (N + 1)) :
    Function.update (arTape (arTail E t p w (j.val + 1))) (arPos N p j.val) (E w j) =
      arTape (arTail E t p w j.val) := by
  apply arTape_ext (N := N)
  intro z b
  simp only [Function.update_apply, arTape_at, arPos_eq, arTail]
  by_cases hz : z = p
  · subst z
    by_cases hj : b = j
    · subst b; simp
    · have hv : b.val ≠ j.val := fun h => hj (Fin.ext h)
      simp only [true_and, hj, and_false, if_false]
      split_ifs <;> first | rfl | omega
  · simp [hz]

private lemma arUpdated_tape {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (a : Action k Γ S) (i : Fin k) :
    (a.apply c).workTapes i = Function.update (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) := by
  cases hw : (a.workTapes i).1 with
  | none => simp [Action.apply, hw, Cfg.workTapeSymbols]
  | some w => simp [Action.apply, hw]

private def arMoveCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (a : Action k Γ S) (r : Fin (N + 2)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e (a.apply c) with
    state := some (.inr (arPending c.workTapeSymbols a, .inr r))
    workTapePos := fun i => arPos N (c.workTapePos i) 0 +
      (((N : ℤ) + 1) - r.val) * ((a.workTapes i).2 : ℤ) }

private def arWriteCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (a : Action k Γ S) (j : Fin (N + 1)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e (a.apply c) with
    state := some (.inr (arPending c.workTapeSymbols a, .inl j))
    workTapes := fun i => arTape (arTail E (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) (j.val + 1))
    workTapePos := fun i => arPos N (c.workTapePos i) j.val }

private lemma arMoveCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State)
    (r : Fin (N + 2)) (hr : r.val ≠ 0) :
    (arTM E e M).tm.step (arMoveCfg E e c a r) =
      arMoveCfg E e c a ⟨r.val - 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : r.val = 0 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_neg hr]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [arMoveCfg, arCfg, Action.apply]
  · funext i
    have hcast : ((r.val - 1 : ℕ) : ℤ) = (r.val : ℤ) - 1 := by omega
    simp only [Action.apply, arMoveCfg, arPending, hcast]
    ring
  · simp [arMoveCfg, arCfg, Action.apply]

private lemma arMoveCfg_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    (arTM E e M).tm.step (arMoveCfg E e c a 0) = arCfg E e (a.apply c) := by
  unfold MultiTapeTM.step
  dsimp only [arMoveCfg, arTM, arPending]
  rw [dif_pos (show (0 : Fin (N + 2)).val = 0 from rfl)]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arCfg, arPos, Fin.val_zero, SignType.coe_zero]
    ring
  · simp [arCfg, Action.apply]

private lemma arMoveCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    ∀ r (hr : r ≤ N + 1), (arTM E e M).tm.runFrom (arMoveCfg E e c a ⟨r, by omega⟩)
      (r + 1) = arCfg E e (a.apply c) := by
  intro r
  induction r with
  | zero => intro hr; exact arMoveCfg_finish E e M c a
  | succ r ih =>
    intro hr
    rw [MultiTapeTM.runFrom_succ_eq_step, arMoveCfg_step E e M c a ⟨r + 1, by omega⟩ (by simp)]
    exact ih (by omega)

private lemma arWriteCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State)
    (j : Fin (N + 1)) (hj : j.val ≠ 0) :
    (arTM E e M).tm.step (arWriteCfg E e c a j) =
      arWriteCfg E e c a ⟨j.val - 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : j.val = 0 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_neg hj]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [arWriteCfg, arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arWriteCfg, arPending]
    rw [arTail_update]
    congr 2
    omega
  · funext i
    simp [Action.apply, arWriteCfg, arPos, SignType.cast]
    omega
  · simp [arWriteCfg, arCfg, Action.apply]

private lemma arWriteCfg_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    (arTM E e M).tm.step (arWriteCfg E e c a 0) =
      arMoveCfg E e c a ⟨N + 1, by omega⟩ := by
  unfold MultiTapeTM.step
  dsimp only [arWriteCfg, arTM, arPending]
  rw [dif_pos (show (0 : Fin (N + 1)).val = 0 from rfl)]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [arMoveCfg, arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arMoveCfg, arCfg, arPending]
    rw [arTail_update]
    simp only [Fin.val_zero, arTail_zero]
    change arTape (fun z => E (Function.update (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) z)) =
      arTape (fun z => E ((a.apply c).workTapes i z))
    rw [arUpdated_tape]
  · funext i
    simp [arMoveCfg, arPos, Action.apply]
  · simp [arMoveCfg, arCfg, Action.apply]

private lemma arWriteCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    ∀ j (hj : j ≤ N), (arTM E e M).tm.runFrom (arWriteCfg E e c a ⟨j, by omega⟩)
      (j + 1) = arMoveCfg E e c a ⟨N + 1, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; exact arWriteCfg_finish E e M c a
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, arWriteCfg_step E e M c a ⟨j + 1, by omega⟩ (by simp)]
    exact ih (by omega)

/-- At the end of the read sweep, decoding recovers all scanned source symbols.
Execute the source input move and emission, save its pending work update in finite
control, and move left to the last bit of each block to start the write sweep. -/
private lemma arReadCfg_dispatch {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State) :
    (arTM E e M).tm.step (arReadCfg E e c q ⟨N + 1, by omega⟩) =
      arWriteCfg E e c (M.tm.tr q c.inputSymbol c.workTapeSymbols) ⟨N, by omega⟩ := by
  unfold MultiTapeTM.step
  dsimp only [arReadCfg, arTM]
  rw [dif_neg (show ¬N + 1 < N + 1 by omega)]
  simp only [arBuffer_full, arDecode_code]
  have hi : (arReadCfg E e c q ⟨N + 1, by omega⟩).inputSymbol.map e =
      c.inputSymbol := arCfg_input E e c
  simp only [arReadCfg, arBuffer_full] at hi
  rw [hi]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · apply Fin.ext
    simp [arWriteCfg, arCfg, Action.apply, moveInputPos]
    split <;> rfl
  · funext i
    simp only [Action.apply, arWriteCfg, arCfg, arTail_full]
  · funext i
    simp [arWriteCfg, arPos, Action.apply, SignType.cast]
    omega
  · simp [arWriteCfg, arCfg, Action.apply, List.map_append, Option.toList_map]

/-- Three sweeps plus two control transitions simulate one source step. Once the
source has halted, both represented configurations are absorbing. -/
private lemma arCfg_cycle {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) :
    (arTM E e M).tm.runFrom (arCfg E e c) (3 * (N + 1) + 2) =
      arCfg E e (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs,
      MultiTapeTM.runFrom_of_halt _ (show (arCfg E e c).state = none by simp [arCfg, hs])]
  | some q =>
    rw [show 3 * (N + 1) + 2 = (N + 1) + (1 + ((N + 1) + ((N + 1) + 1))) by omega,
      MultiTapeTM.runFrom_add, arReadCfg_run E e M c q hs (N + 1) (le_refl _)]
    rw [MultiTapeTM.runFrom_add]
    change (arTM E e M).tm.runFrom
      ((arTM E e M).tm.step (arReadCfg E e c q ⟨N + 1, by omega⟩)) _ = _
    rw [arReadCfg_dispatch, MultiTapeTM.runFrom_add,
      arWriteCfg_run E e M c _ N (le_refl _), arMoveCfg_run E e M c _ (N + 1) (le_refl _)]
    simp only [MultiTapeTM.step, hs]

private lemma arCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) :
    (arTM E e M).tm.runFrom (arCfg E e c) ((3 * (N + 1) + 2) * t) =
      arCfg E e (M.tm.runFrom c t) := by
  induction t with
  | zero => simp only [Nat.mul_zero, MultiTapeTM.runFrom_zero]
  | succ t ih =>
    rw [Nat.mul_succ, MultiTapeTM.runFrom_add, ih, arCfg_cycle,
      MultiTapeTM.runFrom_succ_eq_step']

private lemma arCfg_init {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (hE : E none = fun _ => none)
    (e : Bool ↪ Γ) (M : FinTM Γ) (x : List Bool) :
    (arTM E e M).tm.initCfg x = arCfg E e (M.tm.initCfg (x.map e)) := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [arCfg]
  · funext i p
    simp only [MultiTapeTM.initCfg, Cfg.init, arCfg, arTape, hE]
  · funext i
    simp [arCfg, arPos]

/-- The output decoder is total, with `false` for every non-image symbol. In the
computation invariant those cases are unreachable: an emitted source symbol remains
in the append-only output, which is a prefix of the completed embedded output. -/
private lemma arEmission_in_image {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) (x : List Bool) (t : ℕ) (a : Γ)
    (ha : M.tm.outputSymbol (M.tm.runFrom (M.tm.initCfg (x.map e)) t) = some a) :
    ∃ b, e b = a := by
  obtain ⟨hs, ho⟩ := (computesInTime_iff M _ _ _).1 (hM x)
  by_cases ht : t < T x.length
  · have hp := M.tm.output_prefix (M.tm.initCfg (x.map e)) (show t + 1 ≤ T x.length by omega)
    rw [ho] at hp
    have hm : a ∈ (M.tm.runFrom (M.tm.initCfg (x.map e)) (t + 1)).output := by
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, ha]
      simp
    obtain ⟨b, _, hb⟩ := List.mem_map.1 (hp.sublist.subset hm)
    exact ⟨b, hb⟩
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show T x.length ≤ t by omega)
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs,
      MultiTapeTM.outputSymbol_of_halt hs] at ha
    cases ha

private lemma arTM_computes {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (hE : E none = fun _ => none)
    (e : Bool ↪ Γ) (M : FinTM Γ) (x : List Bool) (w : List Bool) (t : ℕ)
    (h : M.ComputesInTime (x.map e) (w.map e) t) :
    (arTM E e M).ComputesInTime x w ((3 * (N + 1) + 2) * t) := by
  rw [computesInTime_iff, arCfg_init E hE, arCfg_run]
  obtain ⟨hs, ho⟩ := (computesInTime_iff M _ _ _).1 h
  simp only [arCfg, hs, ho, Option.map_none, true_and, List.map_map]
  simp only [Function.comp_def, arBit_embed]
  exact List.map_id w

/-- **Alphabet reduction** [AB09, Claim 1.5]: if a machine over a finite alphabet `Γ`
computes the binary string function `f` via `e : Bool ↪ Γ` within time `T`, then a
binary-alphabet machine with the *same number of work tapes* computes `f` within
`c · (T n + 1)` for some constant `c` (depending on the original machine).

**Proof sketch.** Fix a binary block code of length `L = ⌈log₂ |Γ|⌉` for `Option Γ`'s
non-blank symbols. `M'` keeps each of `M`'s work tapes as a block-encoded tape. One
step of `M` is simulated by: reading the `L` bits under each work head into the state
(`L` steps per tape, walking right), reading the input bit directly (its `e`-image is
determined by the table), computing `M`'s transition inside the finite state, writing
back the `L`-bit codes while returning left (`L` steps per tape), moving each head `L`
cells in the simulated direction, and emitting the decoded bit whenever `M` emits.
Total: at most `c` steps of `M'` per step of `M` with `c = O((k + 1) · L)` — the
`+ 1` covering the input-read, state-update, and emission work that remains even for
`k = 0` — plus a constant start-up. Logical blank is represented by the all-blank (`none`-cell) block — never-
visited blocks already have this shape, so no binary code needs reserving and no
initialization pass is required (phase-2 audit, finding 8). The invariant
relating block-encoded configurations to `M`'s configurations is preserved by each
simulated step, and `M`'s halting transfers.

**Implementation note (epoch 2, batch C).** As permitted by the brief's arbitrary
fixed-width scheme, the implementation uses a one-hot binary code of width
`L = Fintype.card Γ + 1` for nonblank symbols; logical blank remains all-`none`.
The proof factors through any injective code of positive width with this blank
property. All work tapes are swept simultaneously: `L` reads, one dispatch,
`L` writes, `L` moves, and one final control transition, for exactly `3 * L + 2`
steps per live source step. This also covers zero work tapes. The input is never
block-encoded. `arEmission_in_image` formalizes the output-prefix argument, while
the run correspondence maps the entire output through a total decoder. -/
theorem alphabet_reduction {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f fun n => c * (T n + 1) := by
  let E := arCode (Γ := Γ)
  have hE : E none = fun _ => none := rfl
  refine ⟨3 * (Fintype.card Γ + 1) + 2, arTM E e M, rfl, ?_⟩
  intro x
  exact (arTM_computes E hE e M x (f x) (T x.length) (hM x)).mono
    (Nat.mul_le_mul_left _ (Nat.le_succ _))

end

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/StateRenaming.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State renaming

Raw-layer transport of actions, configurations, and machines along maps of the
state type. This is the generic component shared by the oracle embedding
(`TCSlib.Complexity.TuringMachine.Oracle`, which renames states into
`State ⊕ Fin 3`) and the code normal form
(`TCSlib.Complexity.TuringMachine.Encoding`, which relabels states into
`Fin (numStates + 1)`), factored out per the epoch-1 audit (finding 5).

## Design

* `Turing.Action.mapState` and `Turing.Cfg.mapState` take an **arbitrary
  function** of the state types: mapping an action or configuration needs no
  injectivity, and the application lemma `Turing.Cfg.mapState_apply` holds for
  any function.
* `Turing.MultiTapeTM.relabelState` takes an **equivalence**: renaming a whole
  transition table along a non-injective map is not well defined (two states
  identified by the map may disagree on their transitions — epoch-1 audit,
  finding 5), and the inverse is used to read the table.
* The run-correspondence lemma is deliberately an **initialized-run** statement
  (`Turing.MultiTapeTM.relabelState_runFrom_init`), as the epoch-1 audit
  specified; an arbitrary-starting-configuration version can be added, with its
  own checked statement, if a result needs it.
* No finiteness assumptions anywhere: this is the raw parametric layer.

## Main definitions

* `Turing.Action.mapState` — rename an action's optional successor state
  (moved here from the oracle module; the definition is unchanged).
* `Turing.Cfg.mapState` — rename a configuration's optional state.
* `Turing.MultiTapeTM.relabelState` — transport a machine along a state
  equivalence.

## Main results

* `Turing.Cfg.mapState_apply` — renaming commutes with applying an action.
* `Turing.MultiTapeTM.relabelState_step` — renaming commutes with one step,
  including the absorbing halted case.
* `Turing.MultiTapeTM.relabelState_runFrom_init` — initialized runs correspond
  at every time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2 — the machine model whose state
  spaces are transported here; the module itself is internal infrastructure
  with no direct textbook counterpart.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

/-- Rename the states of an action along a function. -/
def Action.mapState {State' : Type*} (f : State → State') (a : Action k Symbol State) :
    Action k Symbol State' where
  inputTape := a.inputTape
  workTapes := a.workTapes
  output := a.output
  state := a.state.map f

/-- Rename a configuration's optional state along a function, preserving the
input position, work tapes, head positions, and output. -/
def Cfg.mapState {State' : Type*} {input : List Symbol} (f : State → State')
    (cfg : Cfg k Symbol State input) : Cfg k Symbol State' input :=
  { cfg with state := cfg.state.map f }

/-- State renaming commutes with applying an action (any function; no
injectivity needed, since the action is supplied explicitly). -/
lemma Cfg.mapState_apply {State' : Type*} {input : List Symbol} (f : State → State')
    (a : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    (a.mapState f).apply (cfg.mapState f) = (a.apply cfg).mapState f := rfl

/-- Transport a machine along a state **equivalence**: the initial state is
mapped forward, and each transition reads the table through the inverse. An
arbitrary function would not suffice here — identifying two states with
different transitions leaves no well-defined table (epoch-1 audit, finding 5). -/
def MultiTapeTM.relabelState {State' : Type*} (tm : MultiTapeTM k Symbol State)
    (e : State ≃ State') : MultiTapeTM k Symbol State' where
  q₀ := e tm.q₀
  tr := fun q inp ws => (tm.tr (e.symm q) inp ws).mapState e

/-- Relabeling commutes with each step, including the absorbing halted case. -/
lemma MultiTapeTM.relabelState_step {State' : Type*} {input : List Symbol}
    (tm : MultiTapeTM k Symbol State) (e : State ≃ State')
    (cfg : Cfg k Symbol State input) :
    (tm.relabelState e).step (cfg.mapState e) = (tm.step cfg).mapState e := by
  have hin : (cfg.mapState e).inputSymbol = cfg.inputSymbol := rfl
  have hwork : (cfg.mapState e).workTapeSymbols = cfg.workTapeSymbols := rfl
  unfold MultiTapeTM.step
  cases hs : cfg.state with
  | none => simp [Cfg.mapState, hs]
  | some q =>
    rw [show (cfg.mapState e).state = some (e q) by
      simp only [Cfg.mapState, hs, Option.map_some]]
    dsimp only
    rw [hin, hwork]
    simp only [MultiTapeTM.relabelState, Equiv.symm_apply_apply]
    exact Cfg.mapState_apply e _ cfg

/-- Initialized runs correspond at every time. This is deliberately an
initialized-run lemma (epoch-1 audit, finding 5); an arbitrary-start version
would be a separate statement. -/
lemma MultiTapeTM.relabelState_runFrom_init {State' : Type*}
    (tm : MultiTapeTM k Symbol State) (e : State ≃ State') (input : List Symbol)
    (t : ℕ) :
    (tm.relabelState e).runFrom ((tm.relabelState e).initCfg input) t =
      (tm.runFrom (tm.initCfg input) t).mapState e :=
  MultiTapeTM.runFrom_comm_of_step (Cfg.mapState e)
    (tm.relabelState_step e) (tm.initCfg input) t

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Finite.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Basic
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite Turing machines

The raw model `Turing.MultiTapeTM k Symbol State` deliberately does not require `Symbol` or
`State` to be finite: semantics, simulations, and resource counting do not need it, and
compound state types arise freely in constructions. Finiteness is nevertheless
mathematically essential for complexity theory — with infinitely many states a machine can
memorize its whole input in the state and decide any language in linear time, and an
infinite transition table has no string encoding.

This file provides the bundled layer `Turing.FinTM`: a machine together with `Fintype` and
`DecidableEq` instances for its state type. All headline definitions of the Chapter 1
development (`DTIME`, `P`, machine encodings, the universal machine) are stated exclusively
over `FinTM`, so the finiteness hypothesis can never be dropped by accident. The instances
are carried as *data* (not `Finite` propositions) because the machine-encoding function
`⌞M⌟` must enumerate the transition table.

The alphabet parameter `Symbol` stays explicit and unbundled: the Chapter 1 headline
definitions fix `Symbol := Bool` (see `TCSlib.Complexity.ClassP.DTIME`), and results that
need a finite alphabet for a general `Symbol` take `[Fintype Symbol]` hypotheses at use
sites.

## Main definitions

* `Turing.FinTM Symbol` — a multi-tape TM over alphabet `Option Symbol` with a bundled
  finite state type. [AB09, §1.2]
* `Turing.FinTM.ComputesInTime` — the machine halts on `input` within `t` steps with
  `output` on the output tape (time-only variant of
  `Turing.MultiTapeTM.ComputesInTimeAndSpace`). [AB09, Definition 1.3]
* `Turing.FinTM.ComputesFunInTime` — the machine computes `f` in time `T`.
  [AB09, Definition 1.3]
* `Turing.FinTM.Computes` — the machine computes `f` with no time constraint; the
  notion of computability underlying the uncomputability results. [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.ComputesInTime.mono` — halting is absorbing, so the time bound can be
  weakened.
* `Turing.FinTM.ComputesInTime.output_unique` — determinism: a machine has at most one
  completed output on a given input.
* `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.Computes.exists_computesInTime_iff` —
  the space-free unfolding of a timed computation, and the completed-output
  characterization of a total machine (promoted from the epoch-1 fill).
* `Turing.FinTM.not_computesInTime_zero` — no machine computes anything in zero steps
  (the initial state is not the halting state).
* `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.output_prefix` — raw-layer
  output lemmas (at most one symbol is emitted per step, and output only grows), stated
  here rather than in the vendored `Deterministic.lean` to keep the vendored files
  unmodified.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.3.)
-/

namespace Turing

/-!
### Raw-layer output lemmas

Additions on top of the vendored files (kept here so the vendored `Deterministic.lean`
stays byte-comparable with upstream).
-/

namespace MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The output of an initialized run after `t` steps has length at most `t`: each step
appends at most one symbol.

**Proof sketch.** Induction on `t` with `Turing.MultiTapeTM.runFrom_succ_eq_step'` and
`Turing.MultiTapeTM.step_output` (`Option.toList` has length at most one); the initial
output is `[]`. -/
theorem output_length_le (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    ((tm.runFrom (tm.initCfg input) t).output).length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    have hone : (tm.outputSymbol (tm.runFrom (tm.initCfg input) t)).toList.length ≤ 1 := by
      cases tm.outputSymbol (tm.runFrom (tm.initCfg input) t) <;> simp
    simp only [List.length_append]
    omega

/-- Output is monotone along a run: the output at an earlier time is a prefix of the
output at any later time.

**Proof sketch.** It suffices to treat one step (`Turing.MultiTapeTM.step_output`: a
step appends), then induct on the difference using
`Turing.MultiTapeTM.runFrom_add` and transitivity of `List.IsPrefix`. -/
theorem output_prefix (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t t' : ℕ} (h : t ≤ t') :
    (tm.runFrom cfg t).output <+: (tm.runFrom cfg t').output := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [MultiTapeTM.runFrom_add]
  generalize tm.runFrom cfg t = c
  induction d with
  | zero => simp
  | succ d ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    exact ih.trans (List.prefix_append _ _)

end MultiTapeTM

/-- A multi-tape Turing machine over the alphabet `Option Symbol` bundled with a finite
state type. This is the machine of [AB09, §1.2] up to the declared model variations
(append-only output tape, start-marker-free initialization — see the deviations list in
`TCSlib.Complexity.ClassP.DTIME`): the raw `MultiTapeTM` is internal plumbing, and
every headline complexity-theoretic definition is stated over `FinTM`.

The instances are data (`Fintype`/`DecidableEq`, not `Finite`) because encoding a machine
as a string requires enumerating its transition table. -/
structure FinTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible, needed to tabulate the transition function -/
  [decEqState : DecidableEq State]
  /-- the underlying machine -/
  tm : MultiTapeTM k Symbol State

namespace FinTM

attribute [instance] FinTM.fintypeState FinTM.decEqState

variable {Symbol : Type}

/-- The machine `M` halts on `input` within `t` steps with `output` written on its output
tape. Time-only variant of `Turing.MultiTapeTM.ComputesInTimeAndSpace` (the space used is
existentially discarded). [AB09, Definition 1.3] -/
def ComputesInTime (M : FinTM Symbol) (input output : List Symbol) (t : ℕ) : Prop :=
  ∃ s, M.tm.ComputesInTimeAndSpace input output t s

/-- The machine `M` computes the string function `f`, halting within `T |input|` steps on
every input. [AB09, Definition 1.3: "M computes f in T(n)-time"] -/
def ComputesFunInTime (M : FinTM Symbol) (f : List Symbol → List Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ input : List Symbol, M.ComputesInTime input (f input) (T input.length)

/-- The machine `M`, over alphabet `Γ`, computes the string function `f` on `α`-strings
*via* the symbol embedding `e : α ↪ Γ`: on every input `x.map e` it halts within
`T |x|` steps with `(f x).map e` on its output tape. This is how a machine over a
larger alphabet is said to compute a function on a smaller one; it is the interface of
the alphabet-robustness results [AB09, §1.3.1]. -/
def ComputesFunInTimeVia {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) : Prop :=
  ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length)

/-- The machine `M` *computes* the string function `f`, with no time constraint: on
every input it eventually halts with `f input` on the output tape. This is the notion
of computability underlying the uncomputability results [AB09, §1.4, p. 20; §1.5];
`Turing.FinTM.ComputesFunInTime` is the time-bounded refinement, and the two are
related by `Turing.FinTM.ComputesFunInTime.computes` (below) and
`Turing.FinTM.Computes.exists_computesFunInTime`
(in `TCSlib.Complexity.Uncomputability.Computable`). -/
def Computes (M : FinTM Symbol) (f : List Symbol → List Symbol) : Prop :=
  ∀ input : List Symbol, ∃ t, M.ComputesInTime input (f input) t

/-- Halting is absorbing, so a time bound can be weakened: if `M` produces `output`
within `t` steps it also does so within any `t' ≥ t` steps.

**Proof sketch.** By `Turing.MultiTapeTM.runFrom_add` the run to step `t'` factors through
step `t`; the state there is `none`, so `Turing.MultiTapeTM.runFrom_of_halt` shows the
configuration no longer changes, and in particular state and output at step `t'` agree with
step `t`. The space used up to step `t'` exists (it is whatever `spaceUsed` evaluates to),
which discharges the existential. -/
theorem ComputesInTime.mono {M : FinTM Symbol} {input output : List Symbol} {t t' : ℕ}
    (h : M.ComputesInTime input output t) (hle : t ≤ t') :
    M.ComputesInTime input output t' := by
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h ⊢
  obtain ⟨s, hhalt, hout, -⟩ := h
  have hrun : M.tm.runFrom (M.tm.initCfg input) t' = M.tm.runFrom (M.tm.initCfg input) t := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  exact ⟨_, by rw [hrun]; exact hhalt, by rw [hrun]; exact hout, rfl⟩

/-- No machine computes anything in zero steps: the initial configuration is in the
initial state, which is not the halting state. In particular a time budget of `0`
(e.g. from a vanishing time bound) is never satisfiable. -/
theorem not_computesInTime_zero (M : FinTM Symbol) (input output : List Symbol) :
    ¬M.ComputesInTime input output 0 := by
  rintro ⟨s, hhalt, -⟩
  simp [MultiTapeTM.runFrom_zero] at hhalt

/-- Determinism of completed outputs: a machine has at most one completed output on a
given input — if `M` halts on `input` with `w` within `t` steps and with `w'` within
`t'` steps, then `w = w'`. Together with `Turing.FinTM.ComputesInTime.mono` this
makes the halting relation of a machine a partial function.

**Proof.** Absorb both computations to time `max t t'`
(`Turing.FinTM.ComputesInTime.mono`); both then name the output of one and the same
run. -/
theorem ComputesInTime.output_unique {M : FinTM Symbol} {input w w' : List Symbol}
    {t t' : ℕ} (h : M.ComputesInTime input w t) (h' : M.ComputesInTime input w' t') :
    w = w' := by
  have h₁ := h.mono (Nat.le_max_left t t')
  have h₂ := h'.mono (Nat.le_max_right t t')
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h₁ h₂
  obtain ⟨s, -, hout, -⟩ := h₁
  obtain ⟨s', -, hout', -⟩ := h₂
  rw [← hout, ← hout']

/-- A time-bounded computation is in particular a computation. -/
theorem ComputesFunInTime.computes {M : FinTM Symbol} {f : List Symbol → List Symbol}
    {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) : M.Computes f :=
  fun input => ⟨T input.length, h input⟩

/-- `ComputesInTime` without the space witness: the machine has halted by time `t`
with completed output exactly `w`. The space existential is uniquely determined by
the run, so it can always be discharged. (Promoted from the epoch-1 fill and
generalized from `Bool` to an arbitrary alphabet, per the epoch-1 audit,
finding 4.) -/
theorem computesInTime_iff (M : FinTM Symbol) (x w : List Symbol) (t : ℕ) :
    M.ComputesInTime x w t ↔
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = w := by
  constructor
  · rintro ⟨s, hs, ho, -⟩
    exact ⟨hs, ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨_, hs, ho, rfl⟩

/-- A total machine's completed outputs are exactly its prescribed values: if `M`
computes `g`, then `M` halts on `x` with completed output `w` — in some number of
steps — iff `w = g x`. Existence of a computation together with determinism of
completed outputs (`Turing.FinTM.ComputesInTime.output_unique`). (Promoted from
the epoch-1 fill per the epoch-1 audit, finding 4.) -/
theorem Computes.exists_computesInTime_iff {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x := by
  obtain ⟨t, ht⟩ := hM x
  constructor
  · rintro ⟨s, hs⟩
    exact hs.output_unique ht
  · rintro rfl
    exact ⟨t, ht⟩

end FinTM

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Configuration.lean =====

```lean
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Aviv Bar Natan

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to its location at our mathlib pin,
  `Mathlib.Data.Sign.Defs`; dropped the cslib-internal `Cslib.Init` import;
* added the repository-standard `set_option` header.
The mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Data.Sign.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configurations of Multi-Tape Turing Machines

Configurations of a multi-tape Turing machine with a read-only input tape, `k` work tapes and one
write-only output tape, together with what a single transition does to one and the space measure
read off a list of them.

## Design

Nothing here mentions a machine. A step is described in two parts: an `Action`, recording
which way the input head moves, what is written and where the work heads move, which symbol is
emitted and which state follows; and `Action.apply`, which carries it out on a
configuration.

The output tape is part of the configuration, so the string emitted along a run can be read off
the configuration the run ends in.

## Main definitions

* `Cfg`: the configuration: the internal state, the tape contents and head positions, and the
    output tape
* `Action`: what a machine does in one step
* `Action.apply`: the effect of one action on a configuration
* `Cfg.Halted`, `Cfg.init`: halting, and the configuration a machine starts in
* `spaceUsedOfCfgs`: work tape cells touched along a list of configurations

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape Turing machine.)
* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
  (§2.3, §2.5: the machine model and the space measure.)
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/-- What a machine does in one step. -/
structure Action (k : ℕ) (Symbol State : Type*) where
  /-- The movement (attempt) of the input head. -/
  inputTape : SignType
  /-- Actions on the work tapes: optionally a symbol to write and the head movement. -/
  workTapes : Fin k → (Option (Option Symbol)) × SignType
  /-- An optional symbol to output. -/
  output : Option Symbol
  /-- The successor state or none to halt. -/
  state : Option State

/--
The configurations of a Turing machine is relative to the input of the machine and consist of:
- an `Option`al state (or none for the halting state),
- the position of the input head (shifted by one),
- the contents of the work tape,
- the positions of the work tape heads,
- the contents of the write-only output tape
-/
@[ext]
structure Cfg (k : ℕ) (Symbol State : Type*) (input : List Symbol) where
  /-- the state of the TM (or none for the halting state) -/
  state : Option State
  /-- the position of the input head, shifted by one -/
  inputPos : Fin (input.length + 2)
  /-- the work tapes -/
  workTapes : Fin k → ℤ → Option Symbol
  /-- the positions of the heads on the work tapes -/
  workTapePos : Fin k → ℤ
  /-- the contents of the write-only output tape -/
  output : List Symbol
deriving Inhabited

/-- Two configurations of a machine without work tapes are equal if their states, input head
positions and outputs are equal. -/
lemma Cfg.ext_zero_tapes {Symbol State : Type*} {input : List Symbol}
    {cfg₁ cfg₂ : Cfg 0 Symbol State input} (state : cfg₁.state = cfg₂.state)
    (inputPos : cfg₁.inputPos = cfg₂.inputPos) (output : cfg₁.output = cfg₂.output) :
    cfg₁ = cfg₂ :=
  Cfg.ext state inputPos (funext fun i => i.elim0) (funext fun i => i.elim0) output

/-- Attempt to move the input tape head.
The machine can only read one empty cell outside of the input,
any attempted movement beyond that results in no movement.

The addition is performed in `ℤ` before clamping. Performing it in `Fin (n + 2)` would wrap an
outward boundary move to the opposite end of the input. -/
@[scoped grind =]
def moveInputPos {n : ℕ} (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2) :=
  let p := ((pos.val : ℤ) + (m.cast : ℤ)).toNat
  if h : p < n + 2 then ⟨p, h⟩ else ⟨n + 1, by omega⟩

@[simp]
lemma moveInputPos_zero {n : ℕ} (pos : Fin (n + 2)) :
    moveInputPos pos 0 = pos := by
  apply Fin.ext
  simp [moveInputPos, pos.isLt]

@[simp]
lemma moveInputPos_leftBoundary {n : ℕ} :
    moveInputPos (0 : Fin (n + 2)) (-1) = 0 := by
  apply Fin.ext
  simp [moveInputPos]

@[simp]
lemma moveInputPos_rightBoundary {n : ℕ} :
    moveInputPos (⟨n + 1, by omega⟩ : Fin (n + 2)) 1 = ⟨n + 1, by omega⟩ := by
  -- ported proof: `dite_eq_right` does not exist at our mathlib pin
  apply Fin.ext
  simp only [moveInputPos, SignType.coe_one]
  split <;> simp <;> omega

/-- A left move away from the left input boundary decrements the native input position. -/
lemma moveInputPos_neg_of_ne_left {n : ℕ} (p : Fin (n + 2)) (h : p ≠ 0) :
    moveInputPos p .neg = ⟨p.val - 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.neg_eq_neg_one, SignType.coe_neg_one]
  split <;> simp <;> omega

/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  -- ported proof: `dite_eq_left` does not exist at our mathlib pin
  have hlt := p.isLt
  apply Fin.ext
  simp only [moveInputPos, SignType.pos_eq_one, SignType.coe_one]
  split <;> simp <;> omega

/-- The symbol currently under the input tape head. -/
def Cfg.inputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos = 0 then none
  else if h₂ : cfg.inputPos = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by
    -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
    have h0 : (cfg.inputPos : ℕ) ≠ 0 := fun hv => h₁ (Fin.val_eq_zero_iff.mp hv)
    have hlt := cfg.inputPos.isLt
    omega)

@[simp]
lemma inputSymbolInner {cfg : Cfg k Symbol State input} (p : ℕ)
    (h₁ : cfg.inputPos.val = 1 + p)
    (h₂ : p < input.length) :
    cfg.inputSymbol = some input[p] := by
  -- ported proof: `grind` at our pin does not bridge the `Fin` equality with `.val`
  have h0 : ¬cfg.inputPos = 0 := fun hz => by
    rw [hz] at h₁
    simp at h₁
    omega
  have hL : ¬(cfg.inputPos : ℕ) = input.length + 1 := by omega
  simp only [Cfg.inputSymbol, dif_neg h0, dif_neg hL]
  simp only [show (cfg.inputPos : ℕ) - 1 = p from by omega]

/-- The symbol read by work tape `i`. -/
def Cfg.workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) : Option Symbol :=
  cfg.workTapes i (cfg.workTapePos i)

/-- A configuration is halted when it has no state to continue from. -/
abbrev Cfg.Halted (cfg : Cfg k Symbol State input) : Prop := cfg.state = none

/-- The initial configuration for a starting state and an input string. -/
@[simp]
def Cfg.init (q₀ : State) (input : List Symbol) : Cfg k Symbol State input :=
  ⟨some q₀, 1, fun _ _ => none, fun _ => 0, []⟩

/--
The effect of an action on a configuration: move the input head, write and move on the work tapes,
append the emitted symbol to the output tape, and go to the successor state. This is the part of a
step that does not depend on how the action was chosen.
-/
@[simp]
def Action.apply (action : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input where
  state := action.state
  inputPos := moveInputPos cfg.inputPos action.inputTape
  workTapes i := match (action.workTapes i).1 with
    | none => cfg.workTapes i
    | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
  workTapePos i := cfg.workTapePos i + (action.workTapes i).2
  output := cfg.output ++ action.output.toList

/-- A work tape head moves by at most one cell when an action is applied. -/
lemma workTapePos_apply_le (action : Action k Symbol State)
    (cfg : Cfg k Symbol State input) (i : Fin k) :
    |(action.apply cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  simp only [Action.apply, add_sub_cancel_left, abs_le, SignType.cast]
  grind

/-- The work tape cells visited by the head of tape `i` along a list of configurations. -/
def visitedOfCfgs (cfgs : List (Cfg k Symbol State input)) (i : Fin k) : Finset ℤ :=
  (cfgs.map (·.workTapePos i)).toFinset

/-- The number of work tape cells touched by the heads along a list of configurations. -/
def spaceUsedOfCfgs (cfgs : List (Cfg k Symbol State input)) : ℕ :=
  ∑ i, (visitedOfCfgs cfgs i).card

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Deterministic.lean =====

```lean
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to `Mathlib.Data.Sign.Defs` (its location at our mathlib
  pin); dropped the cslib-internal `Cslib.Init` import; added
  `Mathlib.Logic.Embedding.Basic` explicitly (upstream receives it transitively);
* dropped the relational semantics (`TransitionRelation`,
  `relatesInSteps_iff_runFrom_eq`) because it depends on the cslib-internal
  `Cslib.Foundations.Data.RelatesInSteps`; the iterated-step semantics `runFrom` is
  self-contained and suffices for the Chapter 1 development. Re-add it (or migrate to
  upstream cslib) when the step-indexed relational view is needed, e.g. for
  nondeterministic machines;
* added the repository-standard `set_option` header.
The remaining mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Embedding.Basic
import TCSlib.Complexity.TuringMachine.Configuration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AB09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Pap94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AB09], Claim 1.8). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Main definitions

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step,
    our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a machine computes a function between specified encodings,
    respecting time and space bounds on each actual input.
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

## References

* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013.
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM

variable {input : List Symbol} {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `TCSlib.Complexity.TuringMachine.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} :
    tm.runFrom cfg 0 = cfg := by
  simp [runFrom]

lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  simp [runFrom, Function.iterate_succ_apply]

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp [runFrom, Function.iterate_succ_apply']

/-- Running `a + b` steps equals running `b` steps from the configuration reached after `a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  unfold runFrom
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- If a function `f` that maps the configurations of one TM to those of another one commutes with
their `step` function, then it also commutes with their `runFrom` function. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input input' : List Symbol}
    {tm : MultiTapeTM k Symbol State} {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- Running from a halting configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.runFrom cfg t').workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := by
  unfold spaceUsed spaceUsedByTape spaceUsedOfCfgs
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card ?_
  ext z
  simp [visitedByTapeHead, visitedOfCfgs]

end Space

open Cfg

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- The output does not change after the machine has halted. -/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses exactly `s` space.
Note that this does not require the alphabet or state set to be finite. -/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧
  (tm.runFrom (tm.initCfg input) t).output = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A machine computes `f` between the supplied encodings, with bounds depending on the input.
The machine's alphabet and state type need not be finite. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ComputesInTimeAndSpace tm (encIn a) (encOut (f a)) t' s'

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunInTimeAndSpace tm encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunInTimeAndSpace tm encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

open Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
def haltsAtStep (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) : Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol State}
    {input : List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.runFrom (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.runFrom (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, runFrom]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, runFrom_add, tm.runFrom_of_halt _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.runFrom_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.runFrom_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Oracle.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle Turing machines

An oracle Turing machine [AB09, §3.4, Definition 3.4; pulled forward to Chapter 1 to
validate the model architecture] is a multi-tape machine with one additional designated
*query tape* and three designated states `qQuery`, `qYes`, `qNo`. Whenever the machine
enters `qQuery`, the string currently written on the query tape is submitted to the oracle
`O`: in a single step the machine moves to `qYes` if the query is in `O` and to `qNo`
otherwise, with all tapes and heads unchanged.

## Design

This file is the architectural test of the `Action`/`Action.apply` split: an oracle machine
reuses the configurations `Turing.Cfg (k + 1)` (the query tape is the extra work tape, at
index `Fin.last k`) and the action application of the plain model, and differs *only* in how
the next action is chosen — the step function is parametrized by the oracle
`O : Language Symbol`. Time and space measures therefore transfer unchanged.

Definitional choices worth auditing:

* **The query string** (`OracleTM.queryString`) is read from cell `0` of the query tape
  rightward up to (excluding) the first blank cell; if the whole nonnegative half-tape is
  blank-free (possible for an arbitrary configuration, though not for one reachable from an
  initial configuration), the query is defined to be `[]`. [AB09] leaves the extraction
  convention implicit; this is one concrete faithful reading.
* **The answer step** changes only the state; heads and tapes stay put. Some texts
  instead erase the query tape on each answer. The two conventions are equivalent up to
  *polynomial* overhead, but **not** constant overhead: computing the parity of `n`
  distinct length-`n` queries takes `O(n)` steps with a persistent tape and `Ω(n²)`
  steps with auto-erasure (`audits/phase1-findings.md`, finding 3, case 12).
  Consequently, exact `DTIME`-level bounds must never be transferred across this
  convention; class-level results (`Pᴼ` etc.) are unaffected.
* `qYes`/`qNo` are ordinary states from the machine's point of view (its transition
  function handles them); only `qQuery` triggers special behavior. The machine may query
  repeatedly. This reading presumes the three special states are pairwise distinct,
  which the raw structure does not enforce (e.g. with `qYes = qQuery` the machine
  re-queries forever after a positive answer): results at the faithful interface assume
  `OracleTM.WellFormed`. Note that
  `q₀ = qQuery` is legitimate and deliberately allowed (the machine then submits the
  empty query on its first step).

## Main definitions

* `Turing.OracleTM` — the oracle machine. [AB09, Definition 3.4]
* `Turing.OracleTM.WellFormed` — the three special states are pairwise distinct; the
  standing hypothesis of the faithful interface (oracle complexity classes will require
  it).
* `Turing.OracleTM.step`, `Turing.OracleTM.runFrom` — semantics relative to an oracle.
* `Turing.OracleTM.ComputesInTime` — output and time bound relative to an oracle.
* `Turing.Action.extend`, `Turing.Cfg.embedOracle`, `Turing.OracleTM.ofMultiTapeTM` —
  the embedding of plain machines as oracle machines that never query (state renaming
  via `Turing.Action.mapState`, now in `TCSlib.Complexity.TuringMachine.StateRenaming`).
* `Turing.OracleTM.plainEmptyOracle` — the converse direction: an oracle machine run
  with the empty oracle, as a plain `k + 1`-tape machine in exact lockstep.

## Main results (sanity checks for the architecture)

* `Turing.OracleTM.step_eq_of_ne_qQuery` — away from `qQuery`, the step does not depend
  on the oracle.
* `Turing.OracleTM.ofMultiTapeTM_wellFormed` — the embedding produces well-formed
  machines.
* `Turing.OracleTM.runFrom_ofMultiTapeTM` — an embedded plain machine runs in lockstep
  with the original, under every oracle.
* `Turing.OracleTM.computesInTime_ofMultiTapeTM` — hence its input/output behavior and
  time bounds are oracle-independent and agree with the plain machine's.
* `Turing.OracleTM.runFrom_plainEmptyOracle` — the empty-oracle elimination runs in
  exact lockstep.
* `Turing.OracleTM.queryString_length_le` — in an initialized run, the query after `t`
  steps has length at most `t`.
* `Turing.OracleTM.runFrom_workTapes_blank` — in an initialized run, cells at distance
  `≥ t` are still blank after `t` steps; the certificate that the no-blank fallback in
  `queryString` is unreachable from initialization.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4: oracle machines; Definition 3.4.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- An oracle Turing machine with `k` ordinary work tapes, one query tape (the work tape
of index `Fin.last k` in its configurations `Cfg (k + 1)`), and designated query and
answer states. Finiteness of `State` is deferred exactly as for `MultiTapeTM`, and so is
distinctness of the three special states: the raw structure allows them to coincide
(with degenerate behavior, e.g. `qYes = qQuery` re-queries forever after a positive
answer), and the faithful interface imposes `OracleTM.WellFormed`.
[AB09, Definition 3.4] -/
structure OracleTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- entering this state submits the query tape's contents to the oracle -/
  qQuery : State
  /-- the state the oracle answer step moves to on a positive answer -/
  qYes : State
  /-- the state the oracle answer step moves to on a negative answer -/
  qNo : State
  /-- transition function on the `k + 1` work tapes (the last being the query tape);
  consulted in every state except `qQuery` -/
  tr (q : State) (input : Option Symbol) (work : Fin (k + 1) → Option Symbol) :
    Action (k + 1) Symbol State

namespace OracleTM

variable {M : OracleTM k Symbol State}

/-- Well-formedness of an oracle machine: the query state and the two answer states are
pairwise distinct. Without this, the advertised semantics degenerates: with
`qYes = qQuery` a positive answer re-queries the unchanged tape forever (a negative
answer may still reach a distinct `qNo` and halt normally), and with all three states
collapsed the machine loops once the common query state is reached (an initial state
elsewhere can still halt via the table without ever querying). Moreover `qYes = qNo`
alone makes the step function — hence every run — oblivious to the oracle. This is the
standing hypothesis of the faithful oracle interface —
oracle complexity classes will require it. `q₀ = qQuery` is deliberately allowed: such a
machine simply submits the empty query on its first step.
(`audits/phase1-findings.md`, finding 2.) -/
structure WellFormed (M : OracleTM k Symbol State) : Prop where
  /-- the query state is not the positive-answer state -/
  qQuery_ne_qYes : M.qQuery ≠ M.qYes
  /-- the query state is not the negative-answer state -/
  qQuery_ne_qNo : M.qQuery ≠ M.qNo
  /-- the two answer states are distinct -/
  qYes_ne_qNo : M.qYes ≠ M.qNo

/-- The index of the query tape among the `k + 1` work tapes. -/
def queryTapeIdx (k : ℕ) : Fin (k + 1) := Fin.last k

open Classical in
/-- The query string of a configuration: the contents of the query tape from cell `0`
rightward, up to (excluding) the first blank cell. If no blank cell exists on the
nonnegative half-tape — impossible in configurations reachable from an initial
configuration, but possible for an arbitrary one — the query is `[]`. -/
noncomputable def queryString (cfg : Cfg (k + 1) Symbol State input) : List Symbol :=
  if h : ∃ n : ℕ, cfg.workTapes (queryTapeIdx k) (n : ℤ) = none then
    (List.range (Nat.find h)).filterMap fun n => cfg.workTapes (queryTapeIdx k) (n : ℤ)
  else []

open Classical in
/-- One step of the oracle machine `M` relative to the oracle `O`. In state `qQuery` the
machine moves to `qYes` or `qNo` according to whether the current query string is in `O`,
leaving tapes, head positions and output unchanged; in every other state it steps by its
transition function exactly like a plain machine. [AB09, §3.4] -/
noncomputable def step (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) : Cfg (k + 1) Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q =>
    if q = M.qQuery then
      { cfg with state := some (if queryString cfg ∈ O then M.qYes else M.qNo) }
    else
      (M.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration of an oracle machine: all `k + 1` work tapes (including the
query tape) blank. -/
@[simp]
def initCfg (M : OracleTM k Symbol State) (input : List Symbol) :
    Cfg (k + 1) Symbol State input :=
  Cfg.init M.q₀ input

/-- The configuration reached by running `M` with oracle `O` for `t` steps from `cfg`. -/
noncomputable def runFrom (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) : Cfg (k + 1) Symbol State input :=
  (M.step O)^[t] cfg

/-- `M` with oracle `O` halts on `input` within `t` steps with `output` on its output
tape. Time-only, mirroring `Turing.FinTM.ComputesInTime`. -/
def ComputesInTime (M : OracleTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) : Prop :=
  (M.runFrom O (M.initCfg input) t).state = none ∧
  (M.runFrom O (M.initCfg input) t).output = output

/-- Away from the query state, a step of an oracle machine does not depend on the oracle. -/
theorem step_eq_of_ne_qQuery (O₁ O₂ : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state ≠ some M.qQuery) :
    M.step O₁ cfg = M.step O₂ cfg := by
  unfold step
  cases hs : cfg.state with
  | none => rfl
  | some q =>
    have hne : q ≠ M.qQuery := fun hq => h (by rw [hs, hq])
    dsimp only
    rw [if_neg hne, if_neg hne]

/-- Applying any action changes a work-tape cell only at the old head position. -/
private lemma apply_workTapes_eq_of_ne {k' : ℕ} (a : Action k' Symbol State)
    (cfg : Cfg k' Symbol State input) (i : Fin k') {z : ℤ}
    (hz : z ≠ cfg.workTapePos i) :
    (a.apply cfg).workTapes i z = cfg.workTapes i z := by
  dsimp only [Action.apply]
  rcases h : (a.workTapes i).1 with _ | s
  · rfl
  · exact Function.update_of_ne hz _ _

/-- A work-tape head moves by at most one cell in a single oracle step. -/
lemma workTapePos_step_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (i : Fin (k + 1)) :
    |(M.step O cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  unfold step
  split
  · simp
  · split
    · simp
    · exact workTapePos_apply_le _ cfg i

/-- An oracle step writes only at the old head position. -/
lemma workTapes_step_eq_of_ne (M : OracleTM k Symbol State) (O : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (i : Fin (k + 1)) {z : ℤ}
    (hz : z ≠ cfg.workTapePos i) :
    (M.step O cfg).workTapes i z = cfg.workTapes i z := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · exact apply_workTapes_eq_of_ne _ cfg i hz

/-- The two run invariants of an initialized oracle run: after `t` steps every work
head is within distance `t` of the origin, and every cell at distance at least `t` is
still blank. -/
private lemma runFrom_workTapes_invariant (M : OracleTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) : ∀ t : ℕ,
    (∀ i, |(M.runFrom O (M.initCfg x) t).workTapePos i| ≤ (t : ℤ)) ∧
    (∀ i (z : ℤ), (t : ℤ) ≤ |z| → (M.runFrom O (M.initCfg x) t).workTapes i z = none) := by
  intro t
  induction t with
  | zero =>
    constructor
    · intro i
      simp [runFrom]
    · intro i z _
      simp [runFrom]
  | succ t ih =>
    obtain ⟨hpos, hblank⟩ := ih
    have hstep : M.runFrom O (M.initCfg x) (t + 1) =
        M.step O (M.runFrom O (M.initCfg x) t) :=
      Function.iterate_succ_apply' _ _ _
    constructor
    · intro i
      rw [hstep]
      have h1 := M.workTapePos_step_le O (M.runFrom O (M.initCfg x) t) i
      have h2 := hpos i
      rw [abs_le] at h1 h2 ⊢
      omega
    · intro i z hz
      rw [hstep]
      have hz' : (t : ℤ) ≤ |z| := le_trans (by omega) hz
      have hne : z ≠ (M.runFrom O (M.initCfg x) t).workTapePos i := by
        intro hzeq
        have h2 := hpos i
        rw [← hzeq] at h2
        have h3 : ((t : ℤ) + 1) ≤ |z| := by exact_mod_cast hz
        have h4 := le_trans h3 h2
        omega
      rw [M.workTapes_step_eq_of_ne O i hne]
      exact hblank i z hz'

/-- In an initialized run, the query after `t` steps has length at most `t`. In
particular the no-blank fallback branch of `queryString` is unreachable from an initial
configuration.

**Proof sketch.** By induction on `t`, every write performed in the first `t` steps
happened at a head position of absolute value at most `t - 1` (heads start at `0` and
move at most one cell per step, `Turing.workTapePos_apply_le`). Hence cell `t` of the
query tape is still blank at time `t`, so the least-blank search in `queryString`
terminates at an index `≤ t`. -/
theorem queryString_length_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) :
    (queryString (M.runFrom O (M.initCfg x) t)).length ≤ t := by
  have hblank : (M.runFrom O (M.initCfg x) t).workTapes (queryTapeIdx k) ((t : ℕ) : ℤ) =
      none :=
    (runFrom_workTapes_invariant M O x t).2 _ _ (le_abs_self _)
  classical
  simp only [queryString]
  rw [dif_pos ⟨t, hblank⟩]
  refine le_trans (List.length_filterMap_le _ _) ?_
  simpa using Nat.find_min'
    (p := fun n : ℕ =>
      (M.runFrom O (M.initCfg x) t).workTapes (queryTapeIdx k) (n : ℤ) = none)
    ⟨t, hblank⟩ hblank

/-- In an initialized run, every work-tape cell at distance at least `t` from the
origin is still blank after `t` steps. This is the certificate that the no-blank
fallback branch of `queryString` is unreachable from initialization (the length bound
`queryString_length_le` alone does not certify this, since the fallback also returns a
short list).

**Proof sketch.** Simultaneous induction on `t` with the head-position bound
`|workTapePos i| ≤ t`: at `t = 0` all tapes are blank and heads are at `0`; an ordinary
step writes only at the *old* head position (of absolute value `≤ t`, hence `< t + 1`;
`Action.apply` writes before moving) and moves each head by at most one cell
(`Turing.workTapePos_apply_le`); oracle-answer and halted steps change no tape. -/
theorem runFrom_workTapes_blank (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) (i : Fin (k + 1)) (z : ℤ) (hz : (t : ℤ) ≤ |z|) :
    (M.runFrom O (M.initCfg x) t).workTapes i z = none :=
  (runFrom_workTapes_invariant M O x t).2 i z hz

end OracleTM

/-- Extend an action on `k` work tapes to `k + 1` work tapes: the extra (last) tape is
neither written nor moved. -/
def Action.extend (a : Action k Symbol State) : Action (k + 1) Symbol State where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < k then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := a.state

/-- Embed a `k`-tape configuration into a `k + 1`-tape configuration over the extended
state type `State ⊕ Fin 3`: the extra work tape is blank with its head at `0`, and the
state is renamed along `Sum.inl`. -/
def Cfg.embedOracle (cfg : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol (State ⊕ Fin 3) input where
  state := cfg.state.map Sum.inl
  inputPos := cfg.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < k then cfg.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i => if h : (i : ℕ) < k then cfg.workTapePos ⟨i, h⟩ else 0
  output := cfg.output

/-- The embedding preserves the scanned input symbol. -/
lemma Cfg.embedOracle_inputSymbol (cfg : Cfg k Symbol State input) :
    cfg.embedOracle.inputSymbol = cfg.inputSymbol := rfl

/-- The embedding preserves the scanned work symbols on the original tapes. -/
lemma Cfg.embedOracle_workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) :
    cfg.embedOracle.workTapeSymbols i.castSucc = cfg.workTapeSymbols i := by
  simp [Cfg.workTapeSymbols, Cfg.embedOracle]

/-- The embedding preserves haltedness. -/
lemma Cfg.embedOracle_state_eq_none {cfg : Cfg k Symbol State input} :
    cfg.embedOracle.state = none ↔ cfg.state = none := by
  simp [Cfg.embedOracle, Option.map_eq_none_iff]

/-- The embedding preserves the output tape. -/
lemma Cfg.embedOracle_output (cfg : Cfg k Symbol State input) :
    cfg.embedOracle.output = cfg.output := rfl

/-- Applying an extended, state-renamed action to an embedded configuration is the
embedding of applying the original action. -/
lemma Cfg.embedOracle_apply (a : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    ((a.mapState (Sum.inl : State → State ⊕ Fin 3)).extend).apply cfg.embedOracle =
      (a.apply cfg).embedOracle := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_pos hi]
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_neg hi]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_pos hi]
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_neg hi]
      simp
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]

/-- The embedding sends initial configurations to initial configurations. -/
lemma Cfg.embedOracle_init (q₀ : State) (input : List Symbol) :
    (Cfg.init q₀ input : Cfg k Symbol State input).embedOracle =
      Cfg.init (Sum.inl q₀ : State ⊕ Fin 3) input := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Cfg.embedOracle]

namespace OracleTM

/-- Embed a plain machine as an oracle machine that never queries: the state type is
extended by three fresh states serving as `qQuery`, `qYes`, `qNo`, and the transition
function acts as before on original states (never moving into the fresh states, and
ignoring the query tape). The fresh states are unreachable from the initial
configuration. The *transition table* halts immediately from all three fresh states;
note that from `qQuery` itself the query override fires first (one answer step into
`qYes`/`qNo`, whose table entries then halt) — the table's `qQuery` row is dead code. -/
def ofMultiTapeTM (tm : MultiTapeTM k Symbol State) : OracleTM k Symbol (State ⊕ Fin 3) where
  q₀ := .inl tm.q₀
  qQuery := .inr 0
  qYes := .inr 1
  qNo := .inr 2
  tr q inp work :=
    match q with
    | .inl q => ((tm.tr q inp fun i => work i.castSucc).mapState Sum.inl).extend
    | .inr _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- The embedding of a plain machine is well-formed: its three fresh special states are
pairwise distinct by construction. -/
theorem ofMultiTapeTM_wellFormed (tm : MultiTapeTM k Symbol State) :
    (ofMultiTapeTM tm).WellFormed := by
  constructor <;> simp [ofMultiTapeTM]

/-- One step of an embedded plain machine, under any oracle, is the embedding of one
step of the original machine: the embedded state is never `qQuery = Sum.inr 0`, so the
oracle step reduces to applying the extended action, and `Cfg.embedOracle_apply` turns
that into the embedding of the original step. -/
lemma step_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) :
    (ofMultiTapeTM tm).step O cfg.embedOracle = (tm.step cfg).embedOracle := by
  unfold OracleTM.step MultiTapeTM.step
  cases hs : cfg.state with
  | none =>
    have h : cfg.embedOracle.state = none := by simp [Cfg.embedOracle, hs]
    rw [h]
  | some q =>
    have h : cfg.embedOracle.state = some (Sum.inl q) := by simp [Cfg.embedOracle, hs]
    rw [h]
    dsimp only
    have hne : (Sum.inl q : State ⊕ Fin 3) ≠ (ofMultiTapeTM tm).qQuery := by
      simp [ofMultiTapeTM]
    rw [if_neg hne]
    have hw : (fun i => cfg.embedOracle.workTapeSymbols i.castSucc) =
        cfg.workTapeSymbols :=
      funext fun i => Cfg.embedOracle_workTapeSymbols cfg i
    have htr : (ofMultiTapeTM tm).tr (Sum.inl q) cfg.embedOracle.inputSymbol
        cfg.embedOracle.workTapeSymbols =
        ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).mapState Sum.inl).extend := by
      show ((tm.tr q cfg.embedOracle.inputSymbol
        fun i => cfg.embedOracle.workTapeSymbols i.castSucc).mapState Sum.inl).extend = _
      rw [Cfg.embedOracle_inputSymbol, hw]
    rw [htr, Cfg.embedOracle_apply]

/-- **Sanity check for the oracle architecture** (plan §3.1): an embedded plain machine
runs in lockstep with the original under every oracle — `step_ofMultiTapeTM` pointwise,
then induction on `t`. -/
theorem runFrom_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (ofMultiTapeTM tm).runFrom O cfg.embedOracle t = (tm.runFrom cfg t).embedOracle := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : (ofMultiTapeTM tm).runFrom O cfg.embedOracle (t + 1) =
        (ofMultiTapeTM tm).step O ((ofMultiTapeTM tm).runFrom O cfg.embedOracle t) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1, ih, MultiTapeTM.runFrom_succ_eq_step', step_ofMultiTapeTM]

/-- An embedded plain machine has the same input/output behavior and time bounds as the
original, relative to every oracle. In particular its behavior is oracle-independent.

**Proof sketch.** `Cfg.embedOracle` sends the initial configuration of `tm` to the initial
configuration of the embedded machine (both have blank work tapes and heads at `0`); by
`runFrom_ofMultiTapeTM` the runs correspond, and `Cfg.embedOracle` preserves haltedness
and the output tape. -/
theorem computesInTime_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) :
    (ofMultiTapeTM tm).ComputesInTime O input output t ↔
      ((tm.runFrom (tm.initCfg input) t).state = none ∧
        (tm.runFrom (tm.initCfg input) t).output = output) := by
  have hinit : (ofMultiTapeTM tm).initCfg input = (tm.initCfg input).embedOracle := by
    simp only [OracleTM.initCfg, MultiTapeTM.initCfg, ofMultiTapeTM]
    exact (Cfg.embedOracle_init tm.q₀ input).symm
  simp only [OracleTM.ComputesInTime, hinit, runFrom_ofMultiTapeTM,
    Cfg.embedOracle_state_eq_none, Cfg.embedOracle_output]

open Classical in
/-- The converse of `ofMultiTapeTM` for the empty oracle: an oracle machine run with the
empty oracle is eliminated into a plain `k + 1`-tape machine over the *same* state type,
by replacing the query behavior with a stationary transition into `qNo` (the empty
oracle always answers no). (`audits/phase1-findings.md`, finding 8.) -/
noncomputable def plainEmptyOracle (M : OracleTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State where
  q₀ := M.q₀
  tr q inp work :=
    if q = M.qQuery then ⟨0, fun _ => (none, 0), none, some M.qNo⟩
    else M.tr q inp work

/-- One step of the empty-oracle elimination coincides with one step of the oracle
machine on the empty oracle: on a halted configuration both sides are fixed; in state
`qQuery` the empty oracle answers `qNo` and the stationary action's `Action.apply`
changes only the state; elsewhere both sides apply the same transition-table action. -/
lemma step_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) :
    M.plainEmptyOracle.step cfg = M.step (0 : Language Symbol) cfg := by
  unfold MultiTapeTM.step OracleTM.step plainEmptyOracle
  cases hs : cfg.state with
  | none => rfl
  | some q =>
    dsimp only
    by_cases hq : q = M.qQuery
    · rw [if_pos hq, if_pos hq, if_neg (Language.notMem_zero _)]
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Action.apply]
    · rw [if_neg hq, if_neg hq]

/-- **Sanity check, converse direction**: the empty-oracle elimination runs in exact
lockstep with the oracle machine on the empty oracle — same configurations at every
step, from every starting configuration (`step_plainEmptyOracle` pointwise, then
induction on `t`). -/
theorem runFrom_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) :
    -- `0` is the empty language (`Language`'s `Zero` instance)
    M.plainEmptyOracle.runFrom cfg t = M.runFrom (0 : Language Symbol) cfg t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : M.runFrom (0 : Language Symbol) cfg (t + 1) =
        M.step 0 (M.runFrom (0 : Language Symbol) cfg t) :=
      Function.iterate_succ_apply' _ _ _
    rw [MultiTapeTM.runFrom_succ_eq_step', h1, ih, step_plainEmptyOracle]

end OracleTM

end Turing
```

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity
```

## ===== TCSlib/Complexity/ClassP/TimeConstructible.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Finite

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

## Main results

* `Complexity.timeConstructible_id` — the identity function is time constructible,
  restoring [AB09]'s example under the repaired definition.

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

/-- The final emission uses at most `n` symbol-writing steps. -/
private lemma counter_bits_length (n : ℕ) : n.bits.length ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← counterInc_bits]
    have := (counterInc_length n.bits).1
    omega

/-- One carry transition, with the first transition also advancing the input. -/
private def counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- The audit's four-state counter: count = 0, carry = 1, rewind = 2, emit = 3.
[AB09, §1.3 examples], implemented by the phase-1 reaudit's transition table. -/
private def counterTM : FinTM Bool where
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
    counterTM.tm.step (counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (counterTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
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
    counterTM.tm.runFrom (counterCfg x 1 p pre.length (pre ++ bs) [])
        (counterCarry bs + 1) =
      counterCfg x 2 p ((pre.length : ℤ) + counterCarry bs - 1)
        (pre ++ counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, counter_carry_step]
    simp [counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, counter_carry_step]
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
    counterTM.tm.runFrom (counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, counterTM, counterCfg, Cfg.workTapeSymbols,
        counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : counterTM.tm.step (counterCfg x 2 p (j : ℤ) bs []) =
        counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (counterTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [counterTM, show (2 : Fin 4) ≠ 0 from by decide,
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
    counterTM.tm.step (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      counterTM.tm.step (counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (counterTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (counterTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
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
    counterTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * counterCarry bs + 2) =
      counterCfg x 0 ⟨i + 2, by omega⟩ 0 (counterInc bs) [] := by
  have hc : counterTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
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

/-- The counting invariant carries a nonnegative potential of twice the popcount.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions. -/
private lemma counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      counterTM.tm.runFrom (counterTM.tm.initCfg x) t =
        counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_⟩
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp [MultiTapeTM.initCfg, counterCfg, counterTape]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc⟩ := ih (by omega)
    refine ⟨t + 2 * counterCarry i.bits + 2, ?_, ?_⟩
    · have hp := counterInc_potential i.bits
      rw [counterInc_bits] at hp
      omega
    · rw [show t + 2 * counterCarry i.bits + 2 = t + (2 * counterCarry i.bits + 2) by omega,
        MultiTapeTM.runFrom_add, hc, counter_increment x i (by omega), counterInc_bits]

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    counterTM.tm.runFrom (counterCfg x 3 p 0 bs []) i =
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
    change (counterTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [counterTM, show (3 : Fin 4) ≠ 0 from by decide,
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
    let c := counterTM.tm.runFrom (counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((counterTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [counterTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, counterCfg]

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
theorem timeConstructible_id : TimeConstructible id := by
  refine ⟨fun n => le_refl n, 5, by decide, counterTM, fun x => ?_⟩
  obtain ⟨t, ht, hc⟩ := counter_count x x.length (le_refl _)
  have hs : counterTM.tm.step
      (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    have hin : (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, counterCfg]
    unfold MultiTapeTM.step
    change (counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [counterTM, Action.apply, counterCfg]
  have hstart : counterTM.tm.runFrom (counterTM.tm.initCfg x) (t + 1) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  have he := counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  have hbase : counterTM.ComputesInTime x x.length.bits
      ((t + 1) + (x.length.bits.length + 1)) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.1
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.2
  apply hbase.mono
  have hl := counter_bits_length x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

end Complexity
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines

A machine is *oblivious* if its head movements depend only on the input length, not on
the input itself [AB09, Remark 1.7 and Exercise 1.5]. Obliviousness will matter for
the Cook-Levin theorem (Chapter 2), where the tableau of an oblivious computation has
input-independent structure.

## Design

* Configurations are indexed by their input, so head positions of runs on different
  inputs live in different types only for the input head; obliviousness compares
  `Fin`-valued input positions through `ℕ` and work positions (in `ℤ`) directly.
* `Oblivious` constrains *represented* head trajectories only — the input head and
  the work heads. Our model has no output-head position (output is an append-only
  stream), so emission schedules are deliberately unconstrained; [AB09]'s read-write
  output head is covered by this reading only via a bridge, e.g. a machine that emits
  once at a fixed final time, as the decider produced below does.
* `Oblivious` does **not** imply that the halting time is determined by the input
  length: heads freeze on halting, but frozen positions can coincidentally agree — a
  stationary-head machine can halt after one or two steps depending on its first
  input bit while satisfying `Oblivious` (phase-2 audit, finding 1, with an explicit
  counterexample in `audits/phase2-findings.md`). The `TimeConstructible` hypothesis
  below is required by the *construction* (the simulator derives a length-determined
  step budget and pads its schedule to it), not forced by the definition. If a
  downstream use (the Cook-Levin tableau, Ch. 2) needs length-determined halting or a
  simultaneous one-work-tape oblivious normal form (`M.k = 1 ∧ M.Oblivious`), those
  are separate conjuncts for that normal-form theorem.
* We state the quadratic version — Exercise 1.5's *first assertion*, adapted to this
  model; the exercise's final two-tape normal form is **not** included here. The
  `O(T log T)` sharpening (Exercise 1.6) is a stretch goal alongside §1.7, off the
  critical path.

## Main definitions

* `Turing.FinTM.Oblivious` — [AB09, Remark 1.7].

## Main results

* `Complexity.oblivious_of_mem_DTIME` — [AB09, Exercise 1.5]: every language decidable
  in time-constructible time `T` is decided by an oblivious machine in `O((T + 1)²)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, p. 17; Exercise 1.5, p. 34.)
-/

namespace Turing.FinTM

/-- A machine is *oblivious* if, at every step, its head positions on two inputs of
the same length agree: they are a function of the input length and the time only.
[AB09, Remark 1.7] -/
def Oblivious {Γ : Type} (M : FinTM Γ) : Prop :=
  ∀ (x y : List Γ), x.length = y.length → ∀ t : ℕ,
    (((M.tm.runFrom (M.tm.initCfg x) t).inputPos : ℕ) =
      ((M.tm.runFrom (M.tm.initCfg y) t).inputPos : ℕ)) ∧
    (M.tm.runFrom (M.tm.initCfg x) t).workTapePos =
      (M.tm.runFrom (M.tm.initCfg y) t).workTapePos

end Turing.FinTM

namespace Complexity

open Turing

/-- **Oblivious simulation** — the first assertion of [AB09, Exercise 1.5], adapted
to this model: for time-constructible `T`, every language in `DTIME T` is decided by
an *oblivious* machine within `c · (T n + 1)²`. (The exercise's additional two-tape
normal form is not part of this statement.)

**Proof sketch** (corrected per the phase-2 audit, finding 2: the construction must
not invoke `one_work_tape_binary` per simulated step — that composes quadratics into
a quartic — must not run the constructibility witness verbatim, which need not be
oblivious, and must park the real input head). Take a decider for `L` within
`a · T n` and a constructibility witness within `b · (T n + 1)`.

1. Run the witness with every non-blank input symbol *read as `false`* (substituted
   in its transition table): its entire run — trajectories, emissions, halting time —
   then coincides with its run on the all-`false` input of length `n`, hence depends
   only on `n`, and it still computes `⌞T n⌟`; store the budget on a work tape.
2. Copy the real input to a work tape in one fixed scan and rewind (cost
   `O(n + 1)`, absorbed since `n ≤ T n`), then park the real input head for good.
3. Set `B n = (a + 1) · (T n + 1)` macrosteps and prepare a marked layout of size
   `O(B n)` holding the decider's work tapes, the virtual input copy, virtual head
   markers, and a step counter.
4. Each macrostep simulates one step of the decider by a fixed number of full sweeps
   of the layout — tape data affects writes, simulated state, and markers, never the
   sweep path or its duration — idling identically once the simulated machine halts,
   for exactly `B n` macrosteps (counter maintenance within the per-macrostep linear
   allowance; fixed-duration binary block coding throughout, so no appeal to the
   existential `alphabet_reduction` is needed to stay binary and oblivious).
5. Emit the stored answer bit at a fixed final time and halt.

Every head trajectory and the halting time are then functions of `n` and `t` alone,
and the total cost is `O(b · (T n + 1) + (B n)²) = O((T n + 1)²)`. -/
theorem oblivious_of_mem_DTIME {L : Language Bool} {T : ℕ → ℕ}
    (hT : TimeConstructible T) (hL : L ∈ DTIME T) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.Oblivious ∧ M.DecidesInTime L fun n => c * (T n + 1) ^ 2 := by
  sorry

end Complexity
```

## ===== TCSlib/Complexity/ClassP/P.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class P

`P` is the class of languages decidable in polynomial time: the union over `c` of
`DTIME (n^c + 1)`. [AB09, Definition 1.13, with the `+ 1` padding explained below —
every *positive*-degree component of the literal unpadded union is empty in this model,
since `n^c` vanishes at `n = 0` and no machine halts in zero steps; [AB09]'s union
ranges over `c ≥ 1`, so its literal reading is empty, while including degree `0` would
give exactly `DTIME 1` (in Lean `0 ^ 0 = 1`).]

## Design and deviations from [AB09]

* We take the union of `DTIME (fun n => n ^ c + 1)` over all `c : ℕ` where [AB09] writes
  `⋃_{c ≥ 1} DTIME(n^c)`. The `+ 1` repairs the empty-input degeneracy: a machine needs
  at least one step to halt, so for the degrees `d ≥ 1` of [AB09]'s union no language
  whatsoever is decided within `c · 0^d = 0` steps on the empty input, and the literal
  [AB09] definition would (vacuously) exclude even constant-time machines on that input. For `n ≥ 1` the bounds `c · (n^d + 1)` and
  `c' · n^d` sandwich each other, so this is the standard reading of the same class.
  Ranging over `c = 0` too is harmless: `n^0 + 1 = 2` is a constant bound, subsumed by
  larger `c`.

## Main definitions

* `Complexity.P` — [AB09, Definition 1.13].

## Main results

* `Complexity.dtime_poly_subset_P` — each `DTIME (n^c + 1)` is contained in `P`.
* `Complexity.mem_P_iff` — `P` is exactly the class decidable within `C · (n + 1) ^ d`
  for some constants, certifying that the `+ 1` padding has the conventional
  polynomial-time content.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definition 1.13.)
-/

namespace Complexity

open Turing

/-- The class of polynomial-time decidable languages:
`P = ⋃ c, DTIME (n^c + 1)`. [AB09, Definition 1.13] -/
def P : Set (Language Bool) := ⋃ c : ℕ, DTIME fun n => n ^ c + 1

/-- Every fixed-degree polynomial time class is contained in `P`. -/
theorem dtime_poly_subset_P (c : ℕ) : DTIME (fun n => n ^ c + 1) ⊆ P :=
  Set.subset_iUnion (fun c : ℕ => DTIME fun n => n ^ c + 1) c

/-- Membership in `P` from a concrete polynomial bound: if `L` is decidable within any
time bound that is pointwise dominated by a polynomial, then `L ∈ P`. (Pointwise, not
eventual, domination: an eventual-bound variant follows with the *same machine* by
absorbing the finitely many exceptional bounds into the constant, and is deferred.)

**Proof sketch.** Pick `c` and `d` with `T n ≤ c * (n ^ d + 1)` for all `n`. By
`Complexity.DTIME.mono`, `DTIME T ⊆ DTIME (fun n => c * (n ^ d + 1))`; the latter equals
a subclass of `DTIME (fun n => n ^ d + 1)` because the constant `c` is absorbed by the
existential constant in the definition of `DTIME` (the two constants multiply). Conclude
with `Complexity.dtime_poly_subset_P`. -/
theorem mem_P_of_dtime_le {L : Language Bool} {T : ℕ → ℕ}
    (hL : L ∈ DTIME T) (c d : ℕ) (hT : ∀ n, T n ≤ c * (n ^ d + 1)) : L ∈ P := by
  obtain ⟨a, M, hM⟩ := hL
  refine dtime_poly_subset_P d ⟨a * c, M, fun x => (hM x).mono ?_⟩
  calc a * T x.length ≤ a * (c * (x.length ^ d + 1)) :=
        Nat.mul_le_mul (le_refl a) (hT x.length)
    _ = a * c * (x.length ^ d + 1) := by ring

/-- The key pointwise inequality behind the padding normalization:
`(n + 1) ^ d ≤ 2 ^ d · (n ^ d + 1)` for every `n` and `d`. -/
lemma succ_pow_le (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ d * (n ^ d + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _)
  · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ d * n ^ d := Nat.mul_pow 2 n d
      _ ≤ 2 ^ d * (n ^ d + 1) := Nat.mul_le_mul (le_refl _) (Nat.le_succ _)

/-- `P` is exactly the class of languages decidable within `C · (n + 1) ^ d` steps for
some constants `C` and `d`. This certifies that the `+ 1` padding in the definition of
`P` has the conventional polynomial-time content: forward, a witness for the degree-`c`
component gives a bound `a · (n ^ c + 1) ≤ 2a · (n + 1) ^ c`; backward, `succ_pow_le`
turns a `C · (n + 1) ^ d` decider into a `(C · 2 ^ d) · (n ^ d + 1)` decider, landing
in the degree-`d` component. (`audits/phase1-findings.md`, "Polynomial-time
normalization".) -/
theorem mem_P_iff {L : Language Bool} :
    L ∈ P ↔ ∃ (C d : ℕ) (M : FinTM Bool),
      M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨c, hs⟩ := Set.mem_iUnion.mp hL
    obtain ⟨a, M, hM⟩ := hs
    refine ⟨2 * a, c, M, fun x => (hM x).mono ?_⟩
    have h1 : x.length ^ c ≤ (x.length + 1) ^ c :=
      Nat.pow_le_pow_left (Nat.le_succ _) c
    have h2 : 0 < (x.length + 1) ^ c := Nat.pow_pos (Nat.succ_pos _)
    calc a * (x.length ^ c + 1)
        ≤ a * ((x.length + 1) ^ c + (x.length + 1) ^ c) :=
          Nat.mul_le_mul (le_refl a) (Nat.add_le_add h1 h2)
      _ = 2 * a * (x.length + 1) ^ c := by ring
  · rintro ⟨C, d, M, hM⟩
    refine Set.mem_iUnion.mpr ⟨d, C * 2 ^ d, M, fun x => (hM x).mono ?_⟩
    calc C * (x.length + 1) ^ d
        ≤ C * (2 ^ d * (x.length ^ d + 1)) :=
          Nat.mul_le_mul (le_refl C) (succ_pow_le x.length d)
      _ = C * 2 ^ d * (x.length ^ d + 1) := by ring

/-- Constant time is polynomial time.

**Proof sketch.** `Complexity.mem_P_of_dtime_le` with `T = fun _ => 1`, `c = 1`,
`d = 1`, since `1 ≤ 1 * (n ^ 1 + 1)`. -/
theorem dtime_one_subset_P : DTIME (fun _ => 1) ⊆ P := fun _ hL =>
  mem_P_of_dtime_le hL 1 1 fun n => by
    rw [one_mul]
    exact Nat.le_add_left 1 (n ^ 1)

end Complexity
```

## ===== TCSlib/Complexity/ClassP/ModelInvariance.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# "And why it doesn't matter": model invariance of DTIME and P

The payoff of the robustness theorems ([AB09, §1.3.1], formalized in
`TCSlib.Complexity.TuringMachine.Robustness`), stated at the strength the theorems
actually deliver (phase-2 audit, finding 4): **alphabet size** never matters —
`DTIME` is alphabet-invariant, the alphabet-dependent constant being absorbed by
`DTIME`'s own existential — while **the number of work tapes** does not matter *for
`P`*, where the quadratic overhead of tape reduction is harmless. No invariance of a
fixed class `DTIME T` under tape reduction is claimed, and [AB09, §1.6.1] likewise
draws only the polynomial-time conclusion. This is the formal content of the
chapter's title at class level.

## Main definitions

* `Turing.FinTM.DecidesInTimeVia` — a machine over a larger alphabet decides a binary
  language via a symbol embedding.

## Main results

* `Complexity.mem_DTIME_of_decidesInTimeVia` — deciding over any finite alphabet lands
  in binary `DTIME` (constant absorbed). [AB09, Claim 1.5 for languages]
* `Complexity.mem_P_of_decidesInTimeVia_poly` — `P` is alphabet-invariant.
* `Complexity.mem_P_iff_one_work_tape` — `P` is exactly what one-work-tape binary
  machines decide in polynomial time. [AB09, Claims 1.5-1.6 for `P`]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3.1; §1.6.1 "Why the model may not matter".)
-/

namespace Turing.FinTM

/-- The machine `M`, over alphabet `Γ`, decides the binary language `L` via the symbol
embedding `e : Bool ↪ Γ` within time `T`: on every input `x.map e` it halts within
`T |x|` steps with output `[e b]` where `b` is the membership bit of `x` in `L`. -/
def DecidesInTimeVia {Γ : Type} (M : FinTM Γ) (e : Bool ↪ Γ) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime (x.map e)
      [e (MultiTapeTM.indicator (L : Set (List Bool)) x)] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- Deciding a language over *any* finite alphabet puts it in the binary-machine class
`DTIME` (with the alphabet-dependent constant absorbed by `DTIME`'s existential).

**Proof sketch.** `DecidesInTimeVia` is `ComputesFunInTimeVia` for the function
`x ↦ [indicator L x]` (note `[b].map e = [e b]`); apply
`Turing.FinTM.alphabet_reduction` and absorb its constant `c` into `DTIME`'s. -/
theorem mem_DTIME_of_decidesInTimeVia {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} {T : ℕ → ℕ}
    (h : M.DecidesInTimeVia e L T) :
    L ∈ DTIME fun n => T n + 1 := by
  obtain ⟨c, M', -, hM'⟩ := FinTM.alphabet_reduction e M
    (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) T
    (fun x => by simpa using h x)
  exact ⟨c, M', fun x => hM' x⟩

/-- **`P` is alphabet-invariant**: a language decided in polynomial time by a machine
over any finite alphabet is in `P`.

**Proof sketch.** `Complexity.mem_DTIME_of_decidesInTimeVia` gives
`L ∈ DTIME (C · (n + 1) ^ d + 1)`; conclude with `Complexity.mem_P_of_dtime_le`
(pointwise bound `C · (n + 1) ^ d + 1 ≤ (C + 1) · 2 ^ d · (n ^ d + 1)`, using
`(n + 1) ^ d ≤ 2 ^ d (n ^ d + 1)` from the `mem_P_iff` arithmetic). -/
theorem mem_P_of_decidesInTimeVia_poly {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (e : Bool ↪ Γ) {M : FinTM Γ} {L : Language Bool} (C d : ℕ)
    (h : M.DecidesInTimeVia e L fun n => C * (n + 1) ^ d) :
    L ∈ P := by
  have h1 := mem_DTIME_of_decidesInTimeVia e h
  refine mem_P_of_dtime_le h1 ((C + 1) * 2 ^ d) d fun n => ?_
  have h2 : 0 < (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos _)
  calc C * (n + 1) ^ d + 1
      ≤ C * (n + 1) ^ d + (n + 1) ^ d := Nat.add_le_add_left h2 _
    _ = (C + 1) * (n + 1) ^ d := by ring
    _ ≤ (C + 1) * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul (le_refl _) (succ_pow_le n d)
    _ = (C + 1) * 2 ^ d * (n ^ d + 1) := by ring

/-- **`P` is tape-count-invariant**: `P` is exactly the class of languages decided by
binary machines with a *single* work tape in polynomial time. [AB09, Claim 1.6 at the
level of `P`; quadratic slowdown preserves polynomiality]

**Proof sketch.** Backward: a one-work-tape polynomial decider is in particular a
polynomial decider (`Complexity.mem_P_iff`). Forward: from `mem_P_iff` take a decider
within `C · (n + 1) ^ d`; `DecidesInTime` is `ComputesFunInTime` for
`x ↦ [indicator L x]`, so `Turing.FinTM.one_work_tape_binary` yields a one-work-tape
binary machine within `c · (C · (n + 1) ^ d + 1)² ≤ C' · (n + 1) ^ (2d)`, again of the
`mem_P_iff` shape. -/
theorem mem_P_iff_one_work_tape {L : Language Bool} :
    L ∈ P ↔ ∃ (M : FinTM Bool) (C d : ℕ),
      M.k = 1 ∧ M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp hL
    obtain ⟨M', c, hk, hM'⟩ := FinTM.one_work_tape_binary M
      (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x])
      (fun n => C * (n + 1) ^ d) hM
    refine ⟨M', c * (C + 1) ^ 2, d * 2, hk, fun x => (hM' x).mono ?_⟩
    have h2 : 0 < (x.length + 1) ^ d := Nat.pow_pos (Nat.succ_pos _)
    calc c * (C * (x.length + 1) ^ d + 1) ^ 2
        ≤ c * ((C + 1) * (x.length + 1) ^ d) ^ 2 := by
          refine Nat.mul_le_mul (le_refl c) (Nat.pow_le_pow_left ?_ 2)
          calc C * (x.length + 1) ^ d + 1
              ≤ C * (x.length + 1) ^ d + (x.length + 1) ^ d :=
                Nat.add_le_add_left h2 _
            _ = (C + 1) * (x.length + 1) ^ d := by ring
      _ = c * (C + 1) ^ 2 * ((x.length + 1) ^ d) ^ 2 := by ring
      _ = c * (C + 1) ^ 2 * (x.length + 1) ^ (d * 2) := by rw [pow_mul]
  · rintro ⟨M, C, d, -, hM⟩
    exact mem_P_iff.mpr ⟨C, d, M, hM⟩

end Complexity
```

## ===== TCSlib/Complexity/ClassP/Examples.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Example: palindromes are decidable in linear time

The language `PAL` of binary palindromes is decidable in linear time, hence in `P`.
[AB09, Examples 1.1 and 1.4] This is the phase-1 sanity check that the model and class
definitions are *usable*: proving it requires constructing a concrete machine and running
the definitional semantics on it end to end.

## Deviations from [AB09]

* [AB09, Example 1.1] states "within `3n` steps". We state `PAL ∈ DTIME (n + 1)`: the
  `∃ c` in `DTIME` absorbs the leading constant, and the `+ 1` covers the empty input, on
  which every machine needs at least one step to halt (`3 · 0 = 0` is unachievable — the
  book ignores this degenerate case).

## Main definitions

* `Complexity.PAL` — the palindrome language. [AB09, Example 1.1]

## Main results

* `Complexity.PAL_mem_DTIME_linear` — `PAL ∈ DTIME (n + 1)`. [AB09, Example 1.4]
* `Complexity.PAL_mem_P` — `PAL ∈ P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Examples 1.1, 1.4.)
-/

namespace Complexity

open Turing

/-- The language of binary palindromes. [AB09, Example 1.1] -/
def PAL : Language Bool := {x | x.reverse = x}

/-- The audited copy/rewind/test transition table; states are numbered 0, 1, 2.
[AB09, Example 1.1], with the boundary transitions from the phase-1 audit. -/
private def palTM : FinTM Bool where
  k := 1
  State := Fin 3
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
          | none => ⟨.neg, fun _ => (none, .zero), none, some 1⟩
        else if q = 1 then
          match inp with
          | some _ => ⟨.neg, fun _ => (none, .zero), none, some 1⟩
          | none => ⟨.pos, fun _ => (none, .neg), none, some 2⟩
        else
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), some true, none⟩
          | some b =>
            if work 0 = some b then
              ⟨.pos, fun _ => (none, .neg), none, some 2⟩
            else ⟨.zero, fun _ => (none, .zero), some false, none⟩ }

/-- The input word restricted to nonnegative cells below `t`. -/
private def palTape (x : List Bool) (t : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < (t : ℤ) then x[z.toNat]? else none

/-- Canonical live configurations used in the three phase invariants. -/
private def palCfg (x : List Bool) (q : Fin 3) (p : Fin (x.length + 2))
    (w : ℤ) (t : ℕ) : Cfg 1 Bool (Fin 3) x :=
  ⟨some q, p, fun _ => palTape x t, fun _ => w, []⟩

/-- Writing the next input bit extends the copied prefix by one cell. -/
private lemma palTape_write (x : List Bool) (t : ℕ) (ht : t < x.length) :
    Function.update (palTape x t) (t : ℤ) (some x[t]) = palTape x (t + 1) := by
  funext z
  by_cases hz : z = (t : ℤ)
  · subst z
    simp [palTape, ht]
  · rw [Function.update_of_ne hz]
    simp only [palTape]
    by_cases hlt : 0 ≤ z ∧ z < (t : ℤ)
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- A copy transition writes at the old head, then advances both heads. -/
private lemma pal_copy_step (x : List Bool) (t : ℕ) (ht : t < x.length) :
    palTM.tm.step (palCfg x 0 ⟨t + 1, by omega⟩ t t) =
      palCfg x 0 ⟨t + 2, by omega⟩ (t + 1) (t + 1) := by
  have hs : (palCfg x 0 ⟨t + 1, by omega⟩ t t).inputSymbol = some x[t] :=
    inputSymbolInner t (by simp only [palCfg]; omega) ht
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    simp only [palTM, Action.apply, ↓reduceIte]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    simpa [palTM, Action.apply] using palTape_write x t ht
  · funext j
    simp [palTM, Action.apply]
  · simp [palTM, Action.apply]

/-- Copy invariant, including the untouched blank cells outside the prefix.
**Proof sketch.** At time zero the prefix is empty. Each subsequent transition
extends it by the next input bit, using `pal_copy_step`. -/
private lemma pal_copy (x : List Bool) : ∀ t (ht : t ≤ x.length),
    palTM.tm.runFrom (palTM.tm.initCfg x) t =
      palCfg x 0 ⟨t + 1, by omega⟩ t t := by
  intro t
  induction t with
  | zero =>
    intro ht
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp only [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg, Cfg.init, palCfg, palTape]
      rw [if_neg (by omega)]
    · rfl
    · rfl
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact pal_copy_step x t (by omega)

/-- The right blank starts the rewind with the input head at position `n`. -/
private lemma pal_copy_end (x : List Bool) :
    palTM.tm.step (palCfg x 0 ⟨x.length + 1, by omega⟩ x.length x.length) =
      palCfg x 1 ⟨x.length, by omega⟩ x.length x.length := by
  have hs : (palCfg x 0 ⟨x.length + 1, by omega⟩ x.length x.length).inputSymbol =
      none := by simp [Cfg.inputSymbol, palCfg]
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    simp only [palTM, Action.apply, ↓reduceIte]
    rw [moveInputPos_neg_of_ne_left _ (by simp)]
    simp
  · rfl
  · funext j; simp [palTM, Action.apply]
  · rfl

/-- Rewinding does not move or change the copied work tape. -/
private lemma pal_rewind_step (x : List Bool) (i : ℕ) (hi : i < x.length) :
    palTM.tm.step (palCfg x 1 ⟨i + 1, by omega⟩ x.length x.length) =
      palCfg x 1 ⟨i, by omega⟩ x.length x.length := by
  have hs : (palCfg x 1 ⟨i + 1, by omega⟩ x.length x.length).inputSymbol =
      some x[i] := inputSymbolInner i (by simp only [palCfg]; omega) hi
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = i
    rw [moveInputPos_neg_of_ne_left _ (by simp)]
    simp
  · rfl
  · funext j; simp [palTM, Action.apply]
  · rfl

/-- The input head reaches the left blank in exactly its current position's steps.
**Proof sketch.** Induct on the input position; each interior transition decreases
it by one and preserves every other field. -/
private lemma pal_rewind (x : List Bool) : ∀ i (hi : i ≤ x.length),
    palTM.tm.runFrom (palCfg x 1 ⟨i, by omega⟩ x.length x.length) i =
      palCfg x 1 0 x.length x.length := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step, pal_rewind_step x i (by omega)]
    exact ih (by omega)

/-- The left boundary transition aligns the input and reversed work-tape scans,
including work position `-1` on empty input. -/
private lemma pal_test_start (x : List Bool) :
    palTM.tm.step (palCfg x 1 0 x.length x.length) =
      palCfg x 2 1 ((x.length : ℤ) - 1) x.length := by
  have hs : (palCfg x 1 0 x.length x.length).inputSymbol = none := by
    simp [Cfg.inputSymbol, palCfg]
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    change (moveInputPos (0 : Fin (x.length + 2)) .pos).val = (1 : Fin (x.length + 2)).val
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    rfl
  · rfl
  · funext j; simp [palTM, Action.apply, sub_eq_add_neg]
  · rfl

/-- In the comparison phase, the work read is the corresponding bit of `reverse`. -/
private lemma pal_test_read (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length).workTapeSymbols 0 =
      some (x.reverse[i]'(by simpa using hi)) := by
  have hz : (x.length : ℤ) - 1 - i = ((x.length - 1 - i : ℕ) : ℤ) := by omega
  simp only [palCfg, Cfg.workTapeSymbols, palTape, hz, Int.toNat_natCast]
  rw [if_pos (by omega), List.getElem?_eq_getElem (by omega), List.getElem_reverse]

/-- A matched pair advances the opposing comparison heads. -/
private lemma pal_test_step (x : List Bool) (i : ℕ) (hi : i < x.length)
    (heq : x.reverse[i]'(by simpa using hi) = x[i]) :
    palTM.tm.step (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length) =
      palCfg x 2 ⟨i + 2, by omega⟩ ((x.length : ℤ) - 1 - (i + 1)) x.length := by
  have hs : (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length).inputSymbol =
      some x[i] := inputSymbolInner i (by simp only [palCfg]; omega) hi
  have hw := pal_test_read x i hi
  rw [heq] at hw
  unfold MultiTapeTM.step
  change (palTM.tm.tr (2 : Fin 3) _ _).apply _ = _
  rw [hs]
  simp only [palTM, show (2 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, hw]
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 2
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · rfl
  · funext j
    simp only [Action.apply, palCfg, SignType.neg_eq_neg_one, SignType.coe_neg_one]
    omega
  · rfl

/-- All opposing pairs at or after position `i` agree. -/
private def palMatches (x : List Bool) (i : ℕ) : Prop :=
  ∀ j (hj : j < x.length), i ≤ j → x.reverse[j]'(by simpa using hj) = x[j]

/-- After a matching comparison, the remaining condition starts at the next bit. -/
private lemma palMatches_succ (x : List Bool) (i : ℕ) (hi : i < x.length)
    (heq : x.reverse[i]'(by simpa using hi) = x[i]) :
    palMatches x i ↔ palMatches x (i + 1) := by
  constructor
  · intro h j hj hij; exact h j hj (by omega)
  · intro h j hj hij
    by_cases hji : j = i
    · subst j; exact heq
    · exact h j hj (by omega)

open Classical in
/-- The comparison phase decides the remaining pointwise equalities in at most
one step per pair plus the final blank transition.
**Proof sketch.** Induct on the number of pairs left. A matching pair reduces to
the induction hypothesis. A mismatch emits false immediately, and halting absorbs
the unused steps. At zero remaining pairs, the right blank emits true. -/
private lemma pal_test (x : List Bool) : ∀ r i (hi : i ≤ x.length)
    (hr : x.length = i + r),
    let c := palTM.tm.runFrom
      (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length) (r + 1)
    c.state = none ∧ c.output = [if palMatches x i then true else false] := by
  intro r
  induction r with
  | zero =>
    intro i hi hr
    have he : i = x.length := by omega
    subst i
    have hm : palMatches x x.length := by intro j hj hij; omega
    have hs : (palCfg x 2 ⟨x.length + 1, by omega⟩
        ((x.length : ℤ) - 1 - x.length) x.length).inputSymbol = none := by
      simp [Cfg.inputSymbol, palCfg]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((palTM.tm.tr (2 : Fin 3) _ _).apply _).state = none ∧ _
    rw [hs]
    simp [palTM, Action.apply, palCfg, hm]
  | succ r ih =>
    intro i hi hr
    have hi' : i < x.length := by omega
    by_cases heq : x.reverse[i]'(by simpa using hi') = x[i]
    · simp only [MultiTapeTM.runFrom_succ_eq_step,
        pal_test_step x i hi' heq]
      simpa only [palMatches_succ x i hi' heq] using
        ih (i + 1) (by omega) (by omega)
    · have hs : (palCfg x 2 ⟨i + 1, by omega⟩
          ((x.length : ℤ) - 1 - i) x.length).inputSymbol = some x[i] :=
        inputSymbolInner i (by simp only [palCfg]; omega) hi'
      have hw := pal_test_read x i hi'
      have hm : ¬palMatches x i := fun h => heq (h i hi' (le_refl _))
      let c := palTM.tm.step
        (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length)
      have hc : c.state = none ∧ c.output = [false] := by
        dsimp only [c]
        unfold MultiTapeTM.step
        change ((palTM.tm.tr (2 : Fin 3) _ _).apply _).state = none ∧ _
        rw [hs]
        simp only [palTM, show (2 : Fin 3) ≠ 0 from by decide,
          show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, hw]
        rw [if_neg (by simpa only [Option.some.injEq] using heq)]
        exact ⟨rfl, rfl⟩
      change (palTM.tm.runFrom c (r + 1)).state = none ∧
        (palTM.tm.runFrom c (r + 1)).output = [if palMatches x i then true else false]
      rw [MultiTapeTM.runFrom_of_halt _ hc.1]
      simpa only [if_neg hm] using hc

/-- Palindromes are decidable in linear time. [AB09, Examples 1.1 and 1.4]

**Proof sketch.** Adapt the machine of [AB09, Example 1.1] to our model (bidirectional
tapes, no start symbol, blank = `none`): a one-work-tape machine with states
`{copy, rewind, test}`.

1. *Copy* (`n + 1` steps): move the input head and the work head right in unison, copying
   each input symbol to the work tape, until the input head reads blank (one cell past the
   input). The work head now sits one cell right of the copied string.
2. *Rewind* (`n + 1` steps): move the input head left back to the left boundary cell while
   the work head stays put; then step the work head one cell left onto the last symbol.
3. *Test* (`n + 1` steps): move the input head right and the work head left in unison,
   comparing the input symbol against the work symbol. On a mismatch, emit `false` and
   halt. When the input head reads blank again (all positions matched), emit `true` and
   halt.

Each phase takes at most `n + 1` steps, so some constant `c` (e.g. `c = 4`) gives
`c · (n + 1) ≥ 3n + 3` total steps, witnessing the `DTIME (n + 1)` bound. The formal
proof constructs the machine's transition function explicitly and establishes the
three-phase invariants by induction on the step count. -/
theorem PAL_mem_DTIME_linear : PAL ∈ DTIME fun n => n + 1 := by
  classical
  refine ⟨3, palTM, fun x => ?_⟩
  have hstart : palTM.tm.runFrom (palTM.tm.initCfg x)
      (x.length + 1 + x.length + 1) =
      palCfg x 2 1 ((x.length : ℤ) - 1) x.length := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step', pal_copy x x.length (le_refl _),
      pal_copy_end, pal_rewind x x.length (le_refl _), pal_test_start]
  have hm : palMatches x 0 ↔ x ∈ PAL := by
    constructor
    · intro h
      apply List.ext_getElem List.length_reverse
      intro j hj hj'
      exact h j hj' (Nat.zero_le _)
    · intro h j hj _
      change x.reverse = x at h
      simp only [h]
  have htest := pal_test x x.length 0 (Nat.zero_le _) (by omega)
  have ht : 3 * (x.length + 1) = (x.length + 1 + x.length + 1) + (x.length + 1) := by
    omega
  refine ⟨_, ?_, ?_, rfl⟩
  · dsimp only
    rw [ht, MultiTapeTM.runFrom_add, hstart]
    simpa only [Nat.cast_zero, sub_zero] using htest.1
  · dsimp only
    rw [ht, MultiTapeTM.runFrom_add, hstart]
    simpa only [Nat.cast_zero, sub_zero, MultiTapeTM.indicator, hm] using htest.2

/-- Palindromes are decidable in polynomial time. -/
theorem PAL_mem_P : PAL ∈ P :=
  mem_P_of_dtime_le PAL_mem_DTIME_linear 1 1 fun n => by simp [pow_one]

end Complexity
```

## ===== TCSlib/Complexity/TuringMachine/Encoding.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim).
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
* `Turing.exists_effectiveMachineCode` — a concrete effective scheme exists.
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
private def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The aligned parser recovers both components, by induction on the first word. -/
private lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-- Six-state pairing controller: double-stay, double-move, emit-true,
first-left, rewind, and copy. The double-stay state's blank branch emits `false`. -/
private def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
private def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- Fixed two-bit serialization of an optional bit. -/
private def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
private def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- Self-delimiting unary serialization of a state index. -/
private def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- Serialization of an optional successor state (`none` = halt). -/
private def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- Serialization of one transition record. -/
private def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- A concrete effective representation scheme exists.

**Proof sketch.** Take `encode := CodeTM.serialize` — which records the state count,
the initial state, and the table (finding 5) — and let `decode` run the aligned-pair
parser of `pairEncode_injective` on the doubled-bit region to recover `numStates`,
then parse the unary initial state and the `9 · (numStates + 1)` fixed-format records;
any malformation (including trailing non-`true` junk) yields a canonical trivial
machine, making `decode` total. The parser **short-circuits on the first incomplete
record** (equivalently, rejects up front any state count whose minimum table length
exceeds the remaining input), so a short malformed string declaring a huge binary
state count is rejected in time polynomial in the string, not by enumerating its
missing records (round-2 audit, finding 8). A complete serialization determines its own length,
and the parser ignores a trailing all-`true` suffix, giving `decode_encode_pad`. The
`canonizer` is a machine implementing exactly this parse followed by re-serialization
(on valid codes, the identity up to padding removal; on invalid ones, the trivial
machine's serialization), with a polynomial `canonizerTime`; its construction uses
the composition combinators of `TCSlib.Complexity.TuringMachine.Composition`. -/
theorem exists_effectiveMachineCode : Nonempty EffectiveMachineCode := by
  sorry

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation uses `Turing.MultiTapeTM.relabelState` (the shared state-renaming
module, `TCSlib.Complexity.TuringMachine.StateRenaming`), eliminates `hk` after
destructuring the bundle, and concludes with
`Turing.MultiTapeTM.relabelState_runFrom_init`. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  classical
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨Fintype.card Q - 1, tm.relabelState e⟩, ?_⟩
  intro x output t
  simp only [CodeTM.toFinTM, FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace,
    MultiTapeTM.relabelState_runFrom_init, Cfg.mapState, Option.map_eq_none_iff]
  constructor
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Universal.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The universal Turing machine

[AB09, §1.4.1 and Theorem 1.9, relaxed form]: there is a single machine `U` that,
given a code and an input, simulates the machine the code denotes — `U(x, α) =
M_α(x)` — with the simulation overhead depending only on the code, not on the input.

## Design and deviations from [AB09] (all shaped by the phase-3 audit)

* Statements are relative to an `Turing.EffectiveMachineCode`: the purely algebraic
  scheme admits noncomputable-meaning pathologies against which no universal machine
  exists (audit finding 1, Argument A).
* **Input layout is `pairEncode α x` — code first, input second** — deviating from
  [AB09]'s `⟨x, α⟩`: with the input first, the startup cost of reaching the code
  grows with `|x|` and the stated bounds are false (audit finding 2, Argument B).
  With the code first, startup (parsing and canonizing `α`) costs a constant
  depending only on `α`, absorbed into `C`, and the simulated input head walks the
  verbatim `x` region on demand.
* `universal` is the **all-string evaluator** [AB09's `U(x, α) = M_α(x)`, p. 20]:
  it covers every `α` through `c.decode` (padded and fallback representations
  included), and it carries **both directions** — the forward time bound, and the
  converse that any *completed* output of `U` (output on halting; intermediate
  emissions of a non-halting run are unconstrained) is a completed output of the
  simulated machine, so divergence is preserved (round-1 finding 3; round-2
  Argument C).
* The constant `C` depends on the **representation** `α`, a documented weakening of
  [AB09]'s machine-dependent constant that is *necessary* at this generality: an
  effective scheme can reserve arbitrarily long identical-prefix representations of
  two fixed machines, defeating any constant that factors through `c.decode α`
  (round-2 audit, finding 6 and Argument E). Recovering the book's dependence would
  require further representation assumptions.
* **The core bound is linear**, `C · (t + 1)`: coded machines are already in
  one-work-tape binary normal form, so `U` pays a constant per simulated step.
  [AB09]'s relaxed quadratic bound reappears in `universal_quadratic`, where an
  *arbitrary* binary machine is first normal-formed ([AB09, Claims 1.5-1.6]); that
  corollary is stated — and labeled — at the level of **total function computation**
  (audit finding 4), the machine-level partial statement being `universal` itself.
  The `O(T log T)` sharpening ([AB09, §1.7]) is the phase-5 stretch goal.
* `timed_universal` outputs `true :: output` on success and `[false]` on timeout, a
  concrete rendering of [AB09]'s "special failure symbol" (§1.4.1); its budget is
  quadratic (binary clock maintenance). The deadline convention: halting is checked
  after every simulated transition *including the `t`-th*, so a machine first
  halting exactly at the deadline is a success; at budget `0` no initialized machine
  has halted, and the timeout branch applies (audit finding 6).

## Main results

* `Turing.universal` — the all-string evaluator [AB09, Theorem 1.9 core].
* `Turing.universal_quadratic` — the relaxed quadratic form for total functions of
  arbitrary binary machines [AB09, Theorem 1.9 as proved in §1.4.1].
* `Turing.timed_universal` — the time-bounded universal machine [AB09, §1.4.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21; Figure 1.6.)
-/

namespace Turing

/-- **The universal machine as an all-string evaluator** [AB09, Theorem 1.9]: for any
effective scheme there is a single machine `U` such that for every string `α` there
is a constant `C` (depending on `α`, absorbing its decoding) with, for every input
`x`: whenever the machine `α` denotes halts on `x` within `t` steps with `output`,
`U` on `pairEncode α x` halts with the same output within `C · (t + 1)` steps —
and conversely every *completed* output of `U` on `pairEncode α x` (its output on
halting) is a completed output of the denoted machine on `x`, so divergence is
preserved.

**Proof sketch** (after [AB09, Figure 1.6], adapted to the code-first layout).
Startup: `U` runs the scheme's `canonizer` on the doubled-bit `α`-region (via the
composition combinators), leaving the fixed serialization of `M := c.decode α` — the
state count, initial state, and table — on a *table* work tape, and writes the
initial state on a *state* tape; cost `O(canonizerTime |α| + |α| + 1)`, a constant
for fixed `α`, absorbed into `C`. `U`'s input head then parks at the start of the
verbatim `x` region, and a *work* tape mirrors `M`'s work tape. **The simulated
input's left boundary must be emulated explicitly** (round-2 audit, finding 3): the
cell physically left of the `x` region is the pairing delimiter's `true`, not a
blank, so `U` keeps a marker on a spare work tape whose head tracks the virtual
input position — at virtual position zero it supplies a blank read and suppresses
further outward moves (mirroring `moveInputPos`'s clamp), and for empty `x` the
virtual head starts at the right boundary blank adjacent to that marked left
boundary. Each simulated step: read the mirrored work symbol and the input symbol
under the simulated head (the input head moves one cell per simulated move — `x` is
verbatim, no doubling — with the boundary marker moved in lockstep), scan the table
for the record matching (state, input read, work read) — at most the table length,
constant in `t` — and apply it: update the state tape, write/move on the mirrored
tape, emit `M`'s emission verbatim. Forward bound: `C · (t + 1)`. Converse:
`U` emits only what the simulation emits and halts only when the simulation halts,
so any completed output of `U` is an output of `M` on `x`. -/
theorem universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      (∀ output : List Bool,
        (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (c.decode α).toFinTM.ComputesInTime x output t) := by
  sorry

/-- **The relaxed quadratic form, for total functions** [AB09, Theorem 1.9 as proved
in §1.4.1 — labeled per audit finding 4: this is the total-function corollary; the
machine-level, partial-computation statement is `Turing.universal`]: every binary
machine computing a total function `f` within `T` has a code `α` such that the
*same* universal machine computes `f x` from `pairEncode α x` within
`C · (T |x| + 1)²`.

**Proof sketch.** Normal-form the machine with `Turing.FinTM.one_work_tape_binary`
(quadratic, [AB09, Claims 1.5-1.6]), relabel its states with `Turing.exists_codeTM`,
take `α := c.encode` of that coded machine (so `c.decode α` is that machine, by
`MachineCode.decode_encode`), and apply the forward direction of `Turing.universal`;
the constants compose as `C_U · (c₁ · (T n + 1)² + 1) ≤ C · (T n + 1)²`. -/
theorem universal_quadratic (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (M₀ : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ),
      M₀.ComputesFunInTime f T →
      ∃ (α : List Bool) (C : ℕ), ∀ x : List Bool,
        U.ComputesInTime (pairEncode α x) (f x) (C * (T x.length + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := universal c
  refine ⟨U, ?_⟩
  intro M₀ f T hM
  obtain ⟨M₁, c₁, hk, h₁⟩ := FinTM.one_work_tape_binary M₀ f T hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := c.encode N
  obtain ⟨C_U, hCU⟩ := hU α
  refine ⟨α, C_U * (c₁ + 1), fun x => ?_⟩
  have hcoded : (c.decode α).toFinTM.ComputesInTime x (f x)
      (c₁ * (T x.length + 1) ^ 2) := by
    rw [show c.decode α = N from c.toMachineCode.decode_encode N]
    exact (hN x (f x) _).2 (h₁ x)
  apply ((hCU x).1 (f x) _ hcoded).mono
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc C_U * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ C_U * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl C_U) (Nat.add_le_add_left hpow _)
    _ = C_U * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

/-- **The time-bounded universal machine** [AB09, §1.4.1, "Universal TM with time
bound"]: a single machine that, given `⟨⟨⌞t⌟, α⟩, x⟩` (clock and code first, input
last), simulates the machine `α` denotes on `x` for at most `t` steps, reporting
success (`true :: output`) or timeout (`[false]`).

**Proof sketch.** Extend the simulation of `Turing.universal` with a binary
countdown clock on a further work tape, initialized from `⌞t⌟ = Nat.bits t` (parsed
from the doubled-bit region; cost `O(t + 1)`, within budget). Each simulated step
costs an additional `O((Nat.bits t).length + 1)` for the decrement, whence the
quadratic budget; `M`'s emissions are buffered on a work tape rather than emitted
(their total length is at most `t`, by `Turing.MultiTapeTM.output_length_le`).
Halting is checked after each simulated transition, **including the `t`-th**: if the
simulated machine has halted by the time the clock expires — deadline included —
`U` emits `true` and flushes the buffer; otherwise it emits `false`. At `t = 0` no
initialized machine has halted (`Turing.FinTM.not_computesInTime_zero`), and the
timeout branch applies (audit finding 6). The two cases below are exhaustive:
either some output witnesses halting within `t`, or every output fails to. -/
theorem timed_universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output) (C * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false] (C * (t + 1) ^ 2)) := by
  sorry

end Turing
```

## ===== TCSlib/Complexity/Uncomputability/Computable.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Vector
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computable functions

A total string function is *computable* if some finite binary machine computes it,
with no time constraint [AB09, §1.4, p. 20]. This is the notion the uncomputability
results of [AB09, §1.5] refute for `UC` and `HALT`. The machine-level predicate is
`Turing.FinTM.Computes` (in `TCSlib.Complexity.TuringMachine.Finite`); this file
provides the machine-independent class and the bridge back to the time-bounded
notion `Turing.FinTM.ComputesFunInTime`.

## Design and deviations from [AB09]

* Computability is defined for **total** functions `List Bool → List Bool` only, as
  in [AB09]; partial computation is handled at the machine level, by the halting
  relation of a machine (see the two clauses of `Turing.universal`). No time bound,
  and no property of any bound, is part of the definition.
* The name clash with Mathlib's `_root_.Computable` (the `Nat.Partrec`-based notion)
  is deliberate and harmless: ours lives in the `Complexity` namespace, and the
  planned `MathlibBridge` module will relate the two.

## Main definitions

* `Complexity.Computable` — some finite binary machine computes `f`.
  [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.Computes.exists_computesFunInTime` — a machine computing `f` with no
  stated time bound admits *some* time bound, by finiteness of the inputs of each
  length. This is the bridge the diagonalization uses to reach the total-function
  normal-form theorems, which are stated with bounds.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, p. 20; §1.5.)
-/

namespace Turing.FinTM

/-- A machine computing `f` with no stated time bound admits some time bound: there
are only finitely many inputs of each length, so the maximum halting time over them
is a bound. (Anticipated by the phase-3 audit, round 2, Argument F: "take the finite
maximum of those times at each input length".)

**Proof sketch.** By choice pick, for each input `x`, a halting time `t x`
witnessing `h x`. The inputs of length `n` form a finite type (`List.Vector Symbol
n`, whose `Fintype` instance transports from `Fintype (Fin n → Symbol)`), so
`T n := Finset.univ.sup` of `t` over it is well defined, and
`Turing.FinTM.ComputesInTime.mono` lifts each witness to the bound `T x.length`.
No monotonicity, positivity, or constructibility of `T` is claimed — none is needed
downstream. -/
theorem Computes.exists_computesFunInTime {Symbol : Type} [Fintype Symbol]
    {M : FinTM Symbol} {f : List Symbol → List Symbol} (h : M.Computes f) :
    ∃ T : ℕ → ℕ, M.ComputesFunInTime f T := by
  classical
  choose t ht using h
  let T : ℕ → ℕ := fun n =>
    (Finset.univ : Finset (List.Vector Symbol n)).sup fun x => t x.val
  refine ⟨T, fun x => (ht x).mono ?_⟩
  exact Finset.le_sup (f := fun y : List.Vector Symbol x.length => t y.val)
    (Finset.mem_univ (α := List.Vector Symbol x.length) ⟨x, rfl⟩)

end Turing.FinTM

namespace Complexity

open Turing

/-- A total string function is *computable* if some finite binary machine computes
it — halts on every input with the value on the output tape — with no time
constraint. [AB09, §1.4, p. 20] -/
def Computable (f : List Bool → List Bool) : Prop :=
  ∃ M : FinTM Bool, M.Computes f

end Complexity
```

## ===== TCSlib/Complexity/Uncomputability/Diagonalization.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.Uncomputability.Computable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uncomputability by diagonalization

[AB09, §1.5, Theorem 1.10]: the diagonal function `UC` is not computable. This is
the theorem the whole encoding layer (`TCSlib.Complexity.TuringMachine.Encoding`)
has been building toward: it needs machines-as-strings and nothing else — not even
the universal machine.

## Design and deviations from [AB09]

* `UC` is defined relative to an **arbitrary** representation scheme
  `Turing.MachineCode`, and Theorem 1.10 is stated at that generality: the
  diagonalization *chooses* one fixed code — `c.encode` of the hypothetical
  decider's normal form — inside a mathematical contradiction, and no machine ever
  computes `encode` or `decode` (phase-3 audit, round 2, Argument F). Effectivity
  (`Turing.EffectiveMachineCode`) is needed only where a machine must *run* codes:
  the universal machine, and the `HALT` reduction of
  `TCSlib.Complexity.Uncomputability.Halting`.
* Output convention: [AB09] writes `M_α(α) = 1`; in this model that is the completed
  singleton output `[true]`. Accordingly `UC c α = true` covers divergence *and*
  every completed output other than `[true]` — exactly the complement of the book's
  acceptance condition (Argument F's reading).
* [AB09] fixes one standing representation once and for all; here the scheme is a
  parameter, so `UC` is a family of functions and Theorem 1.10 a family of
  theorems, each an instance of the book's.

## Main definitions

* `Complexity.UC` — the diagonal function. [AB09, §1.5]

## Main results

* `Complexity.UC_not_computable` — [AB09, Theorem 1.10].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.5, Theorem 1.10, pp. 21-22.)
-/

namespace Complexity

open Turing

open Classical in
/-- The diagonal function `UC` of a representation scheme [AB09, §1.5]: `UC c α` is
`false` iff the machine `α` denotes *accepts its own representation* — that is,
`(c.decode α).toFinTM` halts on input `α` with completed output `[true]`. On
divergence, and on any completed output other than `[true]`, the value is `true`.
([AB09] writes: `UC(α) = 0` if `M_α(α) = 1`, and `UC(α) = 1` otherwise.) -/
noncomputable def UC (c : MachineCode) (α : List Bool) : Bool :=
  if ∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t then false else true

/-- Unfolding lemma: `UC c α = false` iff the denoted machine accepts its own
representation. -/
theorem UC_eq_false_iff (c : MachineCode) (α : List Bool) :
    UC c α = false ↔ ∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t := by
  unfold UC
  split <;> simp_all

/-- Unfolding lemma: `UC c α = true` iff the denoted machine does not accept its own
representation — it diverges on it, or completes with an output other than
`[true]`. -/
theorem UC_eq_true_iff (c : MachineCode) (α : List Bool) :
    UC c α = true ↔ ¬∃ t, (c.decode α).toFinTM.ComputesInTime α [true] t := by
  unfold UC
  split <;> simp_all

/-- **`UC` is not computable** [AB09, Theorem 1.10] — for every representation
scheme, effective or not.

**Proof sketch** (diagonalization, [AB09, proof of Theorem 1.10]; blueprint:
phase-3 audit round 2, Argument F). Suppose some machine computes
`fun α => [UC c α]`. `Turing.FinTM.Computes.exists_computesFunInTime` supplies a
time bound; `Turing.FinTM.one_work_tape_binary` normal-forms the machine into a
one-work-tape binary machine computing the same function; `Turing.exists_codeTM`
relabels that into a coded machine `N` with the same input-by-input `ComputesInTime`
relation. Set `α₀ := c.encode N`, so `c.decode α₀ = N` by
`Turing.MachineCode.decode_encode`, and `N.toFinTM` halts on `α₀` with completed
output `[UC c α₀]`. If `UC c α₀ = false`, then `Complexity.UC_eq_false_iff` (read
through `decode_encode`) says `N.toFinTM` also halts on `α₀` with `[true]`, and
`Turing.FinTM.ComputesInTime.output_unique` forces `[false] = [true]` — absurd. If
`UC c α₀ = true`, then `N.toFinTM` halts on `α₀` with `[true]`, so
`UC_eq_false_iff` gives `UC c α₀ = false` — absurd. No step computes `encode` or
`decode`: the code `α₀` is chosen inside the contradiction. -/
theorem UC_not_computable (c : MachineCode) : ¬Computable fun α => [UC c α] := by
  rintro ⟨M, hM⟩
  obtain ⟨T, hT⟩ := hM.exists_computesFunInTime
  obtain ⟨M', C, hk, hM'⟩ := FinTM.one_work_tape_binary M _ T hT
  obtain ⟨N, hN⟩ := exists_codeTM M' hk
  let α := c.encode N
  have hrun : (c.decode α).toFinTM.ComputesInTime α [UC c α]
      (C * (T α.length + 1) ^ 2) := by
    rw [show c.decode α = N from c.decode_encode N]
    exact (hN α [UC c α] _).2 (hM' α)
  cases hu : UC c α with
  | false =>
    obtain ⟨t, ht⟩ := (UC_eq_false_iff c α).1 hu
    have hcontra := hrun.output_unique ht
    simp only [hu, List.cons.injEq, Bool.false_eq_true, false_and] at hcontra
  | true =>
    have hfalse : UC c α = false :=
      (UC_eq_false_iff c α).2 ⟨_, by simpa only [hu] using hrun⟩
    simp only [hu, Bool.true_eq_false] at hfalse

end Complexity
```

## ===== TCSlib/Complexity/Uncomputability/Halting.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.Uncomputability.Diagonalization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uncomputability of the halting problem

[AB09, §1.5.1, Theorem 1.11]: `HALT` is not computable — proved, as in the book, by
*reduction*: if `HALT` were computable then so would be `UC`, contradicting
[AB09, Theorem 1.10]. This is the chapter's (and history's) first reduction, and the
first consumer of the universal machine `Turing.universal` and of the guarded
composition combinators of `TCSlib.Complexity.TuringMachine.Composition`.

## Design and deviations from [AB09]

* `HALT` takes the pair `⟨α, x⟩` in exactly the universal machine's input format
  `Turing.pairEncode α x` (code first — the phase-3 layout), so the reduction can
  feed pairs it builds straight into the evaluator without re-encoding.
* [AB09] leaves the pairing convention implicit and does not say what `HALT` does on
  strings that are not pairs (the pairing is not surjective); we **totalize by
  `false`** off the image of `pairEncode` — "does not halt".
  `Turing.pairEncode_injective` makes the value on genuine pairs unambiguous
  (`Complexity.HALT_pairEncode_eq_true_iff`), and the reduction only ever evaluates
  `HALT` on genuine pairs, so the off-image convention is immaterial to
  Theorem 1.11. It is *not* immaterial in general — `HALT c [] = false` is a
  convention-dependent equality — so a downstream client evaluating `HALT` on
  arbitrary strings must keep the convention or prove its inputs are genuine pairs
  (phase-4 audit, finding 6).
* "Halts" is rendered as *has a completed output*: `∃ output t, ComputesInTime`.
  This is equivalent to reaching the halting state (every halted configuration has
  some finite output).
* Theorem 1.11 is stated relative to an **effective** scheme
  (`Turing.EffectiveMachineCode`): the reduction runs the universal evaluator,
  which exists only for effective schemes — in contrast to Theorem 1.10, which
  holds for every `Turing.MachineCode`. The reduction itself is a separate lemma
  (`Complexity.UC_computable_of_HALT_computable`), the book's "if `HALT` were
  computable, `UC` would be".

## Main definitions

* `Complexity.HALT` — the halting function. [AB09, §1.5.1]

## Main results

* `Complexity.UC_computable_of_HALT_computable` — the reduction
  [AB09, proof of Theorem 1.11].
* `Complexity.HALT_not_computable` — [AB09, Theorem 1.11].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.5.1, Theorem 1.11, pp. 22-23.)
-/

namespace Complexity

open Turing

open Classical in
/-- The halting function [AB09, §1.5.1]: `HALT c s = true` iff `s` is a pair
`Turing.pairEncode α x` — the universal machine's input format, code first — such
that the machine `α` denotes halts on `x`, i.e. completes *some* output in *some*
number of steps. Strings not of that form (the pairing is not surjective) map to
`false`. -/
noncomputable def HALT (c : MachineCode) (s : List Bool) : Bool :=
  if ∃ α x : List Bool, s = pairEncode α x ∧
      ∃ (output : List Bool) (t : ℕ), (c.decode α).toFinTM.ComputesInTime x output t
  then true else false

/-- Unfolding lemma for `HALT`. -/
theorem HALT_eq_true_iff (c : MachineCode) (s : List Bool) :
    HALT c s = true ↔
      ∃ α x : List Bool, s = pairEncode α x ∧
        ∃ (output : List Bool) (t : ℕ),
          (c.decode α).toFinTM.ComputesInTime x output t := by
  unfold HALT
  split <;> simp_all

/-- On a genuine pair, `HALT` says exactly whether the denoted machine halts:
injectivity of the pairing (`Turing.pairEncode_injective`) identifies the
components. -/
theorem HALT_pairEncode_eq_true_iff (c : MachineCode) (α x : List Bool) :
    HALT c (pairEncode α x) = true ↔
      ∃ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t := by
  rw [HALT_eq_true_iff]
  constructor
  · rintro ⟨α', x', heq, hhalt⟩
    have hp : (α, x) = (α', x') := pairEncode_injective heq
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact hhalt
  · intro hhalt
    exact ⟨α, x, rfl, hhalt⟩

/-- **The reduction** [AB09, proof of Theorem 1.11]: if `HALT` were computable,
`UC` would be. Stated for an effective scheme, whose universal evaluator the
reduction runs.

**Proof sketch** (blueprint: phase-3 audit round 2, Argument F; every ingredient
below is a stated result of this development — the fill is assembly, not new
mathematics). Let `D` compute `fun s => [HALT c.toMachineCode s]`, let `U` be the
evaluator of `Turing.universal c`, and write
`p α := HALT c.toMachineCode (pairEncode α α)`.

1. `Turing.computesFunInTime_pairEncode_diag` gives a machine for the diagonal
   pairing `α ↦ pairEncode α α`; `Turing.FinTM.exists_comp_partial` composes it
   with `D`, and determinism (`Turing.FinTM.ComputesInTime.output_unique`)
   collapses the intermediate string, yielding a machine `D'` computing
   `fun α => [p α]`.
2. `Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]` gives the
   postprocessor `w ↦ if w = [true] then [false] else [true]`; two applications of
   `exists_comp_partial` chain the diagonal pairing, `U`, and the postprocessor
   into a machine `Mt` such that `Mt` halts on `α` with `w'` iff `U` halts on
   `pairEncode α α` with some `w` and `w'` is the postprocessed `w`.
3. `Turing.FinTM.computesFunInTime_const [true]` gives `Mf`, computing the constant
   `[true]`; `Turing.FinTM.exists_cond D' Mt Mf p` assembles the branch machine
   `R`.
4. Correctness of `R` at each `α`: if `p α = false`, then by
   `Complexity.HALT_pairEncode_eq_true_iff` the denoted machine never halts on `α`,
   so `Complexity.UC_eq_true_iff` gives `UC = true`, and the selected branch `Mf`
   outputs exactly `[true]`. If `p α = true`, the same lemma yields a completed
   output `w₀` within some `t₀`; the **forward clause** of `Turing.universal` makes
   `U` halt on `pairEncode α α` with `w₀` (the converse clause is not needed — the
   positive `HALT` answer already guarantees halting), so `Mt` halts on `α` with
   the postprocessed value, and `output_unique` identifies the condition
   `w₀ = [true]` with `Complexity.UC_eq_false_iff`'s, making that value
   `[UC c.toMachineCode α]` in both subcases. Hence `R` computes
   `fun α => [UC c.toMachineCode α]`. -/
theorem UC_computable_of_HALT_computable (c : EffectiveMachineCode)
    (h : Computable fun s => [HALT c.toMachineCode s]) :
    Computable fun α => [UC c.toMachineCode α] := by
  classical
  obtain ⟨D, hD⟩ := h
  obtain ⟨U, hU⟩ := universal c
  obtain ⟨P, _, hP⟩ := computesFunInTime_pairEncode_diag
  obtain ⟨Q, _, hQ⟩ := FinTM.computesFunInTime_ifEq [true] [false] [true]
  obtain ⟨Mf, _, hMf⟩ := FinTM.computesFunInTime_const [true]
  let p : List Bool → Bool := fun α => HALT c.toMachineCode (pairEncode α α)
  let r : List Bool → List Bool := fun w => if w = [true] then [false] else [true]
  -- First decide whether the decoded machine halts on its own code.
  obtain ⟨D', hD'⟩ := FinTM.exists_comp_partial P D
  have hDp : D'.Computes fun α => [p α] := by
    intro α
    exact (hD' α [p α]).2 ⟨pairEncode α α, hP.computes α, hD _⟩
  -- The positive branch evaluates the self-pair and postprocesses its output.
  obtain ⟨PU, hPU⟩ := FinTM.exists_comp_partial P U
  obtain ⟨Mt, hMt⟩ := FinTM.exists_comp_partial PU Q
  have hMt' (α z : List Bool) :
      (∃ t, Mt.ComputesInTime α z t) ↔
        ∃ w, (∃ t, U.ComputesInTime (pairEncode α α) w t) ∧ z = r w := by
    simp only [r, hMt, hPU, hP.computes.exists_computesInTime_iff,
      hQ.computes.exists_computesInTime_iff, exists_eq_left]
  obtain ⟨R, hR⟩ := FinTM.exists_cond D' Mt Mf p hDp
  refine ⟨R, fun α => (hR α _).2 ?_⟩
  cases hp : p α with
  | false =>
    have huc : UC c.toMachineCode α = true := (UC_eq_true_iff _ _).2 (by
      rintro ⟨t, ht⟩
      have htrue : p α = true :=
        (HALT_pairEncode_eq_true_iff _ _ _).2 ⟨[true], t, ht⟩
      simp only [hp, Bool.false_eq_true] at htrue)
    simpa only [hp, Bool.cond_false, huc] using hMf.computes α
  | true =>
    obtain ⟨w, t, hw⟩ := (HALT_pairEncode_eq_true_iff _ _ _).1 hp
    obtain ⟨C, hC⟩ := hU α
    have huw : ∃ s, U.ComputesInTime (pairEncode α α) w s :=
      ⟨C * (t + 1), (hC α).1 w t hw⟩
    have hr : r w = [UC c.toMachineCode α] := by
      by_cases hwtrue : w = [true]
      · have huc : UC c.toMachineCode α = false :=
          (UC_eq_false_iff _ _).2 ⟨t, hwtrue ▸ hw⟩
        simp only [r, if_pos hwtrue, huc]
      · have huc : UC c.toMachineCode α = true := (UC_eq_true_iff _ _).2 (by
          rintro ⟨t', ht'⟩
          exact hwtrue (hw.output_unique ht'))
        simp only [r, if_neg hwtrue, huc]
    have hMtuc := (hMt' α [UC c.toMachineCode α]).2 ⟨w, huw, hr.symm⟩
    simpa only [hp, Bool.cond_true] using hMtuc

/-- **`HALT` is not computable** [AB09, Theorem 1.11]: immediate from the reduction
`Complexity.UC_computable_of_HALT_computable` and the diagonal theorem
`Complexity.UC_not_computable`. -/
theorem HALT_not_computable (c : EffectiveMachineCode) :
    ¬Computable fun s => [HALT c.toMachineCode s] :=
  fun h => UC_not_computable c.toMachineCode (UC_computable_of_HALT_computable c h)

end Complexity
```

## ===== TCSlib/Complexity/TuringMachine.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Configuration
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Oracle
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
import TCSlib.Complexity.TuringMachine.Robustness.Bidirectional
import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Universal

/-!
# Complexity — Turing machines

The multi-tape Turing machine model underlying the Arora-Barak formalization
(see `AroraBarakChapter1Plan.md`): a machine-free configuration/action layer, the
deterministic machine with time and space semantics, the bundled finite layer over which
all complexity classes are stated, and oracle machines as a wrapper over the same
configurations.

The core model files are vendored from cslib
(https://github.com/leanprover/cslib, commit a3747758, 2026-09-14); see the file headers
for the local modifications.

## Contents

* `Configuration` — configurations `Cfg`, actions `Action` and their application; the
  space measure. Nothing here mentions a machine (vendored).
* `Deterministic` — `MultiTapeTM`, the step/run semantics, time and space bounds
  (vendored).
* `StateRenaming` — transport of actions, configurations, and machines along maps
  of the state type; shared by the oracle embedding and the code normal form.
* `Finite` — the bundled `FinTM` layer carrying `Fintype`/`DecidableEq` state instances;
  all headline definitions are stated over it.
* `Oracle` — oracle machines `OracleTM` [AB09, §3.4]: same configurations, oracle-dependent
  step; the embedding of plain machines and its oracle-independence sanity theorems.
* `Simulation` — generic machine-construction gadgets: emission chains, control
  actions, disjoint tape-block embeddings with lockstep run lemmas, the input-head
  rewind, and the two-machine branch union.
* `Composition` — identity/constant machines and closure of time-bounded computability
  under composition; also the formal home of the append-only-output convention
  argument.
* `Robustness/AlphabetReduction` — binary alphabet suffices [AB09, Claim 1.5].
* `Robustness/SingleTape` — one work tape suffices, quadratically [AB09, Claim 1.6].
* `Robustness/Bidirectional` — unidirectional tape use suffices [AB09, Claim 1.8].
* `Robustness/Oblivious` — oblivious machines and the quadratic oblivious simulation
  [AB09, Remark 1.7, Exercise 1.5] (imports the `ClassP` definitions it needs).
* `Encoding` — machines as strings [AB09, §1.4]: the code normal form `CodeTM`, the
  fixed canonical serialization, the representation-scheme laws `MachineCode`, and
  the effective scheme `EffectiveMachineCode` that the universal machine requires.
* `Universal` — the universal machine [AB09, Theorem 1.9]: the all-string evaluator
  with linear overhead and divergence preservation, the relaxed quadratic
  total-function form, and the time-bounded variant (code-first input layout).
-/
```

## ===== TCSlib/Complexity/ClassP.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassP.ModelInvariance
import TCSlib.Complexity.ClassP.Examples

/-!
# Complexity — DTIME and the class P

Deterministic time-bounded computation and the class `P`, following [AB09, §1.3, §1.6]
(see `AroraBarakChapter1Plan.md` for the chapter-level plan).

## Contents

* `DTIME` — deciding a language within a time bound; the classes `DTIME T`
  [AB09, Definition 1.12].
* `TimeConstructible` — time-constructible functions [AB09, §1.3].
* `P` — the class `P` [AB09, Definition 1.13] and basic membership lemmas.
* `ModelInvariance` — `DTIME`/`P` do not depend on alphabet size or tape count
  [AB09, §1.3.1, §1.6.1]: the class-level corollaries of the robustness theorems.
* `Examples` — the palindrome language is in `DTIME (n + 1)` and in `P`
  [AB09, Examples 1.1, 1.4].
-/
```

## ===== TCSlib/Complexity/Uncomputability.lean =====

```lean
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Uncomputability.Computable
import TCSlib.Complexity.Uncomputability.Diagonalization
import TCSlib.Complexity.Uncomputability.Halting

/-!
# Complexity — Uncomputability

[AB09, §1.5]: not every function is computable. The diagonal function `UC` is
uncomputable by a direct diagonalization over machines-as-strings, and the halting
function `HALT` is uncomputable by reduction — the book's first reduction, run on
the universal machine (see `AroraBarakChapter1Plan.md`).

## Contents

* `Computable` — computable string functions, with no time bound
  [AB09, §1.4, p. 20].
* `Diagonalization` — the diagonal function `UC` and its uncomputability
  [AB09, Theorem 1.10], stated for every representation scheme.
* `Halting` — the halting function `HALT`, the reduction to `UC`, and
  [AB09, Theorem 1.11], stated for effective schemes.
-/
```

---

# ATTACHMENT INVENTORY (36 files)

- audits/epoch2-agent-reports/batchA.md
- audits/epoch2-agent-reports/batchB.md
- audits/epoch2-agent-reports/batchC.md
- AroraBarakChapter1Plan.md
- policy.md
- audits/epoch1-findings.md
- audits/epoch1-resolutions.md
- audits/phase2-findings.md
- audits/phase2-reaudit-findings.md
- briefs/epoch2-batchA.md
- briefs/epoch2-batchB.md
- briefs/epoch2-batchC.md
- TCSlib/Complexity/TuringMachine/Simulation.lean
- TCSlib/Complexity/TuringMachine/Composition.lean
- TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean
- TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean
- TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean
- TCSlib/Complexity/TuringMachine/StateRenaming.lean
- TCSlib/Complexity/TuringMachine/Finite.lean
- TCSlib/Complexity/TuringMachine/Configuration.lean
- TCSlib/Complexity/TuringMachine/Deterministic.lean
- TCSlib/Complexity/TuringMachine/Oracle.lean
- TCSlib/Complexity/ClassP/DTIME.lean
- TCSlib/Complexity/ClassP/TimeConstructible.lean
- TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean
- TCSlib/Complexity/ClassP/P.lean
- TCSlib/Complexity/ClassP/ModelInvariance.lean
- TCSlib/Complexity/ClassP/Examples.lean
- TCSlib/Complexity/TuringMachine/Encoding.lean
- TCSlib/Complexity/TuringMachine/Universal.lean
- TCSlib/Complexity/Uncomputability/Computable.lean
- TCSlib/Complexity/Uncomputability/Diagonalization.lean
- TCSlib/Complexity/Uncomputability/Halting.lean
- TCSlib/Complexity/TuringMachine.lean
- TCSlib/Complexity/ClassP.lean
- TCSlib/Complexity/Uncomputability.lean
