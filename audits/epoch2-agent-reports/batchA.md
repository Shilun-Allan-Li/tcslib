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
