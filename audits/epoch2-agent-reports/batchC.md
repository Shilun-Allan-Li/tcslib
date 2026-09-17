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
