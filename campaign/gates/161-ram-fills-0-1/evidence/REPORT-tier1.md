# Word-size fill report

Date: 2026-11-17 (America/Los_Angeles).
Base: `81557aad15a7123fa7e006f53310b5f702e0b0cd`, fetched from
`complexity/ram-simulation` in `https://github.com/Shilun-Allan-Li/tcslib`.
Local proof branch: `codex/fill-ram-wordsize`; its HEAD stayed at the base and was never rebased
or pushed. Delivery is only to `exchange/pass-shelat-ch5-8`,
`arora-barak-ch3-4/inbox/fill-ram-wordsize/fill-ram-wordsize.zip`.

## Outcome

All three targets are proved, with no remaining admission or frontier:

| Target | Result |
|---|---|
| `WordRAM.WordSizeComputable.mono` | Same machine and times; weaken both bounds. |
| `WordRAM.wordSizeComputable_logSpace` | Linear time, logarithmic visited work space, all coefficients and input lengths including zero. |
| `WordRAM.wordSizeComputable_of_spaceConstructible` | Space a constant times `S`, with a uniform length-dependent time bound. |

The four original public declaration headers are **byte-identical** to the base, including
whitespace. No public declaration was added or removed. `WordSizeComputable` itself is unchanged.
There are twelve new private declarations and three additional imports. The source has 930 lines.
The module docstring and the two construction targets' proof sketches now describe the completed
proofs without campaign labels or stale line pointers. No new simp attribute, axiom, admission,
or build product is delivered.

## Construction

The multiplier is a finite-control arithmetic leaf with no work tapes. For a positive constant,
one input step emits the low bit of the constant times the input bit plus its bounded carry;
a final bounded phase emits the carry in canonical binary. At coefficient zero the published
constant machine emits the empty word. On canonical input `n.bits`, this takes at most the
input width plus a constant number of steps and zero work space.

`scale_computes` captures an existing numerical machine's output with the published returning
embedding, rewinds the captured word, and hosts the multiplier on that word. Two published
seams perform the handoffs. Its deadline is the source deadline plus twice the answer width
and a constant; its space is a constant times the source space, answer width, and one.

For the logarithm, the published native input-length counter writes `x.length.bits`. A hosted
conditional length counter emits that word's bit length, returning one for an empty word.
This is exactly `logSpace x.length`, including length zero. Both phases have linear time in
their respective input widths; the second therefore costs only `O(log n)`. Their explicit
head and tape-bank bounds give logarithmic visited space. The shared scaling construction then
multiplies this answer by the requested constant. No polynomial-in-logarithm estimate is needed:
the arithmetic leaf has linear rather than polynomial width cost.

For a space-constructible `S`, the existing ConfigCount normal-form theorem supplies a uniform
configuration-count deadline and the same space bound at every time. The shared scaler consumes
that witness. `length_bits_le_self`, `logSpace ≤ S`, and `logSpace_eq` give width at most `S`
and `1 ≤ S`, absorbing all extra space. Its source deadline plus scaling overhead is `TW`.
This uses the existing uniform configuration bound rather than re-proving a finite-input maximum.

## Private declarations and reuse searches

Searches covered the import closure, the Build catalog and registry, and the repository for
existing multiplication, space composition, state-map composition, and start-state space facts.
The search terms included `multiply`, `multiplication`, `mulTM`, `mulBits`, `computes.*mul`,
`bufferedComp.*spaceUsed`, `spaceUsed.*with_q`, `mapState_comp`, and `mapState_mapState`.

| New private declaration | Role and facts cited after the search |
|---|---|
| `mulCarry` | Carry in `Fin (c + 1)` for the positive multiplier; elementary division bound. |
| `mulMachine` | The arithmetic leaf; no catalog leaf computes this canonical binary constant product. |
| `parity_bits` | Remainder/quotient form of the published `Complexity.LogProg.bits_two_mul_add`, using `Nat.mod_two_eq_zero_or_one`. |
| `mul_flush` | Carry-phase run, using `parity_bits` and published step/run/action equations. |
| `mul_scan` | Canonical suffix run, using `mul_flush`, `parity_bits`, `inputSymbolInner`, and list append readers. |
| `constant_multiplier` | Joins the positive leaf and the published zero constant machine. |
| `cfg_map_comp` | Composes control renamings through the five `Cfg.mapState` field equations and `Option.map_map`; no public composition lemma was found. |
| `space_with_start` | Derives invariance under a start-state update from `runFrom_with_q₀` and the published visited-space readers; no existing space lemma for this update was found. |
| `bank_sum_bound` | Sharp bank sum: selected contributions are counted once, plus a uniform unused-tape bound. Cites `Finset.sum_sdiff`, `sum_image`, and cardinality bounds. This avoids copying the coarse private relocation lemma in Constructible. |
| `scale_computes` | Instantiates the existing capture, rewind, hosting, embedding, and seam combinators with the arithmetic leaf. |
| `normalized_counter` | Cites `ifEqTM_computes`, `constTM_computes`, `computesFunInTime_lengthBits_spaceUsed`, and `computesFunInTime_cond`. |
| `logarithmic_computation` | Cites `exists_inputLengthTM`, `normalized_counter`, published embedding/hosting/seam contracts, and the shared bank ledger. |

The only new transition table is the arithmetic leaf. No new loop, interpreter, input-device,
or other control host is introduced. The logarithmic bank layout uses the existing
`Fin.revPerm`, `Fin.castLEEmb`, and `Fin.natAddEmb`; it does not copy Constructible's private
layout function or logarithm machine. No copied proved material or new public API is requested.

A buffered-composition route was investigated and discarded after a scratch opacity probe found
that its generated first-configuration head equation did not directly transport across the
opaque tape-count definition. The delivered construction uses the published embedding and seam
contracts instead. This is not a remaining blocker.

## Imports and definition readers

Additional imports:

- `SpaceComplexity.ConfigCount`: existing space monotonicity and the space-to-uniform-time
  normal-form theorem. **Explicitly approved by the user in this session** after the brief's
  Build-only import restriction was identified; the question and answer are in
  `evidence/import-approval.txt`.
- `TuringMachine.Build.InterpreterStartup`: `embedSilentRetTM_firstReturn` and
  `embedSilentCfg_initCfg`, avoiding re-derivation of existing published capture facts.
- `TuringMachine.Build.Rewind`: the framed `rewindTM_run_ofCfg` contract.

Every reached other-file definition is accessed through these published interfaces:

| Definitions | Published readers used |
|---|---|
| `Cfg.init` | `init_state`, `init_inputPos`, `init_workTapes`, `init_workTapePos`, `init_output`. |
| `Action.apply` | `apply_state`, `apply_inputPos`, `apply_output`. |
| `Cfg.inputSymbol`, `Cfg.workTapeSymbols` | `inputSymbolInner`, `Cfg.inputSymbol_of_end`; work symbols are passed to transitions without unfolding. |
| `MultiTapeTM.step`, `runFrom`, `initCfg` | `step_of_some`, `runFrom_one`, `runFrom_add`, `runFrom_with_q₀`, `initCfg_eq`, `initCfg_with_q₀`. |
| `MultiTapeTM.spaceUsed`, `spaceUsedByTape`, `visitedByTapeHead` | `spaceUsed_eq_sum`, `spaceUsedByTape_eq_card`, `mem_visitedByTapeHead_iff`, `spaceUsed_mono`, `spaceUsed_le_of_abs_le`. |
| `Cfg.mapState` | Its five field equations. |
| `FinTM.ComputesInTime`, `ComputesFunInTime`, `ComputesInSpace` | `computesInTime_iff`, `computesFunInTime_iff`; the space predicate is consumed by `ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le`. |
| `FinTM.constTM`, `ifEqTM`, conditional machine | `constTM_computes`, `constTM_spaceUsed`, `ifEqTM_computes`, `computesFunInTime_cond`; no transition or tape-count reduction. |
| `FinTM.bufferTape` | `bufferTape_eq_none_of_not_mem` and the embedding/hosting buffer contracts. |
| `embedSilentRetTM`, `embedSilentTM` | `embedSilentRetTM_firstReturn`, returning visited-set equality, selected/frame visited-space equations, capture-tape space bound. |
| `embedSilentCfg` | `embedSilentCfg_initCfg`, capture and unselected-tape equations, output equation. |
| `embedEmitTM`, `embedEmitCfg` | `embedEmitTM_runFrom`, selected/frame visited-space equations; configuration reconstruction and selected/unselected/state/input/output equations. |
| `vhostEmitTM`, `vhostCfg`, `FinTM.VirtualTag` | `vhostEmitTM_runFrom`, `vhostEmitTM_spaceUsed_le`, the five configuration equations, `VirtualTag_iff`. |
| `rewindTM`, `seamCompTM` | `rewindTM_run_ofCfg`; `seamCompTM_run_ofCfg`, `firstReturn_ofCfg`, `spaceUsed_le_add_ofCfg`. |
| `Complexity.SpaceConstructible`, `logSpace` | `spaceConstructible_iff`, `logSpace_eq`, `logSpace_le_succ`. |
| `FinTM.configBound` | Appears only as the opaque deadline supplied by the normal-form theorem; its definition is not read. |

The final seal makes all 31 listed external definitions irreducible, removes the applicable
simp-definition attributes, and re-elaborates the entire delivered source. For every sealed
definition, separate delta and equation controls succeed unsealed and fail sealed; the sealed
control also confirms the irreducibility and inactive simp status. All controls pass.

## Verification

All checks used the pinned Lean 4.25.0 through the repository's `leanelab.sh`/`leanelab-o.sh`
wrappers, `nice -n 10`, `-j4`, with this job's own scratch olean tree. No `lake build` ran.
The import closure was bootstrapped from base sources: 36 initial modules, 12 added-import
prerequisites, and 12 downstream prerequisites/modules, for 60 distinct modules. The owned
file was recompiled after finalization. Two original short bootstrap log names collided;
those two modules were rechecked under unique full-module log names.

| Final check | Exit | Result |
|---|---:|---|
| Owned `WordSize.lean` | 0 | Zero errors, zero admission warnings. |
| Entire source with 31 external definitions sealed | 0 | Zero errors, zero admission warnings. |
| `#print axioms` for all three targets | 0 | Each lists only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. |
| Unsealed and sealed delta/equation controls | 0, 0 | All 31 controls behave as required. |
| `RAMSimulation/Simulation` | 0 | Zero errors; its 2 unchanged admissions remain. |
| `RAMSimulation/Classes` | 0 | Zero errors; its 9 unchanged admissions remain. |
| `TCSlib/Complexity/RAMSimulation.lean` | 0 | Zero errors, zero admission warnings. |
| Raw public-header comparison and declaration audit | 0 | Four public declarations unchanged; only the three authorized proof bodies changed. |
| Patch check, application to the base file, and byte comparison | 0, 0 | Reconstructed file is byte-identical to the checked delivery. |
| `git diff --check` | 0 | Clean. |
| Package pin check; cache integrity and Mathlib-root probe | 0 | All present packages match; 7,544 package oleans, none empty; probe passes. |

The exact axiom prints and final exit codes are in `evidence/logs/final-axioms.log` and
`final-check-results.json`. Full check output includes start/end timestamps and peak memory.
The maximum measured Lean RSS was 2,267,725,824 bytes (2.112 GiB), in Primitives.

Source diff (Lean paths only, against the fixed base):

```text
 TCSlib/Complexity/RAMSimulation/WordSize.lean | 900 +++++++++++++++++++++++++-
 1 file changed, 866 insertions(+), 34 deletions(-)
```

## Environment and deviations

- Native macOS/APFS host, 12 logical CPUs and 19,327,352,832 bytes of physical memory.
  Linux cgroup and `/proc` metrics do not exist here; preflight records `vm_stat` and
  `memory_pressure -Q` instead (66% system-wide memory free). Both scratch and checkout
  had 129,946,279,936 free bytes on disk-backed APFS. Resource floors passed.
- The preinstalled pinned system toolchain was used normally; no runtime shim was needed.
  The permitted populated-package symlink points to the existing main checkout's
  `.lake/packages`. Every present package URL and revision matches the manifest; absent
  documentation packages are listed as ABSENT. No package, object tree, or toolchain was
  copied, moved, merged, or downloaded. TCSlib oleans were built afresh in this job's scratch.
- No waits for Lean capacity were needed. One premature scratch assembly probe was launched
  while InterpreterStartup was still compiling, briefly making two checks from this job
  (still below the machine-wide limit of three). It exited in 0.712 seconds on the missing
  prerequisite. That result was discarded and not treated as a code finding; the probe was
  rerun after bootstrap completion. All final checks were strictly serial. The premature
  launch violated the brief's one-own-process and prerequisite-order rules; it did not
  overwrite an output, and the work continued under the environment addendum's deviation rule.
- Managed checkout creation on case-insensitive APFS immediately showed 30 unrelated
  blueprint paths modified because each has a tracked case-colliding alias. This was observed
  before proof edits and verified in `checkout-case-collisions.log`. None was edited, staged,
  or delivered. The only changed Lean file is the owned file, and the exchange delivery
  contains only the zip at the requested inbox path.
- The additional ConfigCount import is the explicitly approved scope exception recorded above.
  No other scope exception or incomplete work remains.

## Payload

`REPORT.md`, the complete owned file at its repository path, `WordSize.patch` against the
fixed base, `SHA256SUMS`, and evidence containing logs, the base file, the final seal/control
and axiom probes as `.lean.txt`, the import approval, and the check runner. No compiled object,
cache tree, executable, or checkpoint archive is included. No checkpoint zip was created.
