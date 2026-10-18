# U2-S startup fill — partial delivery

**Phase reached: phase 1 complete; phase 2 partial. This is not a 1/1 fill.**
`Turing.exists_selfStartupTMK` remains open, with its original `sorry` unchanged.
All 15 new private declarations are proved. The delivery adds a cleaned canonizer,
its length-based computation bound, cleanup at its first halt, and reusable first-halt,
returning-capture, silence, space, and tape-placement facts. It does not establish the
normalized return layout required to finish phase 2, redistribution/rewind in phase 3,
or the complete startup assembly in phase 4.

## Checklist

- [x] Phase reached stated above; pinned base and successful ancestor check recorded below.
- [x] First edit was exactly the authorized Clean import. Only regions (a), (b), and (d)
  changed; region (c), the target body, remains unchanged.
- [x] Every new declaration and its role are listed below. No new leaf or host.
  The target docstring contains the flagged **Fill appendix (U2-S)** paragraph.
- [x] Proved phase times and space bounds, and the remaining full-target `T`/`B` work,
  are distinguished below.
- [x] Promotion candidates and the escalation status are recorded below.
- [x] Rule 10 external citations and the extended import probe are recorded.
  Rule 11 grep results and reviewed spelling collisions are recorded.
- [x] Both v3 screens are included, their totals are quoted, and new pairs are accounted for.
- [x] File/declaration counts, final sweep tail, axiom prints, lint result, and regional
  freeze verification are included below and in the evidence logs.

## Inputs, base, and branch

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Initial checkout: `complexity/arora-barak-ch3-4`, observed tip
  `87318cd857b665af66953243df0214c57891d311`.
- Before creating the fill branch,
  `git merge-base --is-ancestor 94b986d4db7167ab2a8b20d38d4385f11e60be0e HEAD`
  returned **0** on that campaign checkout.
- Base: **`94b986d4db7167ab2a8b20d38d4385f11e60be0e`**.
- Branch: **`fill/u2s-startup`**, created at exactly that base.
- Delivery commit: `259a349d52203807da2d292d81e2c3a56a807dd5`.
- No rebase, merge, cherry-pick, push, or PR was performed.
- Uploaded brief SHA-256:
  `6e579c35d89c5cedacadb44ee4c94fcc029ac763c35cdf51f215fc0aa923552e`.
- Uploaded environment addendum SHA-256:
  `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928`.
- The repository brief matched the attachment byte for byte after replacing its
  `@ANCESTOR@` placeholders with the named base. No other difference was accepted.

The first edit inserted exactly
`import TCSlib.Complexity.SpaceComplexity.Machines.Clean` after the four existing imports.
The exact first-edit diff is quoted in the evidence appendix below. The final regional check removes this
import, the new private home, and the flagged appendix and recovers the original file
byte for byte. No existing statement, proof body, attribution, or other tracked file changed.
Unrelated untracked campaign audit files present after checkout were left untouched and
are not in this archive.

## Retained declarations

All names below are private in namespace `Turing` and use the required `ss_` prefix.

| Declaration | Role |
| --- | --- |
| `ss_cleanCanonizer` | Bundle the public `cleanTM`, restarting it at `.init F.tm.q₀`; `2 * F.k` work tapes. |
| `ss_cleanCanonizer_run` | Relate the restarted bundle's initial run to the public cleaning entry using the restart equations. |
| `ss_cleanCanonizer_halts` | Transfer a completed computation through `cleanTM_run`, preserving output and blanking all work tapes and heads. |
| `ss_lengthBound` | Bound an arbitrary string-dependent natural number by a finite maximum over strings of each length. |
| `ss_cleanCanonizer_computes` | Establish `ComputesFunInTime` after cleaning and retain blank tapes/zero heads at that length bound. |
| `ss_bufferedHalt_iff` | Read the buffered second configuration's halted state through its public state equation. |
| `ss_prefix_first_halt` | Transfer a first halt through the fixed prefix phase, uniformly over every suffix. |
| `ss_cleanCanonizer_first_halt` | Retain canonical output and cleaned scratch at the first halt, using the public first-halt theorem. |
| `ss_captureInitial` | Identify the silent embedding of a fresh source with the blank host initial configuration. |
| `ss_captureTM` | Restart the public returning silent embedding at the source's initial state; no new transition host. |
| `ss_capture_run` | Exact returned embedding of the source run, first return, and silence through the return time. |
| `ss_capturedPrefix_run` | Compose the preceding contracts to obtain a suffix-uniform first return and space bound for the captured cleaned prefix. The final configuration still names the prefix run. |
| `ss_sourceSlot` | Embed the prefix's work tapes after the first `k + 2` protected tapes. |
| `ss_captureTape` | Select the last work tape, beyond the embedded prefix block. |
| `ss_capture_indices` | Prove the capture tape is off the source range and all first `k + 2` tapes are off both blocks. |

No leaf was added, so no “why no catalog row serves it” justification is needed.
No catalog contract was re-proved. No clean-machine stage, prefix parsing phase,
or returning-embedding transition table was reimplemented.

The helpers quantify over arbitrary tape counts and suffixes. In particular, they do not
assume `k > 0`, a nonempty suffix, or a positive canonizer tape count. This observation
concerns these partial contracts; it is not a claim that the full target's boundary cases
have been completed.

## Phase times and space

For a fixed canonizer `F`, function `f`, and computation hypothesis:

1. `ss_cleanCanonizer_halts` obtains a time `u(α)` from the public cleanup contract.
   Its auxiliary space bound is the finite supremum of the original run's visited-set
   cardinalities over `Fin F.k`.
2. `ss_lengthBound` forms a maximum over `Fin n → Bool` using `List.ofFn`.
   `ss_cleanCanonizer_computes` uses it to obtain a bound `τ'(n)` for every input
   of length `n`. Absorbing halting freezes the completed output and cleaned fields
   from `u(α)` to `τ'(|α|)`. No computability assumption on this bound is introduced.
3. `ss_cleanCanonizer_first_halt` selects the first cleaned halt `t(α)` on input `α`.
   Its configuration has output `f α`, blank work tapes, and zero work heads.
4. The captured prefix first returns at
   **`N(α) = 3 * α.length + 4 + t(α)`**. The existential choice of `t` precedes
   `∀ w`; the time therefore does not depend on the suffix. The capture is silent
   for every `u ≤ N(α)` and does not reach its return anchor for `u < N(α)`.
5. On an `n`-tape capture host, the proved bound is
   **`Bprefix(α) = n * (N(α) + 1)`**, by `MultiTapeTM.spaceUsed_le_mul_succ`.
   With `m` prefix work tapes the supplied index layout has `n = (m + 1) + (k + 2)`.

These are bounds for the prefix/capture phase, **not** witnesses for the full startup
target. The remaining target time must add the code-dependent redistribution, clearing,
rewind, and seam times to `N(α)`. After those phases are proved, the full space bound can
be `(K + (k + 2)) * (T(α) + 1)`. No full-target `T`, `B`, machine, or fresh exit witness
is claimed by this delivery.

## Open work and escalation status

**Owned open declaration: `Turing.exists_selfStartupTMK`.**

**Proof sketch.** Specialize the generic cleaned-canonizer helpers to `E.canonizer`,
`fun α => serializeK (E.machine α)`, and `E.canonizer_computes`. Normalize the
captured prefix's return using `prefixCanon_run` and the published buffered/embedding
field equations: the capture tape must hold the serialization at its one-past head,
the code buffer must hold `bufferTape α` at the cleaned run's virtual head minus one,
and the remaining selected scratch must be blank. Establish the protected frame through
`ss_sourceSlot`, `ss_captureTape`, `ss_capture_indices`, and the public embedding fields.
Read `serializeK_eq`, `pairEncode_eq`, and `unaryFin_eq`; use the named catalog
`_run_ofCfg` contracts and only justified finite leaves to split and place the unary state
and table. Clear capture and buffer, restore all work heads to zero, and prove a
code-only rewind time to native input position 1. Compose using `phaseHostTM` or the
allowed R2 seams with a fresh exit. Sum all phase times, retain silence and first exit,
and derive the full space bound from the final time.

The exact normalized phase-2 configuration was attempted but its dependent tape/state
transport proof was not closed. That candidate was discarded; no unproved helper or
extra admission is included. Phases 3 and 4 have not been implemented. This is an explicit
continuation-budget partial under ground rule 9, not a claim that the target or any cited
contract is false.

**Ground-rule escalations: none.** No missing public lemma or unprovable stated contract
is asserted. No rule was relaxed to finish a proof.

The two other open declarations in the owned file remain frozen:

- `Turing.exists_selfUniversalK` — **Proof sketch:** its original docstring describes
  composing startup with the forwarding step-block loop and deriving the ledgers and
  converse; this delivery does not work on that proof.
- `Turing.universalK` — **Proof sketch:** its original docstring describes the code-first
  input-device composition and simulation; this delivery does not work on that proof.

All other base admissions are outside this batch. The 35-entry base list is quoted
below; the final comparison is by module and declaration name, not line number.

## Promotion candidates — notes only

- The cleaned bundle and its run, halt, length-bound, computation, and first-halt contracts.
  These do not depend on `EffectiveCodeK` or on a particular serialization.
- `ss_prefix_first_halt`, as a possible companion to the public prefix contracts.
- The fresh-start adapter and run/silence contract for the returning silent embedding.
- The small buffered-state predicate fact, if another consumer needs it.

No leaf or reusable redistribution lemma was completed. The tape-index definitions are
local placement bookkeeping. No promotion or other-file edit was performed.

## Public APIs, no unfolding, and MIG-1

The complete external citation inventory below lists all 110 explicit declaration and
structural-interface names used by the retained helpers. Tactic implementation internals and generated instance
dependencies are not treated as source-level citations.

The import probe is the provided 100-check probe over the final source overlay, extended
with 68 additional checks from that inventory: **168 checks, exit 0, no errors**. Its only
warnings are the three unchanged admissions in the overlay. The brief's introductory
“0 warnings” phrase does not describe a probe containing the admitted source overlay;
the final required criterion is 0 errors. The exact additional checks and axiom-print commands are quoted below.
The probes ran through `scripts/lean_check_tree.sh` and required fresh output oleans.

The retained home also passes a scratch check with these 17 relevant upstream definitions
made locally irreducible: exit 0, empty diagnostics.

```text
MultiTapeTM.initCfg MultiTapeTM.runFrom Cfg.init Cfg.mapState
embedSilentCfg embedSilentRetTM Complexity.LogProg.cleanTM FinTM.ComputesInTime
FinTM.ComputesFunInTime prefixCanonTM universalPrefixTM FinTM.bufferedCompTM
FinTM.bufferedSecondCfg FinTM.bufferTape pairEncode MultiTapeTM.spaceUsed
MultiTapeTM.visitedByTapeHead
```

The final source contains no such attributes. Its explicit proof reductions concern
only its own definitions; upstream machinery is read through public equations and
contracts. The implicit `Cfg.Halted` conversion used by `exists_first_halt` is the
reducible-abbreviation case explicitly described in the pinned
`audits/evidence/brief-api/r3/gate-review-r2.md`, section 5.

The diff grep finds none of the six forbidden R3 canonical rows. A fixed-word grep
against 5,046 foreign-private spellings finds only spelling collisions: local type
variable `S` (also the prose label `U2-S`) and the public qualified
`Turing.Cfg.mapState_state`. The latter resolves in the public import probe.
Actual references to another file's private declarations: **none**.
The raw grep commands, matches, and disposition are quoted below.

## Duplication

Both declaration-keyed v3 screens ran one at a time under `nice -n 10`, over the exact
10-file population in `audits/evidence/u2s-fill/screen-population.txt`.
The before output is byte-identical to the supplied base output.

Before:

```text
declarations screened: 655; copy pairs (target reproduces >= half of source): 514; reproduced text: 151,065 chars
```

After:

```text
declarations screened: 668; copy pairs (target reproduces >= half of source): 514; reproduced text: 151,065 chars
```

New cross-file pairs involving the owned file: **none**. New in-file pairs: **none**.
The complete pair listing is unchanged from the before-screen.

**new copies: none.** Newly copied proved material: 0 lines, 0% of the 601-line file.
The two pre-existing in-file pairs between `EffectiveMachineCode.toK` and
`EffectiveMachineCode2.toK` remain frozen. Screen similarity is reported separately from
the copied-material ledger; no upstream proof was transcribed into the new home.
The complete outputs are `evidence/screen-before.txt` and `evidence/screen-after.txt`.
An initial after-screen found a 78/156-character match against
`Catalog.lean::f2_loop_live_prefix` in the halt-freezing calculation. That calculation
was refactored to expose the remaining-duration witness and apply the public absorbing-run
contract directly. The final screen reported above is the rerun after that change; no screen rule
or population was changed.

## Verification

- **Bootstrap:** the exact prescribed sequential loop over all 92 modules completed
  with exit 0, on the base plus the authorized first import. The full diagnostics are
  `evidence/logs/bootstrap.log`; the recorded bootstrap process exit was 0.
- **Final owned file:** exit 0; exactly three `sorry` warnings, for U2-S, U2-U, and U2-E;
  no other warning, as recorded in its segment of `evidence/logs/final-sweep.log`.
- **Consumers:** `SelfUniversal` and the `TuringMachine` facade passed with fresh oleans
  in the same ordered final sweep.
- **Final sweep:** all 92 modules passed sequentially in the prescribed dependency order, exit 0, 0 errors, and fresh oleans; see `evidence/logs/final-sweep.log`.
- **Sorry set:** exactly the base set of 35 declarations in 15 modules, compared by name; no additions and no removals.
- **Axioms:** all 15 new privates use only subsets of
  `[propext, Classical.choice, Quot.sound]`. In particular, none has `sorryAx`.
  The target prints `[propext, sorryAx, Classical.choice, Quot.sound]` because its body
  is still directly admitted. No completed target or proved-modulo claim is made.
  The scratch-copy axiom output is `evidence/logs/axioms.log`.
- **Style:** `style_lint: 0 FAIL, 67 WARN over 79 files`, unchanged from the base.
  No new line exceeds 100 characters. `git diff --check` passed.
- **Size:** 601 lines, compared with the base's 279; 12 explicit public declarations
  (unchanged), 15 new private declarations (4 definitions, 11 theorems).
  Counts exclude generated projections, constructors, instances, and equation lemmas.
- **Freeze:** byte-for-byte reconstruction of the base outside the owned regions passed.
  The result is quoted below. There are no removed declarations.

Earlier disk-backed final-check attempts did not complete: the filesystem filled at
module 13 (`ClassNP/PolyTime`), and a retry ended with Lean status 135 and no fresh olean.
Scratch probes also failed while their cached imports were unavailable. None of these
attempts counts as a pass. The extracted toolchain download archive and obsolete
task-owned snapshots were removed to free reproducible temporary storage.

The successful final sweep was restarted from module 1 in a memory-backed output tree,
with no pre-existing TCSlib oleans. It checked all 92 modules sequentially in the exact
provided order. The log is the complete successful run, not a splice of partial runs.
The axiom, import, and strict no-unfold probes ran afterward against that stable output
tree, using exact copies of the frozen final source/home. The final source SHA-256 is
`1b82e5834000bd0c5183efcd70dc3145f58a04c3bca0aba15b7a951ee503b44b`.

Final sweep tail:

```text
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
EXIT 0
MODULE TCSlib/Complexity/TuringMachine/UniversalK
TCSlib/Complexity/TuringMachine/UniversalK.lean:510:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/UniversalK.lean:555:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/UniversalK.lean:593:8: warning: declaration uses 'sorry'
EXIT 0
MODULE TCSlib/Complexity/TuringMachine/SelfUniversal
EXIT 0
MODULE TCSlib/Complexity/TuringMachine
EXIT 0
FINAL: 92/92 modules passed; ordered loop EXIT 0.
```

## Environment addendum

The unmodified pinned Lean failed with **`error: failed to locate application`** before
the fallback was used. The original diagnostic and successful version output are
quoted below. The exact authorized C source
was then compiled with:

```sh
cc -shared -fPIC -O2 executable-path.c -ldl -o executable-path.so
```

Its SHA-256 is
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`, matching the addendum.
The source is included at `evidence/runtime/executable-path.c`. The compiled `.so`,
toolchain, cache, scratch probes, and oleans are not shipped.

The exact process-scoped environment values used for Lean/Lake checks were:

```sh
PATH=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux/bin:$PATH
LEAN_SYSROOT=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/edcf4c9982ed/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/edcf4c9982ed/runtime/executable-path.so
```

The shim was scoped to Lean/Lake launch commands and check-script descendants, never
exported to the session. `lean --version` then printed Lean 4.25.0, commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`. No toolchain or
repository dependency source was patched and no permission or sandbox escalation was used.
Archive extraction used `--no-same-owner` and `TAR_OPTIONS=--no-same-owner`
after ownership-restoration errors. Cache
preparation used the prescribed `lake exe cache get` (including a successful targeted
retry); no `lake build` command was invoked by the agent.

A supplementary parallel recheck was stopped before completion and is not used as a
gate. It used isolated output paths ending in `.lake/u2s/final-oleans-0` through
`final-oleans-3`. Earlier scratch checks used
`TCSLIB_OLEANS=/workspace/scratch/edcf4c9982ed/tcslib/.lake/u2s/probe-oleans`.
All final gates instead used these exact additional environment values:

```sh
TCSLIB_OLEANS=/dev/shm/u2s-startup-edcf4c9982ed/oleans
TMPDIR=/dev/shm/u2s-startup-edcf4c9982ed/tmp
```

To recover the complete dependency data after the storage failures, the pinned project's
`lake exe cache lookup` selected the content-addressed archives for its 1,002 package
modules. The existing official `leantar-0.1.16` extracted those cached outputs into
memory-backed temporary storage, retaining the `.olean.private`, `.olean.server`, and
other companion data files needed by Lean 4.25.0. The actual mathlib checkout was
verified as `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, matching the manifest. No dependency
version, Lean binary, checking script, proof-checking option, or source file was changed
for this recovery. Cache and output-location changes affect temporary storage only.

## Archive and integration evidence

The archive contains this report, the full modified owned source at its repository path,
the format-patch series against the pinned base, the bundle with that base as its sole
prerequisite, the required verification and runtime-source evidence, both screens,
and `SHA256SUMS`. Bundle verification and the exact archive manifest are quoted below.
No unrelated untracked file or compiled build product is included.

## Complete external citation inventory

```text
Turing.FinTM
Turing.FinTM.k
Turing.FinTM.State
Turing.FinTM.tm
Turing.FinTM.fintypeState
Turing.FinTM.decEqState
Turing.FinTM.ComputesInTime
Turing.FinTM.ComputesFunInTime
Turing.FinTM.computesInTime_iff
Turing.FinTM.computesFunInTime_iff
Turing.FinTM.bufferedCompTM
Turing.FinTM.bufferedCompTM_State
Turing.FinTM.bufferedSecondCfg
Turing.FinTM.bufferedSecondCfg_state
Turing.FinTM.bufferTape_nil
Turing.MultiTapeTM
Turing.MultiTapeTM.q₀
Turing.MultiTapeTM.initCfg
Turing.MultiTapeTM.initCfg_eq
Turing.MultiTapeTM.initCfg_with_q₀
Turing.MultiTapeTM.runFrom
Turing.MultiTapeTM.runFrom_with_q₀
Turing.MultiTapeTM.runFrom_add
Turing.MultiTapeTM.runFrom_of_halt
Turing.MultiTapeTM.runFrom_state_ne_none_of_le
Turing.MultiTapeTM.exists_first_halt
Turing.MultiTapeTM.visitedByTapeHead
Turing.MultiTapeTM.spaceUsed
Turing.MultiTapeTM.spaceUsed_le_mul_succ
Turing.Cfg
Turing.Cfg.ext
Turing.Cfg.state
Turing.Cfg.inputPos
Turing.Cfg.workTapes
Turing.Cfg.workTapePos
Turing.Cfg.output
Turing.Cfg.Halted
Turing.Cfg.init
Turing.Cfg.init_state
Turing.Cfg.init_inputPos
Turing.Cfg.init_workTapes
Turing.Cfg.init_workTapePos
Turing.Cfg.init_output
Turing.Cfg.mapState
Turing.Cfg.mapState_state
Turing.Cfg.mapState_inputPos
Turing.Cfg.mapState_workTapes
Turing.Cfg.mapState_workTapePos
Turing.Cfg.mapState_output
Turing.prefixCanonTM
Turing.prefixCanonTM_eq
Turing.prefixCanon_start
Turing.prefixCanon_run
Turing.universalPrefixTM
Turing.pairEncode
Turing.embedSilentCfg
Turing.embedSilentCfg_selected_tape
Turing.embedSilentCfg_selected_pos
Turing.embedSilentCfg_cap
Turing.embedSilentCfg_unselected
Turing.embedSilentCfg_state
Turing.embedSilentCfg_inputPos
Turing.embedSilentCfg_output
Turing.embedSilentRetTM
Turing.embedSilentRetTM_run
Complexity.LogProg.CleanSt
Complexity.LogProg.CleanSt.init
Complexity.LogProg.cleanTM
Complexity.LogProg.cleanTM_run
Finset.univ
Finset.sup
Finset.le_sup
Finset.mem_univ
Finset.card
List.ofFn
List.ofFn_get
List.get
List.length
List.nil_append
List.length_nil
Nat.add_sub_of_le
Nat.cast_zero
Option.some_ne_none
Option.map_eq_none_iff
Option.map_some
Fin.ext
Fin.val
Set.range
Function.Embedding
Function.Embedding.toFun
Function.Embedding.inj'
congrArg
funext
lt_or_eq_of_le
lt_irrefl
Eq.trans
Bool
Nat
Int
Fin
List
Option
Option.none
Option.some
Sum
Sum.inl
Sum.inr
Unit
Unit.unit
Nat.exists_eq_add_of_le
```

## Reproducibility evidence

### First edit

```diff
diff --git a/TCSlib/Complexity/TuringMachine/UniversalK.lean b/TCSlib/Complexity/TuringMachine/UniversalK.lean
index 7e54aa4b..279ec003 100644
--- a/TCSlib/Complexity/TuringMachine/UniversalK.lean
+++ b/TCSlib/Complexity/TuringMachine/UniversalK.lean
@@ -7,6 +7,7 @@ import TCSlib.Complexity.TuringMachine.Codes2Tape
 import TCSlib.Complexity.TuringMachine.UniversalStartup
 import TCSlib.Complexity.TuringMachine.Build.StepBlockForward
 import TCSlib.Complexity.TuringMachine.Build.InputDevice
+import TCSlib.Complexity.SpaceComplexity.Machines.Clean
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
```

### Base admission set

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Build/NDHost: 1: ndWriterTM_run_block
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

### Rule 11 grep on the final diff

```text
Six R3 canonical rows, exact word-pattern grep of added source:
COMMAND: rg -n -f /workspace/scratch/edcf4c9982ed/evidence/r3-patterns.txt /workspace/scratch/edcf4c9982ed/evidence/added-source.txt
rg exit 1
NO MATCHES

Other-file private names (5046 unique spellings), fixed-word grep of added source:
COMMAND: rg -n -w -F -f /workspace/scratch/edcf4c9982ed/evidence/foreign-private-names.txt /workspace/scratch/edcf4c9982ed/evidence/added-source.txt
rg exit 0
166:private theorem ss_captureInitial {m n : ℕ} {S : Type} (M : MultiTapeTM m Bool S)
170:      Cfg.init (Sum.inl M.q₀ : S ⊕ Unit) x := by
191:  · rw [Cfg.mapState_state, embedSilentCfg_state, MultiTapeTM.initCfg_eq,
314:**Fill appendix (U2-S).** This delivery completes phase 1: a cleaned canonizer,

Reviewed spelling collisions (not references to foreign private declarations):
- S: local type binder in ss_captureInitial; also text in the U2-S appendix label.
- mapState_state: the qualified public Turing.Cfg.mapState_state equation, checked by the probe.
Actual references to other-file private declarations: none.
```

### Extended probe and axiom-print commands

```lean
Final source overlay plus all 100 provided #checks and 68 additional #checks.
The import context has only the four base imports and the authorized Clean import.

#check @Turing.FinTM
#check @Turing.FinTM.k
#check @Turing.FinTM.State
#check @Turing.FinTM.tm
#check @Turing.FinTM.fintypeState
#check @Turing.FinTM.decEqState
#check @Turing.FinTM.ComputesInTime
#check @Turing.FinTM.bufferTape_nil
#check @Turing.MultiTapeTM
#check @Turing.MultiTapeTM.q₀
#check @Turing.MultiTapeTM.initCfg
#check @Turing.MultiTapeTM.runFrom
#check @Turing.MultiTapeTM.runFrom_of_halt
#check @Turing.MultiTapeTM.runFrom_state_ne_none_of_le
#check @Turing.MultiTapeTM.exists_first_halt
#check @Turing.MultiTapeTM.visitedByTapeHead
#check @Turing.MultiTapeTM.spaceUsed
#check @Turing.Cfg
#check @Turing.Cfg.ext
#check @Turing.Cfg.state
#check @Turing.Cfg.inputPos
#check @Turing.Cfg.workTapes
#check @Turing.Cfg.workTapePos
#check @Turing.Cfg.output
#check @Turing.Cfg.Halted
#check @Turing.Cfg.init
#check @Complexity.LogProg.CleanSt.init
#check @Finset.univ
#check @Finset.sup
#check @Finset.le_sup
#check @Finset.mem_univ
#check @Finset.card
#check @List.ofFn
#check @List.ofFn_get
#check @List.get
#check @List.length
#check @List.nil_append
#check @List.length_nil
#check @Nat.add_sub_of_le
#check @Nat.cast_zero
#check @Option.some_ne_none
#check @Option.map_eq_none_iff
#check @Option.map_some
#check @Fin.ext
#check @Fin.val
#check @Set.range
#check @Function.Embedding
#check @Function.Embedding.toFun
#check @Function.Embedding.inj'
#check @congrArg
#check @funext
#check @lt_or_eq_of_le
#check @lt_irrefl
#check @Eq.trans
#check @Bool
#check @Nat
#check @Int
#check @Fin
#check @List
#check @Option
#check @Option.none
#check @Option.some
#check @Sum
#check @Sum.inl
#check @Sum.inr
#check @Unit
#check @Unit.unit

#print axioms Turing.exists_selfStartupTMK
#print axioms Turing.ss_cleanCanonizer
#print axioms Turing.ss_cleanCanonizer_run
#print axioms Turing.ss_cleanCanonizer_halts
#print axioms Turing.ss_lengthBound
#print axioms Turing.ss_cleanCanonizer_computes
#print axioms Turing.ss_bufferedHalt_iff
#print axioms Turing.ss_prefix_first_halt
#print axioms Turing.ss_cleanCanonizer_first_halt
#print axioms Turing.ss_captureInitial
#print axioms Turing.ss_captureTM
#print axioms Turing.ss_capture_run
#print axioms Turing.ss_capturedPrefix_run
#print axioms Turing.ss_sourceSlot
#print axioms Turing.ss_captureTape
#print axioms Turing.ss_capture_indices

#check @Nat.exists_eq_add_of_le
```

### Regional ownership check

```text
REGION FREEZE PASS: removing only the authorized import, private home and flagged appendix
recovers the pinned base byte for byte, including the target statement and body.
Target body is unchanged: sorry. U2-U and U2-E are untouched.
Tracked changed paths: TCSlib/Complexity/TuringMachine/UniversalK.lean
All 15 new declarations are private ss_ names. No new admitted helper.
No section/open/variable/namespace introduced in the home.
No new line exceeds 100 characters. git diff --check: PASS.
Final source: 601 lines, 12 explicit public declarations,
15 explicit private declarations (4 definitions, 11 theorems).
Counts exclude generated constructors, projections, instances and equation lemmas.
SHA-256 1b82e5834000bd0c5183efcd70dc3145f58a04c3bca0aba15b7a951ee503b44b

New private declarations:
def ss_cleanCanonizer
theorem ss_cleanCanonizer_run
theorem ss_cleanCanonizer_halts
theorem ss_lengthBound
theorem ss_cleanCanonizer_computes
theorem ss_bufferedHalt_iff
theorem ss_prefix_first_halt
theorem ss_cleanCanonizer_first_halt
theorem ss_captureInitial
def ss_captureTM
theorem ss_capture_run
theorem ss_capturedPrefix_run
def ss_sourceSlot
def ss_captureTape
theorem ss_capture_indices
```

### Original Lean startup failure

```text
error: failed to locate application
```

### Pinned Lean after the authorized fallback

```text
Lean (version 4.25.0, x86_64-unknown-linux-gnu, commit cdd38ac5115bdeec5f609e9126cce00f51ae88b3, Release)
```

### Final axiom prints

```text
.lake/u2s/AxiomProbe.lean:510:8: warning: declaration uses 'sorry'
.lake/u2s/AxiomProbe.lean:555:8: warning: declaration uses 'sorry'
.lake/u2s/AxiomProbe.lean:593:8: warning: declaration uses 'sorry'
'Turing.exists_selfStartupTMK' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_cleanCanonizer' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_cleanCanonizer_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_cleanCanonizer_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_lengthBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_cleanCanonizer_computes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_bufferedHalt_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_prefix_first_halt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_cleanCanonizer_first_halt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_captureInitial' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_captureTM' depends on axioms: [propext, Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_capture_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_capturedPrefix_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_sourceSlot' depends on axioms: [propext, Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_captureTape' depends on axioms: [propext, Quot.sound]
'_private.«.lake».u2s.AxiomProbe.0.Turing.ss_capture_indices' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Bundle verification

```text
Command: git bundle verify fill-u2s-startup.bundle
/workspace/scratch/edcf4c9982ed/delivery/fill-u2s-startup/fill-u2s-startup.bundle is okay
The bundle contains this ref:
259a349d52203807da2d292d81e2c3a56a807dd5 refs/heads/fill/u2s-startup
The bundle requires this ref:
94b986d4db7167ab2a8b20d38d4385f11e60be0e 
The bundle uses this hash algorithm: sha1

Bundle refs:
259a349d52203807da2d292d81e2c3a56a807dd5 refs/heads/fill/u2s-startup

Verified prerequisite count: 1 (the pinned base).
Format-patch reverse application check against the delivered tree: PASS.
```

### Archive manifest

```text
REPORT.md
SHA256SUMS
TCSlib/Complexity/TuringMachine/UniversalK.lean
evidence/logs/axioms.log
evidence/logs/bootstrap.log
evidence/logs/final-sweep.log
evidence/runtime/executable-path.c
evidence/screen-after.txt
evidence/screen-before.txt
fill-u2s-startup.bundle
patches/0001-feat-u2s-prove-cleaned-canonizer-and-partial-capture.patch
```

<details>
<summary>Complete before-screen output</summary>

```text
declarations screened: 655; copy pairs (target reproduces >= half of source): 514; reproduced text: 151,065 chars
   Catalog.lean::f2_timed_branch_run  reproduces  Wrappers.lean::timed_branch_run: 1051/1051 = 100%
   Catalog.lean::f2_timedCondTM  reproduces  Wrappers.lean::timedCondTM: 802/802 = 100%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::f2_space_of_time: 713/713 = 100%
   Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Catalog.lean::f2_timed_control_init  reproduces  Wrappers.lean::timed_control_init: 470/470 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::catalog_redirect_loop: 140/140 = 100%
   Catalog.lean::catalog_redirect_loop  reproduces  Wrappers.lean::redirect_loop: 140/140 = 100%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Wrappers.lean::timedBranchCfg  reproduces  Catalog.lean::f2_timedBranchCfg: 92/92 = 100%
   Catalog.lean::f2_timedBranchCfg  reproduces  Wrappers.lean::timedBranchCfg: 92/92 = 100%
   Wrappers.lean::timedControlCfg  reproduces  Catalog.lean::f2_timedControlCfg: 89/89 = 100%
   Catalog.lean::f2_timedControlCfg  reproduces  Wrappers.lean::timedControlCfg: 89/89 = 100%
   Wrappers.lean::redirectState  reproduces  Catalog.lean::catalog_redirectState: 78/78 = 100%
   Catalog.lean::catalog_redirectState  reproduces  Wrappers.lean::redirectState: 78/78 = 100%
   Wrappers.lean::timedPadTM  reproduces  Catalog.lean::f2_timedPadTM: 72/72 = 100%
   Catalog.lean::f2_timedPadTM  reproduces  Wrappers.lean::timedPadTM: 72/72 = 100%
   Catalog.lean::catalog_redirectAction  reproduces  Wrappers.lean::redirectAction: 71/71 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Wrappers.lean::timedCondTM  reproduces  Catalog.lean::f2_timedCondTM: 802/805 = 100%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   Catalog.lean::f2_timedReadyCfg  reproduces  Wrappers.lean::timedReadyCfg: 136/137 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Catalog.lean::catalog_redirectCfg  reproduces  Wrappers.lean::redirectCfg: 84/85 = 99%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Catalog.lean::f2_timed_start  reproduces  Wrappers.lean::timed_start: 1025/1049 = 98%
   Wrappers.lean::timed_control_init  reproduces  Catalog.lean::f2_timed_control_init: 470/482 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Wrappers.lean::timed_branch_run  reproduces  Catalog.lean::f2_timed_branch_run: 1051/1081 = 97%
   Wrappers.lean::timedReadyCfg  reproduces  Catalog.lean::f2_timedReadyCfg: 136/140 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Wrappers.lean::computesFunInTime_cond  reproduces  Catalog.lean::f2_cond_time: 621/641 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::copyMapTM: 478/498 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   Wrappers.lean::timed_start  reproduces  Catalog.lean::f2_timed_start: 1025/1073 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::catalog_redirect_apply  reproduces  Wrappers.lean::redirect_apply: 175/187 = 94%
   Catalog.lean::f2_timed_capture  reproduces  Wrappers.lean::timed_capture: 314/338 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_timed_read  reproduces  Wrappers.lean::timed_read: 1692/1832 = 92%
   Catalog.lean::f2_cond_time  reproduces  Wrappers.lean::computesFunInTime_cond: 621/673 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Wrappers.lean::timed_capture  reproduces  Catalog.lean::f2_timed_capture: 314/347 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Wrappers.lean::redirectCfg  reproduces  Catalog.lean::catalog_redirectCfg: 84/93 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Wrappers.lean::redirectAction  reproduces  Catalog.lean::catalog_redirectAction: 71/79 = 90%
   Catalog.lean::catalog_redirect_step  reproduces  Wrappers.lean::redirect_step: 826/921 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::transferMapTM: 478/533 = 90%
   Catalog.lean::catalog_redirect_run  reproduces  Wrappers.lean::redirect_run: 160/180 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_timed_read: 1692/1931 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   UniversalInterpreter.lean::universalInterpreter  reproduces  UniversalInterpreter.lean::universalSkipDone: 60/69 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Simulation.lean::bufferedFirstCfg_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Wrappers.lean::redirect_apply  reproduces  Catalog.lean::catalog_redirect_apply: 175/203 = 86%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::clearTM: 344/409 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   Wrappers.lean::redirect_step  reproduces  Catalog.lean::catalog_redirect_step: 826/1041 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   UniversalStartup.lean::universalCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Wrappers.lean::redirect_run  reproduces  Catalog.lean::catalog_redirect_run: 160/204 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Simulation.lean::bufferedFirstCfg_init  reproduces  UniversalStartup.lean::universalCapture_init: 255/334 = 76%
   Wrappers.lean::emit_run  reproduces  UniversalStartup.lean::universalCapture_run: 129/169 = 76%
   Wrappers.lean::capture_run  reproduces  UniversalStartup.lean::universalCapture_run: 129/169 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  UniversalStartup.lean::universalCapture_run: 128/169 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyMapTM: 369/498 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Clean.lean::cleanTM_run  reproduces  CleanSweep.lean::PB_ccfg: 94/128 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 706/970 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 706/987 = 72%
   Wrappers.lean::emit_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Wrappers.lean::capture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   CleanSweep.lean::erase_run  reproduces  CleanSweep.lean::goR_run: 1095/1548 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::transferTM_run: 478/680 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   CleanSweep.lean::back_run  reproduces  CleanSweep.lean::goR_run: 1077/1548 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::emit_run: 430/626 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   CleanSweep.lean::goR_run  reproduces  CleanSweep.lean::back_run: 1077/1580 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   CleanSweep.lean::erase_run  reproduces  CleanSweep.lean::back_run: 1058/1580 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 637/970 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 171/264 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferMapTM: 344/533 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   UniversalStartup.lean::universalCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   UniversalStartup.lean::universalCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_cond_ledger  reproduces  Wrappers.lean::timed_start: 655/1049 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Wrappers.lean::captureCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 129/212 = 61%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::capture_run: 430/708 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Simulation.lean::bufferedCompTM  reproduces  UniversalStartup.lean::universalCaptureTM: 223/372 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 109/184 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 168/290 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::clearTM_run: 220/385 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::f2_loopBodyCfg  reproduces  Wrappers.lean::captureCfg: 129/227 = 57%
   Simulation.lean::bufferedFirstCfg_step  reproduces  UniversalStartup.lean::universalCapture_step: 725/1281 = 57%
   Wrappers.lean::emit_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/228 = 57%
   Wrappers.lean::capture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/228 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::copyTM_run: 228/404 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::f2_rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_control_heads: 95/169 = 56%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::copyTM_run: 225/404 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   CleanSweep.lean::cleanTM  reproduces  Clean.lean::simSt: 76/140 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   Catalog.lean::f2_extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalStartup.lean::universalCanon_complete: 141/262 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Simulation.lean::bufferedSecondCfg_step  reproduces  UniversalStartup.lean::universalCapture_init: 175/334 = 52%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::clearTM_run: 198/385 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Wrappers.lean::captureCfg  reproduces  Wrappers.lean::emitCfg: 61/119 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Wrappers.lean::redirect_loop: 71/140 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::compareTM_run_stop_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_write_take: 62/124 = 50%
```

</details>

<details>
<summary>Complete after-screen output</summary>

```text
declarations screened: 668; copy pairs (target reproduces >= half of source): 514; reproduced text: 151,065 chars
   Catalog.lean::f2_timed_branch_run  reproduces  Wrappers.lean::timed_branch_run: 1051/1051 = 100%
   Catalog.lean::f2_timedCondTM  reproduces  Wrappers.lean::timedCondTM: 802/802 = 100%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::f2_space_of_time: 713/713 = 100%
   Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Catalog.lean::f2_timed_control_init  reproduces  Wrappers.lean::timed_control_init: 470/470 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::catalog_redirect_loop: 140/140 = 100%
   Catalog.lean::catalog_redirect_loop  reproduces  Wrappers.lean::redirect_loop: 140/140 = 100%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   Wrappers.lean::timedBranchCfg  reproduces  Catalog.lean::f2_timedBranchCfg: 92/92 = 100%
   Catalog.lean::f2_timedBranchCfg  reproduces  Wrappers.lean::timedBranchCfg: 92/92 = 100%
   Wrappers.lean::timedControlCfg  reproduces  Catalog.lean::f2_timedControlCfg: 89/89 = 100%
   Catalog.lean::f2_timedControlCfg  reproduces  Wrappers.lean::timedControlCfg: 89/89 = 100%
   Wrappers.lean::redirectState  reproduces  Catalog.lean::catalog_redirectState: 78/78 = 100%
   Catalog.lean::catalog_redirectState  reproduces  Wrappers.lean::redirectState: 78/78 = 100%
   Wrappers.lean::timedPadTM  reproduces  Catalog.lean::f2_timedPadTM: 72/72 = 100%
   Catalog.lean::f2_timedPadTM  reproduces  Wrappers.lean::timedPadTM: 72/72 = 100%
   Catalog.lean::catalog_redirectAction  reproduces  Wrappers.lean::redirectAction: 71/71 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Wrappers.lean::timedCondTM  reproduces  Catalog.lean::f2_timedCondTM: 802/805 = 100%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   Catalog.lean::f2_timedReadyCfg  reproduces  Wrappers.lean::timedReadyCfg: 136/137 = 99%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Catalog.lean::catalog_redirectCfg  reproduces  Wrappers.lean::redirectCfg: 84/85 = 99%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Catalog.lean::f2_timed_start  reproduces  Wrappers.lean::timed_start: 1025/1049 = 98%
   Wrappers.lean::timed_control_init  reproduces  Catalog.lean::f2_timed_control_init: 470/482 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Wrappers.lean::timed_branch_run  reproduces  Catalog.lean::f2_timed_branch_run: 1051/1081 = 97%
   Wrappers.lean::timedReadyCfg  reproduces  Catalog.lean::f2_timedReadyCfg: 136/140 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   Wrappers.lean::computesFunInTime_cond  reproduces  Catalog.lean::f2_cond_time: 621/641 = 97%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::copyMapTM: 478/498 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   Wrappers.lean::timed_start  reproduces  Catalog.lean::f2_timed_start: 1025/1073 = 96%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Catalog.lean::catalog_redirect_apply  reproduces  Wrappers.lean::redirect_apply: 175/187 = 94%
   Catalog.lean::f2_timed_capture  reproduces  Wrappers.lean::timed_capture: 314/338 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_timed_read  reproduces  Wrappers.lean::timed_read: 1692/1832 = 92%
   Catalog.lean::f2_cond_time  reproduces  Wrappers.lean::computesFunInTime_cond: 621/673 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Wrappers.lean::timed_capture  reproduces  Catalog.lean::f2_timed_capture: 314/347 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Wrappers.lean::redirectCfg  reproduces  Catalog.lean::catalog_redirectCfg: 84/93 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Wrappers.lean::redirectAction  reproduces  Catalog.lean::catalog_redirectAction: 71/79 = 90%
   Catalog.lean::catalog_redirect_step  reproduces  Wrappers.lean::redirect_step: 826/921 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::transferMapTM: 478/533 = 90%
   Catalog.lean::catalog_redirect_run  reproduces  Wrappers.lean::redirect_run: 160/180 = 89%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_timed_read: 1692/1931 = 88%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   UniversalInterpreter.lean::universalInterpreter  reproduces  UniversalInterpreter.lean::universalSkipDone: 60/69 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   Simulation.lean::bufferedFirstCfg_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Wrappers.lean::redirect_apply  reproduces  Catalog.lean::catalog_redirect_apply: 175/203 = 86%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::clearTM: 344/409 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   Wrappers.lean::redirect_step  reproduces  Catalog.lean::catalog_redirect_step: 826/1041 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   UniversalStartup.lean::universalCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Wrappers.lean::redirect_run  reproduces  Catalog.lean::catalog_redirect_run: 160/204 = 78%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Simulation.lean::bufferedFirstCfg_init  reproduces  UniversalStartup.lean::universalCapture_init: 255/334 = 76%
   Wrappers.lean::emit_run  reproduces  UniversalStartup.lean::universalCapture_run: 129/169 = 76%
   Wrappers.lean::capture_run  reproduces  UniversalStartup.lean::universalCapture_run: 129/169 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  UniversalStartup.lean::universalCapture_run: 128/169 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   Wrappers.lean::redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyMapTM: 369/498 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Clean.lean::cleanTM_run  reproduces  CleanSweep.lean::PB_ccfg: 94/128 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 706/970 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 706/987 = 72%
   Wrappers.lean::emit_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Wrappers.lean::capture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   CleanSweep.lean::erase_run  reproduces  CleanSweep.lean::goR_run: 1095/1548 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::transferTM_run: 478/680 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   CleanSweep.lean::back_run  reproduces  CleanSweep.lean::goR_run: 1077/1548 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::emit_run: 430/626 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   CleanSweep.lean::goR_run  reproduces  CleanSweep.lean::back_run: 1077/1580 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   CleanSweep.lean::erase_run  reproduces  CleanSweep.lean::back_run: 1058/1580 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 637/970 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 171/264 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferMapTM: 344/533 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   UniversalStartup.lean::universalCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   UniversalStartup.lean::universalCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_cond_ledger  reproduces  Wrappers.lean::timed_start: 655/1049 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Wrappers.lean::captureCfg  reproduces  Catalog.lean::f2_loopBodyCfg: 129/212 = 61%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::capture_run: 430/708 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Simulation.lean::bufferedCompTM  reproduces  UniversalStartup.lean::universalCaptureTM: 223/372 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 109/184 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 168/290 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::clearTM_run: 220/385 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Catalog.lean::f2_loopBodyCfg  reproduces  Wrappers.lean::captureCfg: 129/227 = 57%
   Simulation.lean::bufferedFirstCfg_step  reproduces  UniversalStartup.lean::universalCapture_step: 725/1281 = 57%
   Wrappers.lean::emit_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/228 = 57%
   Wrappers.lean::capture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 129/228 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::copyTM_run: 228/404 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::f2_rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Wrappers.lean::timed_read  reproduces  Catalog.lean::f2_control_heads: 95/169 = 56%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::copyTM_run: 225/404 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   CleanSweep.lean::cleanTM  reproduces  Clean.lean::simSt: 76/140 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   Catalog.lean::f2_extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalStartup.lean::universalCanon_complete: 141/262 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Wrappers.lean::redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Simulation.lean::bufferedSecondCfg_step  reproduces  UniversalStartup.lean::universalCapture_init: 175/334 = 52%
   Wrappers.lean::emit_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::emit_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Wrappers.lean::capture_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Wrappers.lean::redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::clearTM_run: 198/385 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   Wrappers.lean::captureCfg  reproduces  Wrappers.lean::emitCfg: 61/119 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Wrappers.lean::redirect_loop: 71/140 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Catalog.lean::compareTM_run_stop_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_write_take: 62/124 = 50%
```

</details>

