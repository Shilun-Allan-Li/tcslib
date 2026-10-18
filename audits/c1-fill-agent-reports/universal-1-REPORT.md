# C1-UN fill report

**Verified partial delivery: phase 1 complete (3/4 targets filled).** The three corollaries
are checked modulo the admission sources below. The universal setup remains open under
ground rules 4 and 10; no setup witness is asserted.

## Provenance and scope

- Base: `83ec6348b325f060cec2a917b45a4eda6e301d84`.
- Delivery commit: `483fb579e8dd1a0c63c066f136ef28602fa74973` (one commit; sole parent is the base).
- Cloned `complexity/arora-barak-ch3-4`, whose observed tip was
  `2cce48048b5875fae75d69ef70ee9032b6b5e744`. The required ancestor check succeeded.
- Created `fill/c1-universal` at the exact base. No rebase, merge, cherry-pick, push or PR.
- Attachment SHA-256: `12086525602871d7395fca72d1002ff27e4baf86e33fdd036571f8066cf71542`.
  The repository brief matches after replacing its `@ANCESTOR@` placeholders with the base.
- Addendum SHA-256: `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928`.
  Its repository copy is byte-identical to the attachment.
- The first source edit added exactly the five authorized imports, in the prescribed order.
  All subsequent edits are the three corollary bodies and four flagged docstring appendices.
  Reversing those edits reproduces the entire base file byte-for-byte.
- All five signatures, the module header/docstring, and the whole `ntime_hierarchy`
  declaration and body are unchanged. No other tracked file is changed.
- No new declaration, public or private. Final source: **404 lines; 5 public / 0 private**
  declarations (base: 342 lines; 5 / 0). No new line exceeds 100 characters. `git diff --check` passes.

## Targets and phase

| Target | Body status | Remaining admission sources |
|---|---|---|
| `Turing.exists_timed_universal_NDTM` | Open | Its own retained `sorry` |
| `Turing.exists_ndAcceptsWithin_decider` | Filled by the prescribed citation | Universal target; `FinNDTM.exists_exhaustiveDecider` |
| `Complexity.ntime_hierarchy_of_pos` | Filled | `Complexity.ntime_hierarchy` |
| `Complexity.NTIME_linear_ssubset_square` | Filled | `Complexity.ntime_hierarchy` |

Phase 1's three bodies are implemented and verified. Phase 2 stops at the scratch cleanup API gap below;
phase 3 is not attempted. The consumer probe was read, but its conditional assembly was not
copied into a new lemma with an unproved setup hypothesis. The hierarchy stub remains outside
this batch's ownership. Every retained open declaration still has its literal **Proof sketch**.

For the positive-bound result, `NTIME.mono` first transfers from `g + 1` to `2 * g`;
the membership witness's constant is then multiplied by two, through `mem_NTIME_iff` and
`decidesInTime_iff`. This reuses the published transfer of halting and acceptance instead of
re-proving that argument. Reverse monotonicity identifies the two classes.

The showcase uses `timeConstructible_poly 1 0` and `timeConstructible_poly 1 1` and the prescribed
threshold `3 * A + 4`. Its arithmetic proof also covers `A = 0`.

## Escalation UN-1: complete scratch configuration of the first-component extractor

**Binding stop: ground rules 4 and 10.** The route requires the output of
`prefixCanonTM (FinTM.pairExtractTM true false)` to be captured and every scratch tape subsequently
cleared. `prefixCanon_complete` gives halting, output and the native input position.
`prefixCanon_run` additionally identifies the buffered configuration, but retains the
first-component extractor's terminal configuration as an opaque argument. The public
`FinTM.pairExtractTM_computes`, `_fst`, `_snd` and `_concat` contracts give computational output
and time; none describes that extractor's work-tape contents or work-head positions.

The next cleanup step, `clearTM_run_ofCfg`, requires a delimited word at the tape's current head;
`skipBackTM_run_ofCfg` similarly requires a specified delimited word behind the head. A bound on
execution time alone does not establish either hypothesis. The relevant implementation-level
facts are private in `Build/Primitives`. Neither unfolding that machine nor citing those privates
is permitted. No replacement parser or cleanup host was built, and no declaration from a later commit was used.

**Requested public lemma**, suggested name `FinTM.pairExtractTM_fst_run`: for arbitrary binary
lists `a, b`, let `M := FinTM.pairExtractTM true false` and

```lean
let d := M.tm.runFrom (M.tm.initCfg (pairEncode a b))
  (5 * ((pairEncode a b).length + 1))
```

Expose the complete terminal data, in particular

```lean
d.state = none ∧ d.output = a ∧ d.inputPos.val = 2 * a.length + 3 ∧
  ∀ j : Fin M.k,
    d.workTapes j = FinTM.bufferTape a ∧ d.workTapePos j = (a.length : ℤ)
```

This is a requested interface, **not a theorem proved in this delivery**. A public equivalent
complete configuration contract would also discharge the identified obstruction. After it lands,
continue with capture, expansion, scratch erasure, the first-exit proof and the total time ledger.
The request does not certify that no further API gap will arise.

**Proof sketch — open universal target.** Capture the header's first component silently, expand
its binary value into the stream block, clear scratch tapes and restore all heads, and prove the
setup's first exit with its per-code bound. Then use consumer probe 1's assembly and core contract.
The setup has not been constructed: no `C_P` or total setup ledger is claimed. The planned final
universal constant remains the probe's `C_P + C_R + 13`. The cases `t = 0` and `x = []` remain
obligations of this open setup; they have not been marked verified.

**Proof sketch — frozen hierarchy stub.** The existing docstring retains the fixed-code
schedule, capped ladder locator, guessed-stream simulation, two transfers and chain contradiction.
This declaration and its `sorry` are byte-identical to the base and are not attempted here.

**Promotion candidate:** the header-first-component pass with complete cleanup, also needed by
R's startup and B5a's H1 continuation. The requested extractor contract is a prerequisite; no
private implementation is offered for promotion.

## Explicit external citations and import probe

The new proof bodies explicitly cite:

- `Turing.ndAcceptsWithin_decider_of_universal`;
- `Complexity.NTIME.mono`, `Complexity.mem_NTIME_iff`;
- `Turing.FinNDTM.decidesInTime_iff`;
- `Complexity.timeConstructible_poly`;
- `Set.Subset.antisymm`, `Nat.le_succ`, `Nat.mul_assoc`, `Nat.zero_add`,
  `pow_one`, `one_mul`, `pow_pos`, `Nat.succ_pos`, `Nat.mul_le_mul_right`.

The original 53-check import probe is extended with the nine explicitly named standard lemmas
not already in it. Seven additional checks cover the public interfaces named in escalation UN-1:
`Turing.prefixCanon_run`, `Turing.FinTM.pairExtractTM`, `Turing.FinTM.pairExtractTM_computes`,
`Turing.FinTM.pairExtractTM_snd`, `Turing.FinTM.pairExtractTM_concat`,
`Turing.FinTM.bufferTape` and `Turing.pairEncode`. Thus the extended probe has 69 checks.
All campaign declarations are public at the base. The tactics are `exact`,
`have`, `intro`, `obtain`, `apply`, `refine`, `rw`, `funext`, `simp only`,
`simpa only`, `decide`, `omega` and `nlinarith`;
no proof unfolds any imported campaign definition. No R3 canonical row or other-file private
name appears in the added code (exact-name scan, after stripping comments from the inventory).
The extra declarations in the read-only axiom probe are evidence utilities, not source changes;
its admission walk is reused from `audits/evidence/s12-8/S128FillAAdmissionWalk.lean.txt`.

## Environment

Pinned unmodified Lean initially printed `error: failed to locate application`.
The exact addendum source was compiled, without modifying Lean, Lake, the kernel or host/toolchain permissions.
Its SHA-256 is `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
It is included under `evidence/runtime/`; the compiled shared object is excluded.
With the fallback, the binary reports Lean 4.25.0, commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.

The Lean/Lake commands use these exact settings:

```text
LEAN_SYSROOT=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux
LD_PRELOAD=/dev/shm/c1-universal/executable-path.so
PATH=/workspace/scratch/177f06803258/runtime/lean-4.25.0-linux/bin:<inherited PATH>
```

The preload is scoped to Lean/Lake command invocations and their check-script processes.
The installed pinned toolchain is reused read-only; copied dependency checkouts were verified
against every corresponding manifest revision, including mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

Storage was exhausted during the initial unrestricted cache retrieval. The first bootstrap
attempt failed on `ChoiceWords` with a bus error and no fresh olean. That attempt is retained in
the bootstrap evidence; it is not counted as a successful check. Recovery removed only this
attempt's generated dependency build products, preserved sources and Git metadata, and restored
the dependency cache from the verified pinned copy. The retry requests only the 33 direct
Mathlib imports in the prescribed module order and their dependencies, with
`MATHLIB_CACHE_DIR=/dev/shm/c1-universal/mathlib-cache`. That retrieval succeeded:
1,003 dependency files unpacked, exit 0. The successful retry starts after cache retrieval
finishes. Checks use `TMPDIR=/dev/shm/c1-universal/tmp` and
`TCSLIB_OLEANS=/dev/shm/c1-universal/oleans`. To reduce memory pressure, 10,858 byte-identical
dependency-cache files (897,597,112 bytes) were atomically replaced with symlinks
to the pinned cache, used read-only, after comparing SHA-256 hashes. Sources and cache contents did not change.
No `lake build` is run.

## Verification results

Bootstrap: **72/72 modules passed**, exit 0, no errors. The owned file has exactly the
universal target and frozen hierarchy sorry warnings, and no other warning.
Final sweep: **72/72 modules passed** in a separate, initially empty olean tree; exit 0,
no errors, and fresh nonempty oleans. The 69-check import probe and the axiom probe each
passed with exit 0, no errors and no warnings. No new private needs an axiom print.
The final tree is `/dev/shm/c1-universal/final-oleans`.
The base sorry list has 29 entries in 13 modules and is recorded by name in the bootstrap log.
The observed difference is removal of precisely the three corollaries' direct sorry warnings,
leaving **26 sorry warnings in 13 modules**, including the universal target and the frozen
hierarchy stub. There is no other admission difference. The 326 non-sorry compiler warnings
are in unchanged upstream source; bootstrap and final warning diagnostics are identical.

Freeze and region check: PASS. R3/private-name checks: PASS. Line-length check: PASS.
Style lint: `0 FAIL, 1 WARN over 4 files`; the unchanged warning is `EXPCOM`'s two definitions
without adjacent API lemmas. Both text screens use v3, one at a time under `nice -n 10`.

### Final sweep tail

```text
PASS TCSlib/Complexity/ClassOracle/Classes
CHECK TCSlib/Complexity/Diagonalization/EXPCOM
PASS TCSlib/Complexity/Diagonalization/EXPCOM
CHECK TCSlib/Complexity/Diagonalization/NTimeHierarchy
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:176:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:318:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/Diagonalization/NTimeHierarchy
CHECK TCSlib/Complexity/Diagonalization/NotTimeConstructible
PASS TCSlib/Complexity/Diagonalization/NotTimeConstructible
CHECK TCSlib/Complexity/Diagonalization/Relativization
PASS TCSlib/Complexity/Diagonalization/Relativization
CHECK TCSlib/Complexity/Diagonalization
PASS TCSlib/Complexity/Diagonalization
FINAL SWEEP PASS 72/72
```

### Actual target axiom prints and walks

```text
CHECK C1UniversalAxioms
'Turing.exists_timed_universal_NDTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Turing.exists_timed_universal_NDTM: direct sorryAx users in closure: [Turing.exists_timed_universal_NDTM]
'Turing.exists_ndAcceptsWithin_decider' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Turing.exists_ndAcceptsWithin_decider: direct sorryAx users in closure: [Turing.FinNDTM.exists_exhaustiveDecider,
 Turing.exists_timed_universal_NDTM]
'Complexity.ntime_hierarchy_of_pos' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.ntime_hierarchy_of_pos: direct sorryAx users in closure: [Complexity.ntime_hierarchy]
'Complexity.NTIME_linear_ssubset_square' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
Complexity.NTIME_linear_ssubset_square: direct sorryAx users in closure: [Complexity.ntime_hierarchy]
PASS C1UniversalAxioms
```

Each axiom set contains only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
The displayed direct-admission closures are exact; no additional stub is hidden.

## Duplication

**new copies: none.** The declaration population increases from 67 to 70 because three
previously sorried bodies are filled. The 14 pairs and 3,174 reproduced characters are unchanged.
There are no new in-file or cross-file pairs to justify. Full outputs follow.

### Before

```text
declarations screened: 67; copy pairs (target reproduces >= half of source): 14; reproduced text: 3,174 chars
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   NDHost.lean::guessRunTM_runWith_live  reproduces  NDHost.lean::guessRunTM_runWith_handoff_state: 81/93 = 87%
   NDHost.lean::guessRunTM_runWith  reproduces  NDHost.lean::guessRunTM_runWith_handoff_state: 81/93 = 87%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   NDHost.lean::GuessRunPhase.instDecidableEqState  reproduces  NDHost.lean::GuessRunPhase.instFintypeState: 165/235 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   NDHost.lean::GuessRunPhase.instFintypeState  reproduces  NDHost.lean::GuessRunPhase.instDecidableEqState: 165/259 = 64%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   NDHost.lean::guessRunCfg  reproduces  NDHost.lean::streamStartCfg: 81/161 = 50%
```

### After

```text
declarations screened: 70; copy pairs (target reproduces >= half of source): 14; reproduced text: 3,174 chars
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   NDHost.lean::guessRunTM_runWith_live  reproduces  NDHost.lean::guessRunTM_runWith_handoff_state: 81/93 = 87%
   NDHost.lean::guessRunTM_runWith  reproduces  NDHost.lean::guessRunTM_runWith_handoff_state: 81/93 = 87%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   NDHost.lean::GuessRunPhase.instDecidableEqState  reproduces  NDHost.lean::GuessRunPhase.instFintypeState: 165/235 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   NDHost.lean::GuessRunPhase.instFintypeState  reproduces  NDHost.lean::GuessRunPhase.instDecidableEqState: 165/259 = 64%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   NDHost.lean::guessRunCfg  reproduces  NDHost.lean::streamStartCfg: 81/161 = 50%
```

## Brief checklist

- [x] Targets and phase: phase 1 complete (3/4); phase 2 escalated; base and ancestor check recorded.
- [x] Five imports were the first source edit; only owned regions subsequently changed.
- [x] New declarations: none; four required fill appendices present.
- [x] Setup constants and ledger: explicitly unproved; planned final constant recorded.
- [x] Promotion candidate and escalation UN-1 recorded.
- [x] Rule 10 citations enumerated; 69-check probe passed. Rule 11 scan passed.
- [x] Both v3 screens quoted; no new pairs; **new copies: none**.
- [x] File size, final sweep tail, exact axiom walks and lint line recorded.

## Delivery integrity

The archive contains the full owned source, one format-patch file, and a verified git bundle
whose sole prerequisite is the base above. The source copy matches the delivery commit byte
for byte. The three logs include the exact probe sources and outputs; the shim C source is
included as required by the addendum. No shared object, olean, dependency cache or other build
product is shipped. `SHA256SUMS` covers every archive member except itself.

## Notation in the requested interface

`a` and `b` are the two binary lists in the encoded pair; `M` is the existing first-component
extractor; `d` is its terminal configuration. `C_P` denotes the unproved setup-time coefficient,
and `C_R` the interpreter-core coefficient in the binding consumer probe.
