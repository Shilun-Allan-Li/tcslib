# ZF-B2 delivery: Task 1 complete; uniform scheme blocked by import scope

**Task 1 is complete. One of the two existence targets is proved.**
Exactly **46** local copies were deleted and every use was rewritten to
the promoted public name. Exactly **24** private declarations remain,
as the B2 brief requires. `exists_effectiveMachineCode2` is checked with
no `sorryAx`; `exists_uniformMachineCode2` retains its original admission.

Task 2 requires an import-scope amendment: B2 forbids new imports but also
requires citation of the unimported `Build.VirtualInput` and `Build.Catalog`
machinery. The compiled environment confirms those names are unavailable.
`CONTINUATION.md` records the evidence, the two exact imports requested,
and the remaining construction obligations. This is not a claim that the
uniform theorem is false or that importing those modules completes it.

## Revision, scope, and commits

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Cloned branch: `complexity/arora-barak-ch3-4`; working branch: `fill/zone-f1-B2`.
- Recorded base: `42627f368fef1fbdc5f0c8af777498d26be124bd`.
- Brief issue commit: `f171767f32e573c345f3fa9b6e9fb87e14b84ddf`.
  The only intervening commit added continuation briefs, evidence, and a
  plan entry; the owned source and promoted originals did not change.
- First commit: `06fb5b1f18268285546e5ad98775aa8ab441cbbb` — applied
  `audits/evidence/zone-f1-B.patch` by `git am -3`, preserving the original
  Codex author and author date (2026-10-10 00:46:39 -0300).
- Second commit: `3a621e903bd27311741456994917473478994bb8` — the 46 deletions, name substitutions,
  and explicitly flagged documentation appendices.
- The only tracked path changed is
  `TCSlib/Complexity/TuringMachine/Codes2Tape.lean`.
- No rebase, push, PR, or `lake build` was performed. NDCodes is byte-identical
  to base. All nine received public signatures and their order are frozen.

Read the complete B2 brief, original ZF-B brief and report, all four inherited
zone audit documents, `AGENTS.md`, `policy.md`, and `workflow.md`.

## Task 1 verification and source changes

The completed cleanup is mechanical. `freeze.log` verifies from source that:

1. The deletion set is exactly the 46 names listed below, with no other
   declaration removed or added by the cleanup commit.
2. Every removed declaration's promoted original is public and matches
   after helper-name/visibility normalization.
3. Every surviving declaration body equals the applied ZF-B body after
   precisely those 46 substitutions. The effective theorem's proof is
   unchanged. The uniform theorem is unchanged from the recorded base.
4. All nine original public declarations retain their signatures and order;
   all other original public bodies are unchanged.
5. The only added imports relative to base are the sanctioned
   `TCSlib.Complexity.TuringMachine.MathlibBridge` and
   `Mathlib.Tactic.FinCases`.

Flagged documentation: the prior patch's `ZF-B status appendix` and
`ZF-B implementation appendix` remain. This cleanup adds the module's
`ZF-B2 cleanup appendix` and a paragraph in the private implementation
section clarifying that the 46 formerly inaccessible helpers are now cited.
The source is 598 lines. No new Task-2 helper, admitted or otherwise, was added.

The concrete grammar and effective construction are preserved: canonical
binary count, guard before table recursion, 27 seven-field records per
state, the 351-per-state table lower bound, all-true suffix padding, the
fixed silent halting fallback, its 354-bit regression, and the canonizer
compiled by public `codePrim_machine`. No polynomial complexity is claimed
for that compiler.

## Deleted copies and public replacements

33 originals belong to `CodeParser.lean`; 13 belong to `MathlibBridge.lean`.

| Deleted private | Public replacement | Home |
|---|---|---|
| `zfBReadUnary_append` | `codeReadUnary_append` | `CodeParser.lean` |
| `zfBReadFin` | `codeReadFin` | `CodeParser.lean` |
| `zfBReadSign` | `codeReadSign` | `CodeParser.lean` |
| `zfBReadOutput` | `codeReadOutput` | `CodeParser.lean` |
| `zfBReadWrite` | `codeReadWrite` | `CodeParser.lean` |
| `zfBReadState` | `codeReadState` | `CodeParser.lean` |
| `zfBReadSymbols` | `codeReadSymbols` | `CodeParser.lean` |
| `zfBReadVec` | `codeReadVec` | `CodeParser.lean` |
| `zfBReadFin_append` | `codeReadFin_append` | `CodeParser.lean` |
| `zfBReadSign_append` | `codeReadSign_append` | `CodeParser.lean` |
| `zfBReadOutput_append` | `codeReadOutput_append` | `CodeParser.lean` |
| `zfBReadWrite_append` | `codeReadWrite_append` | `CodeParser.lean` |
| `zfBReadState_append` | `codeReadState_append` | `CodeParser.lean` |
| `zfBReadSymbols_append` | `codeReadSymbols_append` | `CodeParser.lean` |
| `zfBReadVec_append` | `codeReadVec_append` | `CodeParser.lean` |
| `zfBBitsNat_bits` | `codeBitsNat_bits` | `CodeParser.lean` |
| `zfBFlatMap_length` | `codeFlatMap_length` | `CodeParser.lean` |
| `zfBReadUnary_sound` | `codeReadUnary_sound` | `CodeParser.lean` |
| `zfBReadFin_sound` | `codeReadFin_sound` | `CodeParser.lean` |
| `zfBReadSign_sound` | `codeReadSign_sound` | `CodeParser.lean` |
| `zfBReadOutput_sound` | `codeReadOutput_sound` | `CodeParser.lean` |
| `zfBReadWrite_sound` | `codeReadWrite_sound` | `CodeParser.lean` |
| `zfBReadState_sound` | `codeReadState_sound` | `CodeParser.lean` |
| `zfBReadSymbols_sound` | `codeReadSymbols_sound` | `CodeParser.lean` |
| `zfBReadVec_sound` | `codeReadVec_sound` | `CodeParser.lean` |
| `zfBEraseFin` | `codeEraseFin` | `CodeParser.lean` |
| `zfBEraseSign` | `codeEraseSign` | `CodeParser.lean` |
| `zfBEraseOutput` | `codeEraseOutput` | `CodeParser.lean` |
| `zfBEraseWrite` | `codeEraseWrite` | `CodeParser.lean` |
| `zfBEraseState` | `codeEraseState` | `CodeParser.lean` |
| `zfBErase_bind` | `codeErase_bind` | `CodeParser.lean` |
| `zfBEraseSymbols` | `codeEraseSymbols` | `CodeParser.lean` |
| `zfBEraseVec` | `codeEraseVec` | `CodeParser.lean` |
| `zfBPrimUnary` | `codePrimUnary` | `MathlibBridge.lean` |
| `zfBPrimBit` | `codePrimBit` | `MathlibBridge.lean` |
| `zfBPrimBitsNat` | `codePrimBitsNat` | `MathlibBridge.lean` |
| `zfBPrimPair` | `codePrimPair` | `MathlibBridge.lean` |
| `zfBPrimBits` | `codePrimBits` | `MathlibBridge.lean` |
| `zfBPrimSkipPair` | `codePrimSkipPair` | `MathlibBridge.lean` |
| `zfBPrimSkipFin` | `codePrimSkipFin` | `MathlibBridge.lean` |
| `zfBPrimSkipState` | `codePrimSkipState` | `MathlibBridge.lean` |
| `zfBSkipRepeat_iter` | `codeSkipRepeat_iter` | `MathlibBridge.lean` |
| `zfBPrimRepeat` | `codePrimRepeat` | `MathlibBridge.lean` |
| `zfBPrimAll` | `codePrimAll` | `MathlibBridge.lean` |
| `zfBPrimDrop` | `codePrimDrop` | `MathlibBridge.lean` |
| `zfBPrimPrefix` | `codePrimPrefix` | `MathlibBridge.lean` |

## Duplication ledger and surviving helpers

**Ledger line:** `Codes2Tape.lean`: base 9 public / 0 private explicit
declarations; imported ZF-B patch 9 public / 70 private; ZF-B2 removes
46 private copies and adds 0 declarations; final **9 public + 24 private
= 33** explicit declarations. Surviving copied/adapted format-specific
material: **23/33 = 69.70%** (20 retargeted adaptations plus 3 required
format-specific instances). Strict twins under identifier/visibility/
whitespace normalization: **3/33 = 9.09%**. One remaining helper is the
new 354-bit regression. Code-line footprint: **290/356 = 81.46%**
expanded; **23/356 = 6.46%** strict. This does not claim zero
format-specific reuse.

The B2 brief explicitly instructs retention of these 23 instances/adaptations
and assigns their eventual format-parameterized replacement to the
maintainer's 12.2c window. No generalization or shared-ledger edit was made.
The three strict normalized twins are `zfBParse_full`, `zfBCanonical`, and
`zfBCanonical_eq`: their referenced parser/decoder/serialization has the
two-tape meaning. Substituting the one-tape public counterparts changes the
format and is expressly forbidden by the brief. All 46 interchangeable
public-declaration copies have been removed.

The table accounts for every surviving private. The final column gives
the retained share of the one-tape counterpart's proof/body: the exact
longest common subsequence of nonblank, comment-stripped body lines, after
removing whitespace and mapping the ZF-B helper names to their counterparts,
divided by the counterpart's body-line count. For lemmas this is the proof;
for definitions it is the defining body. Types/constants are not retargeted
by this metric. A 100% body overlap does not assert equal declarations or
interchangeable types. The expanded ledger conservatively counts the entire
23 declared adaptations/instances, independent of these textual shares.
`check_delivery.py` and `ledger.json` reproduce all counts and fractions.

| Private | Role | One-tape counterpart | Retained proof/body share |
|---|---|---|---|
| `zfBReadAction` | Read the seven fields and reconstruct both work-tape actions. | `CodeParser.lean` · `codeReadAction` | 6/7 = 85.7% (definition) |
| `zfBFallback` | The one-state, immediately halting, silent two-tape machine. | `CodeParser.lean` · `codeFallback` | 1/1 = 100.0% (definition) |
| `zfBFallback_serialize_length` | Kernel-checked 354-bit fallback serialization regression. | None | New regression |
| `zfBParse` | Canonical header, 351-per-state guard, initial state, table, and padding validation. | `CodeParser.lean` · `codeParse` | 8/11 = 72.7% (definition) |
| `zfBDecode` | Totalize parsing with the halting fallback. | `CodeParser.lean` · `codeDecode` | 1/1 = 100.0% (definition) |
| `zfBReadAction_append` | Exact prefix inverse for ReadAction. | `CodeParser.lean` · `codeReadAction_append` | 7/11 = 63.6% (proof) |
| `zfBAction_length` | Every two-tape action record has at least 13 bits. | `CodeParser.lean` · `codeAction_length` | 14/15 = 93.3% (proof) |
| `zfBTable_length` | Derive the 351-per-state lower bound from 27 records. | `CodeParser.lean` · `codeTable_length` | 11/16 = 68.8% (proof) |
| `zfBReadTable_append` | Recover all 27 transitions per state in the fixed enumeration. | `CodeParser.lean` · `codeReadTable_append` | 2/3 = 66.7% (proof) |
| `zfBParse_serialize_pad` | Exact parser recovery after arbitrary true padding. | `CodeParser.lean` · `codeParse_serialize_pad` | 22/27 = 81.5% (proof) |
| `zfBDecode_serialize_pad` | The total decoder satisfies the required padded round-trip. | `CodeParser.lean` · `codeDecode_serialize_pad` | 2/2 = 100.0% (proof) |
| `zfBReadAction_sound` | Reconstruct the exact consumed prefix for ReadAction. | `CodeParser.lean` · `codeReadAction_sound` | 6/10 = 60.0% (proof) |
| `zfBSkipAction` | Erase the seven-field reader, retaining only the suffix. | `CodeParser.lean` · `codeSkipAction` | 6/6 = 100.0% (definition) |
| `zfBEraseAction` | Identify Action reader suffix erasure with the public skipping operations. | `CodeParser.lean` · `codeEraseAction` | 11/11 = 100.0% (proof) |
| `zfBParseFull` | Parser retaining the decoded machine and unconsumed padding. | `CodeParser.lean` · `codeParseFull` | 8/11 = 72.7% (definition) |
| `zfBScan` | Erased full parser with the same guard and padding test. | `CodeParser.lean` · `codeScan` | 6/8 = 75.0% (definition) |
| `zfBParse_full` | The decoder parser is the first projection of full parsing. | `CodeParser.lean` · `codeParse_full` | 11/11 = 100.0% (proof) |
| `zfBScan_full` | The scanner is the second projection of full parsing. | `CodeParser.lean` · `codeScan_full` | 15/18 = 83.3% (proof) |
| `zfBParseFull_sound` | Reconstruct the exact serialization prefix from successful full parsing. | `CodeParser.lean` · `codeParseFull_sound` | 24/27 = 88.9% (proof) |
| `zfBCanonical` | Return the consumed prefix or fallback serialization. | `CodeParser.lean` · `codeCanonical` | 1/1 = 100.0% (definition) |
| `zfBCanonical_eq` | Identify that prefix function with serialization after total decoding. | `CodeParser.lean` · `codeCanonical_eq` | 10/10 = 100.0% (proof) |
| `zfBPrimSkipAction` | Primitive recursiveness of the seven-field suffix reader. | `MathlibBridge.lean` · `codePrimSkipAction` | 11/12 = 91.7% (proof) |
| `zfBPrimScan` | Assemble primitive recursiveness of the complete erased parser. | `MathlibBridge.lean` · `codePrimScan` | 18/20 = 90.0% (proof) |
| `zfBPrimCanonical` | Assemble primitive recursiveness of the canonizer function. | `MathlibBridge.lean` · `codePrimCanonical` | 2/3 = 66.7% (proof) |

## Verification evidence

- Fresh sweep: **81/81** module checks exit 0, no error diagnostics, and a
  new olean for every module. The 65-entry bootstrap was expanded to its
  current closure, all Build modules, and Codes2Tape; the facade runs last.
- Owned module: exit 0, zero errors, **one** sorry warning at the unchanged
  uniform target. This is a Task-1-complete partial delivery; the full
  batch's zero-sorry gate remains open.
- TuringMachine facade: exit 0, zero errors. Codes2Tape was checked directly,
  since the facade does not import it.
- `style_lint: 0 FAIL, 12 WARN over 45 files`.
- `git diff --check`: pass; bundle verification: pass.
- `freeze.log`: all public statements, retained bodies, deletion-set,
  import, and file-ownership checks pass.

Required axiom prints, followed by the compiled import-availability probe:

```text
'Turing.exists_effectiveMachineCode2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_uniformMachineCode2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
available under Codes2Tape imports: Turing.vhostEmitTM = false
available under Codes2Tape imports: Turing.vhostSilentTM = false
available under Codes2Tape imports: Turing.FinTM.exists_loopTM = false
available under Codes2Tape imports: Turing.FinTM.exists_loopTM_spaceUsed = false
available under Codes2Tape imports: Turing.FinTM.computesFunInTime_pairFst_spaceUsed = false
```

The first target meets the axiom ceiling exactly. The second target is still
admitted and is not reported as proved. No axiom dependency on the ND existence
theorem was introduced.

Final owned-module sweep output:

```text
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:595:8: warning: declaration uses 'sorry'
EXIT Codes2Tape 0
```

Final sweep tail:

```text
EXIT TCSlib.Complexity.ClassNP.ExpPoly 0
CHECK TCSlib.Complexity.ClassNP
EXIT TCSlib.Complexity.ClassNP 0
CHECK TCSlib.Complexity.TuringMachine.Build.VirtualInput
EXIT TCSlib.Complexity.TuringMachine.Build.VirtualInput 0
CHECK TCSlib.Complexity.TuringMachine.Build.Zone
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1001:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1037:8: warning: declaration uses 'sorry'
EXIT TCSlib.Complexity.TuringMachine.Build.Zone 0
CHECK TCSlib.Complexity.TuringMachine
EXIT TCSlib.Complexity.TuringMachine 0
SWEEP_DONE
```

Remaining admissions observed in the required sweep (9 warning
emissions; all listed below):

| File | Declaration | Source line |
|---|---|---:|
| `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean` | `one_work_tape_spaceUsed` | 1014 |
| `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean` | `one_work_tape_binary_spaceUsed` | 1036 |
| `TCSlib/Complexity/TuringMachine/NDCodes.lean` | `exists_effectiveNDMachineCode` | 187 |
| `TCSlib/Complexity/TuringMachine/Codes2Tape.lean` | `exists_uniformMachineCode2` | 595 |
| `TCSlib/Complexity/TuringMachine/CounterProgRun.lean` | `sim_run_of_regs_le` | 343 |
| `TCSlib/Complexity/Formulas/QBF.lean` | `truth_exPrefix_iff_satisfiable` | 119 |
| `TCSlib/Complexity/Formulas/QBFEncoding.lean` | `decode_encode` | 88 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `exists_zoneShiftInTM` | 1001 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `exists_zoneShiftOutTM` | 1037 |

These are the admissions at the recorded checkout; they are not inferred
from the older ZF-B report. The current alphabet-reduction space theorem
is already proved; Zone has only its two shift-machine admissions.

## Requested continuation amendment and shared work

For Task 1, no new shared lemma is requested; the commissioned promotions
were sufficient. The remaining format-specific layer stays with the brief's
12.2c item. For Task 2, sanction only the two imports listed in
`CONTINUATION.md`, then continue the finite simulator construction and
its per-input joint polynomial ledger. The brief's literal prohibition on
additional imports prevented the required reuse route in this delivery.

## Packet and application

The flattened archive includes this report, full owned source, the two
ordered format patches, an incremental bundle, the complete sweep, axiom,
lint, freeze, and bundle logs, the declaration/proof-share ledger,
verification scripts, the exact module order, the import closure, the
continuation report, environment notes, and `SHA256SUMS`.

Apply both patches, in filename order, with `git am -3` on the recorded
base (or perform normal maintainer conflict review on a later branch).
The first patch preserves ZF-B authorship. The incremental bundle requires
the recorded base. Nothing was pushed or submitted as a PR.
