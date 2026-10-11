# Item 8 (CH34-D2): machine-code format refactor

Tasks 1 and 2 complete. The source replay, statement freeze, public-axiom comparison,
duplication gates and lint pass. **One required legacy audit program fails identically
at the base and final commits** because it expects an already-proved theorem to
remain admitted; see the verification table. This is not an unconditional pass of
that legacy program.

## Provenance and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib.
- Requested branch: `complexity/arora-barak-ch3-4`.
- Base: `5eb189196b117883a1db198cba87ba35db8e315b`.
- Required ancestor: `c1f9181cea266340e0e699a08d57ef414fd71a1c`; the `git merge-base --is-ancestor` check passed before work.
- Local working branch: `refactor/ch34-t1-codeformat`. No rebase, push, or PR.
- Binding sources read: `briefs/ch34-t1-item8.md`, all three archived Item8 pre-ship probes, `policy.md`, `workflow.md` §4, `AGENTS.md`, the prescribed order list, the C1 bootstrap loop and the copy-text screen.
- Six owned source files only; no blueprint or consumer source edits.

## Changes

Task 1 factors transition records, table formats, the 27-record two-work-tape table, and the one-tape instance into `CodeFormat.lean`. The seven public moves preserve their docstrings and signatures. The five one-tape wrappers use the prescribed term-mode transports. MathlibBridge exposes the generic primitive-recursion layer and canonizer construction; its existing public compiler and effective-scheme theorem remain byte-identical. NDCodes only gains the sanctioned import, loses the two verbatim moved definitions, and gains its prefix-preserving module appendix.

Task 2 replaces Codes2Tape's parser/canonizer copies by its private `twoTapeFormat` instance, retains the typed `zfBDecode` alias, and transports the size and guard facts. Only the designated malformed-code hypothesis changes. The two-tape effective-scheme theorem and conditional uniform-simulator assembly use the shared canonizer. The remaining ZF-B3 declarations are byte-identical.

### Two integration details

1. **Declaration placement.** The primitive-recursive layer and both table-skipper proofs are inserted after `codePrimPrefix`, before `BridgeAlphabet`. The new `CodeFormat.exists_canonizer` is placed immediately after `codePrim_machine`, before `codeCanonical_machine`: its proof requires that compiler, which is declared later than the brief's suggested insertion point. No existing declaration was moved, and every new signature matches the main probe. This is the only placement deviation.
2. **Axiom-preserving proof adjustment.** The archived `codeActionK_length` proof's unrestricted `simp` for the optional-state length introduced `Classical.choice` via generic ordered-addition instances. Consequently the three required public definition wrappers acquired that axiom through the `oneTapeFormat` proof fields. Replacing that one simplifier step by explicit list-length unfolding and `omega` removes the extra dependency. This changes only a new proof body, leaves its probed statement unchanged, and preserves the old public axiom sets. Both the initial diagnostic and the corrected diagnostic are included. No declaration or hypothesis was weakened.

The new CodeFormat file is 575 lines. Each new public declaration has `[AB09, §1.4]` attribution; the prescribed proof sketches are included. Existing moved docstrings are preserved exactly, including those predating the attribution convention. No new `@[simp]` lemma is introduced.

## Freeze, declarations and imports

| File | Base public/private | Delivered public/private |
|---|---:|---:|
| CodeParser | 46 / 16 | 41 / 0 |
| CodeFormat | 0 / 0 | 45 / 3 |
| MathlibBridge | 15 / 62 | 21 / 60 |
| NDCodes | 9 / 0 | 7 / 0 |
| Codes2Tape | 9 / 40 | 9 / 20 |
| TuringMachine facade | 0 / 0 | 0 / 0 |

All counts meet rule 6 exactly. The 123 public declarations are the 79 baseline publics plus 44 additions. The source-union freeze log enumerates every retained declaration, sanctioned body change, move, deletion, and new declaration; new signatures are compared byte-for-byte with the main probe. The CodeFormat structure fields and both instance fields retain the probed contracts.

The only import changes are the four sanctioned ones: CodeFormat imports only CodeParser; MathlibBridge replaces CodeParser by CodeFormat; NDCodes adds CodeFormat; the facade adds CodeFormat and one Contents bullet. Codes2Tape's imports are unchanged.

The effective two-tape scheme uses the ordinary nested structure constructors after obtaining its shared canonizer. This avoids repeating the frozen one-tape scheme's named-field literal, which otherwise creates an unlisted new 50% cross-file screen pair. It does not introduce a helper or copy a proof.

## Duplication

Final screen totals: 117 → 77 directed pairs; 29,824 → 12,563 reproduced characters. All 44 directed CodeParser/Codes2Tape pairs and all seven Codes2Tape/MathlibBridge pairs disappear. Both full outputs and an itemized classification of every new directed pair are supplied.

The additional in-file similarities beyond the brief's list are the two directions of `codePrimSkipTable1`/`codePrimSkipTable2` (67%, 54%; nested applications of the shared `codePrimRepeat` theorem) and `zfB3_decode_length` → `zfB3_decode_states` (50%; generic corollary wrappers and the fixed fallback-length rewrite). They are below 90%; no new unlisted cross-file pair remains.

Codes2Tape adaptations: **23 → 1** (`zfBFallback`, the retained one-line literal). **New copies: none.**

## Verification

| Check | Result | Evidence |
|---|---|---|
| Issued baseline bootstrap | 244/244 modules; zero errors; 84 existing sorry-warning declarations recorded | `evidence/bootstrap.log`, `evidence/sorries-before.log` |
| Task 1 checkpoint | 23/23 modules; zero errors; Codes2Tape unchanged; 23 replay-surface sorry warnings exactly match baseline | `evidence/task1-sweep.log`, `evidence/task1-sorry-compare.log` |
| Final replay | 23/23 modules, Codes2Tape checked directly; zero errors; the same 23 sorry-warning declarations | `evidence/sweep.log`, `evidence/sorry-compare.log` |
| Public axiom prints | 123/123; all 79 pre-existing axiom sets identical; all 44 new publics within the standard triple | `evidence/axioms-before.log`, `evidence/axioms.log`, `evidence/axiom-compare.log` |
| Axiom admissions | `sorryAx` occurs only for the two frozen existence declarations named by the brief | `evidence/axiom-compare.log` |
| Freeze and contracts | All public signatures byte-identical over the six-file union; only sanctioned changes; new probe signatures and structure/instance fields match | `evidence/freeze.log`, `evidence/contracts.log` |
| Duplication | 117 → 77 pairs; 29,824 → 12,563 characters; all targeted cross-file pairs removed | Both copy-text logs and `evidence/duplication-analysis.md` |
| Style lint | `style_lint: 0 FAIL, 14 WARN over 47 files`; all 14 WARNs pre-existing, including MathlibBridge's size WARN | `evidence/lint-before.log`, `evidence/lint.log` |
| `ch1-infra-BuildSpecAxioms` | Exit 0 at base and final; output byte-identical | `evidence/audit-BuildSpec-before.log`, `evidence/audit-BuildSpec.log` |
| `ch1-infra-BridgeExportAxioms` | Exit 1 at base and final; output byte-identical | `evidence/audit-BridgeExport-before.log`, `evidence/audit-BridgeExport.log` |

The BridgeExport program fails at its `run_cmd` (line 59), after finding
`ROOTS Complexity.TMSAT_mem_NP: []`, because its assertion expects
`[Complexity.TMSAT_mem_NP]`. Its printed TMSAT theorem axioms already exclude
`sorryAx` at the base. The program stops at that obsolete assertion; its remaining
assertions are not claimed to pass. Both audit-program sources are untouched.
`evidence/audit-program-comparison.log` records the byte-identical outputs and
exit statuses. Five extra upstream modules were checked solely to load these
programs; their log and order are included.

The old public docstring ending immediately before the new Item-8 paragraph
contains one space before its closing delimiter. That space is deliberately
retained at the new paragraph boundary to preserve the exact prefix; it is the
single `git diff --check` trailing-space diagnostic. There is no code whitespace
error. `evidence/contracts.log` validates this exact exception.

Local commits:

- Task 1: `88a1010c` — shared record/format layer and one-tape refactor.
- Task 2: `13ab0f3f` — two-tape instance and transported consumers.

Every Lean check uses the repository's `scripts/lean_check_tree.sh`; `lake build` was never run. `lake exe cache get` completed successfully at the pinned mathlib revision. Initial environment failures and diagnostic attempts are retained separately from successful sweep logs. Lean's executable-location lookup needed a small `/proc/<pid>/exe` to `/proc/self/exe` compatibility shim because this container exposes different PID namespaces; its source is included. It changes no Lean/kernel code, axioms, compiler options or check script.

The full 244-module baseline bootstrap uses the issued order. The baseline compiled tree was snapshotted before the refactor for the legacy-program comparison; the five extra audit dependencies were added from their checked, unchanged base sources. The final replay order lists the specified 23 modules, including the direct Codes2Tape check; the root `TCSlib` is excluded. Sorry warnings are compared by module and declaration, rather than line number, because the sanctioned moves and deletions change source coordinates.

## Archive

The archive contains this report, the six complete source files, the local commit patch series and bundle against the recorded base, sweep/axiom/freeze/copy-screen/lint evidence and verification programs, and `SHA256SUMS`. Verification scripts and logs do not belong to the six-file repository patch.

## Copy-text screen outputs

Before:

```text
declarations screened: 169; copy pairs (target reproduces >= half of source): 117; reproduced text: 29,824 chars
   Codes2Tape.lean::zfBAction_length  reproduces  CodeParser.lean::codeAction_length: 370/370 = 100%
   NDCodes.lean::EffectiveNDMachineCode  reproduces  Encoding.lean::EffectiveMachineCode: 127/127 = 100%
   NDCodes.lean::EffectiveNDMachineCode  reproduces  Codes2Tape.lean::EffectiveMachineCode2: 127/127 = 100%
   Encoding.lean::EffectiveMachineCode  reproduces  NDCodes.lean::EffectiveNDMachineCode: 127/127 = 100%
   Encoding.lean::EffectiveMachineCode  reproduces  Codes2Tape.lean::EffectiveMachineCode2: 127/127 = 100%
   Codes2Tape.lean::EffectiveMachineCode2  reproduces  NDCodes.lean::EffectiveNDMachineCode: 127/127 = 100%
   Codes2Tape.lean::EffectiveMachineCode2  reproduces  Encoding.lean::EffectiveMachineCode: 127/127 = 100%
   NDCodes.lean::actionBits₂  reproduces  Encoding.lean::actionBits: 119/119 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   CodeParser.lean::codeAction_length  reproduces  Codes2Tape.lean::zfBAction_length: 370/371 = 100%
   MathlibBridge.lean::codePrimBitsNat  reproduces  MathlibBridge.lean::bridgePrimNumber: 128/129 = 99%
   MathlibBridge.lean::bridgePrimNumber  reproduces  MathlibBridge.lean::codePrimBitsNat: 128/129 = 99%
   Codes2Tape.lean::zfBSkipAction  reproduces  CodeParser.lean::codeSkipAction: 155/157 = 99%
   CodeParser.lean::codePairDecode_sound  reproduces  Encoding.lean::eq_pairEncode_of_pairDecode: 656/672 = 98%
   Codes2Tape.lean::zfBParseFull  reproduces  Codes2Tape.lean::zfBParse: 304/312 = 97%
   CodeParser.lean::codeParseFull  reproduces  CodeParser.lean::codeParse: 283/291 = 97%
   Codes2Tape.lean::zfBPrimScan  reproduces  MathlibBridge.lean::codePrimScan: 983/1014 = 97%
   Codes2Tape.lean::zfBScan  reproduces  CodeParser.lean::codeScan: 247/255 = 97%
   Encoding.lean::eq_pairEncode_of_pairDecode  reproduces  CodeParser.lean::codePairDecode_sound: 656/682 = 96%
   Codes2Tape.lean::zfBReadTable_append  reproduces  CodeParser.lean::codeReadTable_append: 109/114 = 96%
   Codes2Tape.lean::zfBParse  reproduces  Codes2Tape.lean::zfBParseFull: 304/319 = 95%
   CodeParser.lean::codeParse  reproduces  CodeParser.lean::codeParseFull: 283/298 = 95%
   Codes2Tape.lean::zfB3_uniform_of_simulator  reproduces  Codes2Tape.lean::exists_effectiveMachineCode2: 278/294 = 95%
   Codes2Tape.lean::zfBParseFull  reproduces  CodeParser.lean::codeParse: 273/291 = 94%
   Codes2Tape.lean::zfBParse  reproduces  CodeParser.lean::codeParse: 273/291 = 94%
   NDCodes.lean::CodeNDTM.serialize  reproduces  Codes2Tape.lean::Code2TM.serialize: 290/310 = 94%
   MathlibBridge.lean::codePrimScan  reproduces  Codes2Tape.lean::zfBPrimScan: 983/1055 = 93%
   Codes2Tape.lean::zfBParseFull_sound  reproduces  CodeParser.lean::codeParseFull_sound: 646/698 = 93%
   Codes2Tape.lean::zfBEraseAction  reproduces  CodeParser.lean::codeEraseAction: 351/381 = 92%
   Codes2Tape.lean::zfBParseFull  reproduces  CodeParser.lean::codeParseFull: 274/298 = 92%
   CodeParser.lean::codeParse_sound  reproduces  CodeParser.lean::codeParseFull_sound: 640/698 = 92%
   Codes2Tape.lean::zfBParse  reproduces  CodeParser.lean::codeParseFull: 273/298 = 92%
   Codes2Tape.lean::zfBScan_full  reproduces  CodeParser.lean::codeScan_full: 660/723 = 91%
   CodeParser.lean::codeScan  reproduces  Codes2Tape.lean::zfBScan: 247/272 = 91%
   CodeParser.lean::codeParse_full  reproduces  Codes2Tape.lean::zfBParse_full: 225/248 = 91%
   Codes2Tape.lean::zfBParse_full  reproduces  CodeParser.lean::codeParse_full: 225/250 = 90%
   CodeParser.lean::codeParse_serialize_pad  reproduces  Codes2Tape.lean::zfBParse_serialize_pad: 527/588 = 90%
   Codes2Tape.lean::zfBPrimSkipAction  reproduces  MathlibBridge.lean::codePrimSkipAction: 413/462 = 89%
   MathlibBridge.lean::bridgeCfg_push  reproduces  MathlibBridge.lean::bridgeCfg_pop: 674/761 = 89%
   CodeParser.lean::codeScan_full  reproduces  Codes2Tape.lean::zfBScan_full: 660/752 = 88%
   Codes2Tape.lean::zfBReadAction  reproduces  CodeParser.lean::codeReadAction: 148/169 = 88%
   CodeParser.lean::codeParseFull  reproduces  Codes2Tape.lean::zfBParse: 273/312 = 88%
   CodeParser.lean::codeParse  reproduces  Codes2Tape.lean::zfBParse: 273/312 = 88%
   CodeParser.lean::codeParseFull_sound  reproduces  Codes2Tape.lean::zfBParseFull_sound: 646/740 = 87%
   CodeParser.lean::codeParseFull_sound  reproduces  CodeParser.lean::codeParse_sound: 640/742 = 86%
   CodeParser.lean::codeParseFull  reproduces  Codes2Tape.lean::zfBParseFull: 274/319 = 86%
   CodeParser.lean::codeParse  reproduces  Codes2Tape.lean::zfBParseFull: 273/319 = 86%
   NDCodes.lean::NDMachineCode  reproduces  Encoding.lean::MachineCode: 93/109 = 85%
   Codes2Tape.lean::MachineCode2  reproduces  Encoding.lean::MachineCode: 93/109 = 85%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   NDCodes.lean::NDMachineCode  reproduces  Codes2Tape.lean::MachineCode2: 93/111 = 84%
   Encoding.lean::MachineCode  reproduces  Codes2Tape.lean::MachineCode2: 93/111 = 84%
   Codes2Tape.lean::Code2TM.serialize  reproduces  NDCodes.lean::CodeNDTM.serialize: 290/348 = 83%
   Encoding.lean::MachineCode  reproduces  NDCodes.lean::NDMachineCode: 93/113 = 82%
   Codes2Tape.lean::MachineCode2  reproduces  NDCodes.lean::NDMachineCode: 93/113 = 82%
   NDCodes.lean::CodeNDTM.serialize  reproduces  Encoding.lean::CodeTM.serialize: 209/254 = 82%
   Codes2Tape.lean::Code2TM.serialize  reproduces  Encoding.lean::CodeTM.serialize: 209/254 = 82%
   Codes2Tape.lean::zfBParse_serialize_pad  reproduces  CodeParser.lean::codeParse_serialize_pad: 527/653 = 81%
   CodeParser.lean::codeParse_sound  reproduces  Codes2Tape.lean::zfBParseFull_sound: 583/740 = 79%
   Codes2Tape.lean::zfBParseFull_sound  reproduces  CodeParser.lean::codeParse_sound: 583/742 = 79%
   Codes2Tape.lean::zfBTable_length  reproduces  CodeParser.lean::codeTable_length: 442/568 = 78%
   MathlibBridge.lean::bridgeCfg_pop  reproduces  MathlibBridge.lean::bridgeCfg_push: 674/871 = 77%
   MathlibBridge.lean::bridgeCfg_push_input  reproduces  MathlibBridge.lean::bridgeCfg_pop_emit: 195/259 = 75%
   CodeParser.lean::codeReadTable_append  reproduces  Codes2Tape.lean::zfBReadTable_append: 109/148 = 74%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadWrite_sound: 143/195 = 73%
   MathlibBridge.lean::codePrimScan  reproduces  MathlibBridge.lean::codePrimSkipFin: 188/257 = 73%
   Codes2Tape.lean::zfBPrimScan  reproduces  MathlibBridge.lean::codePrimSkipFin: 188/257 = 73%
   Codes2Tape.lean::zfBScan_full  reproduces  Codes2Tape.lean::zfBParse_full: 181/248 = 73%
   CodeParser.lean::codeEraseAction  reproduces  Codes2Tape.lean::zfBEraseAction: 351/482 = 73%
   CodeParser.lean::codeScan_full  reproduces  CodeParser.lean::codeParse_full: 182/250 = 73%
   CodeParser.lean::codeScan_full  reproduces  Codes2Tape.lean::zfBParse_full: 177/248 = 71%
   Codes2Tape.lean::zfBScan_full  reproduces  CodeParser.lean::codeParse_full: 177/250 = 71%
   CodeParser.lean::codeReadAction_append  reproduces  Codes2Tape.lean::zfBReadAction_append: 141/201 = 70%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadSign_sound: 159/227 = 70%
   CodeParser.lean::codeSkipAction  reproduces  Codes2Tape.lean::zfBSkipAction: 155/224 = 69%
   CodeParser.lean::codeReadSign_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 159/233 = 68%
   Codes2Tape.lean::zfBReadAction_sound  reproduces  CodeParser.lean::codeReadAction_sound: 257/378 = 68%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimUnary: 367/542 = 68%
   Encoding.lean::CodeTM.serialize  reproduces  Codes2Tape.lean::Code2TM.serialize: 209/310 = 67%
   Encoding.lean::actionBits  reproduces  NDCodes.lean::actionBits₂: 119/177 = 67%
   MathlibBridge.lean::codePrimSkipAction  reproduces  Codes2Tape.lean::zfBPrimSkipAction: 413/647 = 64%
   MathlibBridge.lean::codePrimCanonical  reproduces  Codes2Tape.lean::zfBPrimCanonical: 88/138 = 64%
   CodeParser.lean::codeCanonical_eq  reproduces  Codes2Tape.lean::zfBCanonical_eq: 125/197 = 63%
   Codes2Tape.lean::zfBPrimCanonical  reproduces  MathlibBridge.lean::codePrimCanonical: 88/140 = 63%
   Codes2Tape.lean::zfBReadAction_append  reproduces  CodeParser.lean::codeReadAction_append: 141/225 = 63%
   CodeParser.lean::codeReadWrite_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 143/233 = 61%
   CodeParser.lean::codeReadAction  reproduces  Codes2Tape.lean::zfBReadAction: 148/244 = 61%
   Encoding.lean::CodeTM.serialize  reproduces  NDCodes.lean::CodeNDTM.serialize: 209/348 = 60%
   MathlibBridge.lean::bridgeCfg_pop_emit  reproduces  MathlibBridge.lean::bridgeCfg_push_input: 195/327 = 60%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipState: 215/361 = 60%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeParser.lean::codeReadSymbols_sound: 142/239 = 59%
   CodeParser.lean::codeReadWrite  reproduces  CodeParser.lean::codeReadOutput: 65/110 = 59%
   Codes2Tape.lean::zfBCanonical_eq  reproduces  CodeParser.lean::codeCanonical_eq: 125/212 = 59%
   CodeParser.lean::codeParseFull  reproduces  CodeParser.lean::codeScan: 146/255 = 57%
   CodeParser.lean::codeParse  reproduces  CodeParser.lean::codeScan: 146/255 = 57%
   CodeParser.lean::codeReadState_sound  reproduces  CodeParser.lean::codeReadUnary_sound: 223/390 = 57%
   Codes2Tape.lean::zfBParseFull  reproduces  CodeParser.lean::codeScan: 145/255 = 57%
   Codes2Tape.lean::zfBParse  reproduces  CodeParser.lean::codeScan: 145/255 = 57%
   MathlibBridge.lean::bridge_back  reproduces  MathlibBridge.lean::bridge_scan: 422/747 = 56%
   CodeParser.lean::codeReadAction_sound  reproduces  Codes2Tape.lean::zfBReadAction_sound: 257/463 = 56%
   Codes2Tape.lean::zfB3Answer_malformed  reproduces  Codes2Tape.lean::zfB3Answer_zero: 68/124 = 55%
   Codes2Tape.lean::zfBParseFull  reproduces  Codes2Tape.lean::zfBScan: 147/272 = 54%
   Codes2Tape.lean::zfBParse  reproduces  Codes2Tape.lean::zfBScan: 147/272 = 54%
   CodeParser.lean::codeParseFull  reproduces  Codes2Tape.lean::zfBScan: 145/272 = 53%
   CodeParser.lean::codeParse  reproduces  Codes2Tape.lean::zfBScan: 145/272 = 53%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   Codes2Tape.lean::zfBEraseAction  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeParser.lean::codeEraseVec  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeParser.lean::codeEraseAction  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeParser.lean::codeReadUnary_sound  reproduces  CodeParser.lean::codeReadState_sound: 223/439 = 51%
   CodeParser.lean::codeScan  reproduces  CodeParser.lean::codeParse: 146/291 = 50%
```

After:

```text
declarations screened: 169; copy pairs (target reproduces >= half of source): 77; reproduced text: 12,563 chars
   NDCodes.lean::EffectiveNDMachineCode  reproduces  Encoding.lean::EffectiveMachineCode: 127/127 = 100%
   NDCodes.lean::EffectiveNDMachineCode  reproduces  Codes2Tape.lean::EffectiveMachineCode2: 127/127 = 100%
   Encoding.lean::EffectiveMachineCode  reproduces  NDCodes.lean::EffectiveNDMachineCode: 127/127 = 100%
   Encoding.lean::EffectiveMachineCode  reproduces  Codes2Tape.lean::EffectiveMachineCode2: 127/127 = 100%
   Codes2Tape.lean::EffectiveMachineCode2  reproduces  NDCodes.lean::EffectiveNDMachineCode: 127/127 = 100%
   Codes2Tape.lean::EffectiveMachineCode2  reproduces  Encoding.lean::EffectiveMachineCode: 127/127 = 100%
   CodeFormat.lean::actionBits₂  reproduces  Encoding.lean::actionBits: 119/119 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   CodeParser.lean::codeEraseWrite  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseSign  reproduces  CodeParser.lean::codeEraseOutput: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseWrite: 92/92 = 100%
   CodeParser.lean::codeEraseOutput  reproduces  CodeParser.lean::codeEraseSign: 92/92 = 100%
   MathlibBridge.lean::codePrimBitsNat  reproduces  MathlibBridge.lean::bridgePrimNumber: 128/129 = 99%
   MathlibBridge.lean::bridgePrimNumber  reproduces  MathlibBridge.lean::codePrimBitsNat: 128/129 = 99%
   NDCodes.lean::CodeNDTM.serialize  reproduces  Codes2Tape.lean::Code2TM.serialize: 290/310 = 94%
   CodeFormat.lean::oneTapeFormat  reproduces  CodeFormat.lean::codeTable2Bits: 208/234 = 89%
   MathlibBridge.lean::bridgeCfg_push  reproduces  MathlibBridge.lean::bridgeCfg_pop: 674/761 = 89%
   NDCodes.lean::CodeNDTM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 206/234 = 88%
   Codes2Tape.lean::Code2TM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 206/234 = 88%
   NDCodes.lean::NDMachineCode  reproduces  Encoding.lean::MachineCode: 93/109 = 85%
   Codes2Tape.lean::MachineCode2  reproduces  Encoding.lean::MachineCode: 93/109 = 85%
   CodeParser.lean::codeSkipAction  reproduces  CodeFormat.lean::codeSkipActionK: 106/125 = 85%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   NDCodes.lean::NDMachineCode  reproduces  Codes2Tape.lean::MachineCode2: 93/111 = 84%
   Encoding.lean::MachineCode  reproduces  Codes2Tape.lean::MachineCode2: 93/111 = 84%
   Codes2Tape.lean::Code2TM.serialize  reproduces  NDCodes.lean::CodeNDTM.serialize: 290/348 = 83%
   Encoding.lean::MachineCode  reproduces  NDCodes.lean::NDMachineCode: 93/113 = 82%
   Codes2Tape.lean::MachineCode2  reproduces  NDCodes.lean::NDMachineCode: 93/113 = 82%
   NDCodes.lean::CodeNDTM.serialize  reproduces  Encoding.lean::CodeTM.serialize: 209/254 = 82%
   Codes2Tape.lean::Code2TM.serialize  reproduces  Encoding.lean::CodeTM.serialize: 209/254 = 82%
   CodeFormat.lean::actionBitsK  reproduces  Encoding.lean::actionBits: 93/119 = 78%
   MathlibBridge.lean::bridgeCfg_pop  reproduces  MathlibBridge.lean::bridgeCfg_push: 674/871 = 77%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeFormat.lean::codeEraseWork: 167/216 = 77%
   MathlibBridge.lean::bridgeCfg_push_input  reproduces  MathlibBridge.lean::bridgeCfg_pop_emit: 195/259 = 75%
   CodeFormat.lean::parseFull  reproduces  CodeFormat.lean::scan: 151/202 = 75%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadWrite_sound: 143/195 = 73%
   MathlibBridge.lean::CodeFormat.primrec_scan  reproduces  MathlibBridge.lean::codePrimSkipFin: 188/257 = 73%
   CodeParser.lean::codeReadOutput_sound  reproduces  CodeParser.lean::codeReadSign_sound: 159/227 = 70%
   CodeParser.lean::codeReadSign_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 159/233 = 68%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimUnary: 367/542 = 68%
   CodeFormat.lean::codeSkipActionK  reproduces  CodeParser.lean::codeSkipAction: 106/157 = 68%
   Encoding.lean::CodeTM.serialize  reproduces  Codes2Tape.lean::Code2TM.serialize: 209/310 = 67%
   Encoding.lean::actionBits  reproduces  CodeFormat.lean::actionBits₂: 119/177 = 67%
   MathlibBridge.lean::codePrimSkipTable1  reproduces  MathlibBridge.lean::codePrimSkipTable2: 135/201 = 67%
   CodeFormat.lean::codeTable2Bits  reproduces  Codes2Tape.lean::Code2TM.serialize: 206/310 = 66%
   CodeFormat.lean::scan  reproduces  CodeFormat.lean::parseFull: 151/234 = 65%
   CodeFormat.lean::oneTapeFormat  reproduces  Codes2Tape.lean::Code2TM.serialize: 192/310 = 62%
   Encoding.lean::actionBits  reproduces  CodeFormat.lean::actionBitsK: 93/151 = 62%
   CodeFormat.lean::actionBits₂  reproduces  CodeFormat.lean::actionBitsK: 93/151 = 62%
   CodeParser.lean::codeReadWrite_sound  reproduces  CodeParser.lean::codeReadOutput_sound: 143/233 = 61%
   Encoding.lean::CodeTM.serialize  reproduces  NDCodes.lean::CodeNDTM.serialize: 209/348 = 60%
   MathlibBridge.lean::bridgeCfg_pop_emit  reproduces  MathlibBridge.lean::bridgeCfg_push_input: 195/327 = 60%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipState: 215/361 = 60%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeParser.lean::codeReadSymbols_sound: 142/239 = 59%
   CodeFormat.lean::codeTable2Bits  reproduces  NDCodes.lean::CodeNDTM.serialize: 206/348 = 59%
   CodeParser.lean::codeReadWrite  reproduces  CodeParser.lean::codeReadOutput: 65/110 = 59%
   Codes2Tape.lean::zfB3_uniform_of_simulator  reproduces  Codes2Tape.lean::exists_effectiveMachineCode2: 85/144 = 59%
   CodeFormat.lean::oneTapeFormat  reproduces  Encoding.lean::CodeTM.serialize: 147/254 = 58%
   Encoding.lean::CodeTM.serialize  reproduces  CodeFormat.lean::codeTable2Bits: 134/234 = 57%
   CodeParser.lean::codeReadState_sound  reproduces  CodeParser.lean::codeReadUnary_sound: 223/390 = 57%
   MathlibBridge.lean::bridge_back  reproduces  MathlibBridge.lean::bridge_scan: 422/747 = 56%
   CodeFormat.lean::oneTapeFormat  reproduces  NDCodes.lean::CodeNDTM.serialize: 192/348 = 55%
   Codes2Tape.lean::zfB3Answer_malformed  reproduces  Codes2Tape.lean::zfB3Answer_zero: 68/124 = 55%
   MathlibBridge.lean::codePrimSkipTable2  reproduces  MathlibBridge.lean::codePrimSkipTable1: 135/249 = 54%
   CodeFormat.lean::codeTable2Bits  reproduces  Encoding.lean::CodeTM.serialize: 134/254 = 53%
   CodeFormat.lean::actionBitsK  reproduces  CodeFormat.lean::actionBits₂: 93/177 = 53%
   CodeParser.lean::codeReadVec_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 127/242 = 52%
   CodeParser.lean::codeEraseVec  reproduces  CodeFormat.lean::codeEraseWork: 113/216 = 52%
   CodeFormat.lean::codeReadActionK_sound  reproduces  CodeFormat.lean::codeReadWork_sound: 126/242 = 52%
   MathlibBridge.lean::codePrimSkipPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   MathlibBridge.lean::codePrimPair  reproduces  MathlibBridge.lean::codePrimSkipFin: 132/257 = 51%
   CodeParser.lean::codeEraseVec  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseWork  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeFormat.lean::codeEraseActionK  reproduces  CodeParser.lean::codeEraseSymbols: 60/118 = 51%
   CodeParser.lean::codeReadUnary_sound  reproduces  CodeParser.lean::codeReadState_sound: 223/439 = 51%
   Codes2Tape.lean::zfB3_decode_length  reproduces  Codes2Tape.lean::zfB3_decode_states: 79/158 = 50%
```
