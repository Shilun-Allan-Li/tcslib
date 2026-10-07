# Split A report: Encoding.lean → Encoding / CodeParser / MathlibBridge

Repo: /Users/seyoonr/phd_experiments/tcslib, branch `complexity/arora-barak-ch1`.
Source file at split time: `TCSlib/Complexity/TuringMachine/Encoding.lean`, 2268 lines
(working-tree state = HEAD `2832663b` for this file).

## Cut points (original line ranges → destination)

| Original lines | Content | Destination |
|---|---|---|
| 1–5 | copyright header | replicated in all three files |
| 6–12 | imports | redistributed (see "Final import lists") |
| 13–17 | blank + three `set_option` lines + blank | residual; replicated verbatim in both new files |
| 18–80 | module docstring | residual (edited — see "Module-docstring edits"); new modules got fresh headers |
| 81–82 | blank + `namespace Turing` | residual; `namespace Turing` replicated in both new files |
| 83–440 | pre-fill audited content: `CodeTM` … `EffectiveMachineCode` | residual `Encoding.lean` |
| 441–1175 | `codeReadUnary` (docstring at 441) … `codeCanonical_eq` (ends 1175) | new `CodeParser.lean` (body at lines 48–782 there) |
| 1176 | blank seam line | dropped (seam) |
| 1177–2228 | `codePrimUnary` … `exists_effectiveMachineCode` (ends 2228) | new `MathlibBridge.lean` (body at lines 47–1098 there) |
| 2229 | blank seam line | dropped (seam) |
| 2230–2268 | `exists_codeTM` (docstring at 2230) + `end Turing` | residual `Encoding.lean` (immediately after line 440's blank) |

`end Turing` is replicated at the end of both new files. There were no `open`
statements, no `variable` declarations, no `open … in` prefixes, and the only
`section` (`section Serialize`, lines 348–399) lies entirely inside the residual,
so no scope replication beyond `namespace Turing` was needed.

All moved bodies were verified byte-identical to the original by line-range diff:
the CodeParser body differs from original 441–1175 in exactly the 13 `private `
deletions and 7 inserted docstring lines below; the MathlibBridge body is
byte-identical to original 1177–2228 (zero diff); the residual diff vs HEAD shows
only the import removals, the module-docstring edit, the 8 `private ` deletions,
and the removal of lines 441–2229.

### Note on the cut declaration (clarification, not a deviation in effect)

The task named `private def codeReadWrite` (line 476) as "the first declaration of
the epoch-3A parser layer". Checked against git: the pre-fill audited file
(`1b16fcb8^`, 497 lines) ends its pre-`exists_effectiveMachineCode` content at
`EffectiveMachineCode`; `codeReadUnary`/`codeReadUnary_append`/`codeReadFin`/
`codeReadSign`/`codeReadOutput` (lines 441–475) are also epoch-3A fill content
(added by commit `1b16fcb8`). The task's governing definition ("everything before
it is the pre-fill audited content") and its CodeParser enumeration ("i.e.
codeRead*") both place those declarations in CodeParser, so the cut was made at
line 441 (start of `codeReadUnary`'s docstring), not 476. The residual is thereby
exactly the audited pre-fill content plus `exists_codeTM`, and lands at 481 lines
(≈500 target). No audited declaration moved out of Encoding.lean except as the
task directs (`exists_effectiveMachineCode` to MathlibBridge).

`exists_codeTM` (original 2230–2267) physically sat at the end of the file but is
pre-fill audited content per git; it was returned to the residual as the task
directs. Its dependencies are all pre-3A (CodeTM/StateRenaming/EquivFin), so
elaboration is unaffected — confirmed by the residual's clean check.

## Final line counts

| File | Lines |
|---|---|
| `TCSlib/Complexity/TuringMachine/Encoding.lean` (residual) | 481 |
| `TCSlib/Complexity/TuringMachine/CodeParser.lean` (new) | 790 |
| `TCSlib/Complexity/TuringMachine/MathlibBridge.lean` (new) | 1100 |

## Private → public flips

Every flip is the deletion of the leading `private ` only; nothing else on any
declaration changed.

### Epoch-3A declarations promoted in CodeParser.lean (13) — all required by MathlibBridge.lean

| Declaration | First referencing use in MathlibBridge |
|---|---|
| `codeReadUnary` | `codePrimUnary : Primrec codeReadUnary` |
| `codeBitsNat` | `codePrimBitsNat : Primrec codeBitsNat` |
| `codeFallback` | `codePrimCanonical` (`Primrec.const codeFallback.serialize`) |
| `codeDecode` | `codeCanonical_machine`, `exists_effectiveMachineCode` |
| `codeDecode_serialize_pad` | `exists_effectiveMachineCode` (`decode_encode_pad` field) |
| `codeSkipPair` | `codePrimSkipPair` |
| `codeSkipFin` | `codePrimSkipFin` (incl. `unfold codeSkipFin`) |
| `codeSkipState` | `codePrimSkipState` |
| `codeSkipAction` | `codePrimSkipAction` (incl. `unfold codeSkipAction`) |
| `codeSkipRepeat` | `codeSkipRepeat_iter`, `codePrimRepeat` |
| `codeScan` | `codePrimScan` (incl. `unfold codeScan`), `codePrimCanonical` |
| `codeCanonical` | `codePrimCanonical`, `codeCanonical_machine` |
| `codeCanonical_eq` | `codeCanonical_machine` |

All other 3A declarations keep `private` in their new module (verified: no
cross-module references — e.g. `codeReadFin`, `codeParse`, `codeParseFull`, all
`code*_append`/`code*_sound`/`codeErase*` stay private in CodeParser; all
`codePrim*`/`bridge*` stay private in MathlibBridge).

### Audited-file (pre-3A) privates promoted in residual Encoding.lean (8)

| Declaration | Required by |
|---|---|
| `pairDecode` | CodeParser (`codeParse`, soundness proofs, `pairDecode.induct`) and MathlibBridge (`codePrimPair : Primrec pairDecode`) |
| `pairDecode_pairEncode` | CodeParser (`codeParse_serialize_pad`) |
| `signBits` | CodeParser (`codeReadSign_append`/`_sound`, `codeAction_length`) |
| `optBoolBits` | CodeParser (`codeReadOutput_append`/`_sound`, `codeAction_length`) |
| `optOptBoolBits` | CodeParser (`codeReadWrite_append`/`_sound`, `codeAction_length`) |
| `unaryFin` | CodeParser (`codeReadFin_append`/`_sound`, `codeAction_length`) |
| `optStateBits` | CodeParser (`codeReadState_append`/`_sound`, `codeAction_length`) |
| `actionBits` | CodeParser (`codeReadAction_append`/`_sound`, `codeTable_length`, …) |

Each of these eight already had a docstring whose first sentence states the result
in natural language (statement prose), so none needed a docstring added or
changed. All `pairDiag*` helpers keep `private` (referenced only inside the
residual).

## Docstrings added (7, all in CodeParser.lean, all on newly public declarations that had none)

* `codeSkipFin` — `/-- Skip a range-checked unary index, keeping only the unconsumed suffix. -/`
* `codeSkipState` — `/-- Skip a halt tag or live successor field, keeping only the unconsumed suffix. -/`
* `codeSkipAction` — `/-- Skip one five-field transition record, keeping only the unconsumed suffix. -/`
* `codeSkipRepeat` — `/-- Iterate a skipping reader a fixed number of times, keeping only the final suffix. -/`
* `codeScan` — `/-- The erased parser: accept exactly the strings the parser accepts, returning only the unconsumed all-true suffix. -/`
* `codeCanonical` — `/-- The canonical serialization of the machine a string denotes: the consumed prefix on scanner success, the fallback machine's serialization otherwise. -/`
* `codeCanonical_eq` — `/-- The suffix scanner computes exactly the fixed serialization of the decoded machine. -/`

No existing declaration docstring was reworded (`codeSkipPair` already had one and
keeps it verbatim). No docstrings were needed in the residual or MathlibBridge.

## Module-docstring edits

Residual `Encoding.lean` (comment-only, two edits inside the `/-! -/` header):

1. Removed one bullet from "## Main results":
   `* `Turing.exists_effectiveMachineCode` — a concrete effective scheme exists.`
2. Added a pointer paragraph after the (otherwise verbatim) bullets:
   "The concrete parser/decoder realizing a scheme lives in
   `TCSlib.Complexity.TuringMachine.CodeParser`, and the existence of an effective
   scheme (`Turing.exists_effectiveMachineCode`) is proved in
   `TCSlib.Complexity.TuringMachine.MathlibBridge`."

The two new modules received fresh module docstrings in the prescribed header
shape. MathlibBridge's states, as required: the quarantine of the
`Mathlib.Computability.TMToPartrec` import behind this single module; the
arbitrary-time compiler route for the canonizer (primitive recursiveness →
Mathlib's verified compilation → private in-model simulation `bridgeTM` →
alphabet reduction), with no polynomial bound claimed; and that its architectural
placement is pending human review — AroraBarakChapter1Plan.md §5, open design
question 1.

## Final import lists

`Encoding.lean` (= the pre-fill audited file's exact import list; the fill-added
`Mathlib.Computability.TMToPartrec` and `Mathlib.Data.Fintype.Vector` moved out):
```
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape
```

`CodeParser.lean`:
```
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Encoding
```
(FinRange for the `List.finRange` lemmas in `codeReadVec_append`/`_sound`;
Nat.Bits for `Nat.binaryRec'`/`Nat.bits_append_bit` in `codeBitsNat_bits`.)

`MathlibBridge.lean`:
```
import Mathlib.Computability.TMToPartrec
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.CodeParser
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
```
(TMToPartrec for `PartrecToTM2`/`ToPartrec.Code`/`TM2`/`Primrec`; Fintype.Vector
for the `List.Vector` Fintype instance in `bridge_binary`; Nat.Bits for
`codePrimBits`/`bridgeNumber_bits`; AlphabetReduction for
`FinTM.alphabet_reduction` in `bridge_binary`.)

## Verification

Command per module (dependency order), with the private olean tree
`TCSLIB_OLEANS=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/335c3cc1-5b69-47fb-b05a-5971f617f571/scratchpad/oleans-splitA`
and `bash scripts/lean_check_tree.sh <module>`. No `lake` command was run.

1. `TCSlib/Complexity/TuringMachine/Encoding` — **PASS**, exit 0, zero
   diagnostics. Tail:
   ```
   ENCODING-EXIT:0
   ```
2. `TCSlib/Complexity/TuringMachine/CodeParser` — **PASS**, exit 0; 8
   `linter.unusedSimpArgs` warnings (in the byte-identical moved proofs of
   `codeParse_serialize_pad` and `codePairDecode_sound`), no `error:` lines, no
   sorry warnings. Tail:
   ```
   TCSlib/Complexity/TuringMachine/CodeParser.lean:420:51: warning: This simp argument is unused:
     h₃
   ...
   Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
   CODEPARSER-EXIT:0
   ```
3. `TCSlib/Complexity/TuringMachine/MathlibBridge` — **PASS**, exit 0; 14
   `linter.unusedSimpArgs` warnings (all in byte-identical moved `bridge*`
   proofs), no `error:` lines, no sorry warnings. Tail:
   ```
   TCSlib/Complexity/TuringMachine/MathlibBridge.lean:878:41: warning: This simp argument is unused:
     SignType.coe_zero
   ...
   Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
   MATHLIBBRIDGE-EXIT:0
   ```

Expected `declaration uses 'sorry'` warnings: none — and none appeared.
No module outside these three was checked.

## Cross-file safety check (read-only)

`grep` over `TCSlib/` confirms no Lean code outside these three files references
any moved or newly public declaration; the only mentions of
`exists_effectiveMachineCode` elsewhere are prose in docstrings
(`Universal.lean:311`, `UniversalStartup.lean:282`). Downstream users of
`Encoding` consume only names that remain there (`CodeTM`, `serialize`,
`pairEncode`, `MachineCode`, `EffectiveMachineCode`, `exists_codeTM`, …).

## Files touched

Only:
* `TCSlib/Complexity/TuringMachine/Encoding.lean` (rewritten residual)
* `TCSlib/Complexity/TuringMachine/CodeParser.lean` (new)
* `TCSlib/Complexity/TuringMachine/MathlibBridge.lean` (new)

No facade edit, no `scripts/ab_ch1_module_order.txt` edit, no other file
modified; no git state-changing command was run. (The working tree's
`Universal.lean` modification and the untracked `Universal*.lean` files are a
parallel split task's work, untouched here.)

## Deviations

None in effect. The one departure from the task's literal text is the cut
declaration: `codeReadUnary` (line 441) instead of the named `codeReadWrite`
(line 476), because git shows lines 441–475 are also epoch-3A fill content and
the task's controlling definition ("everything before it is the pre-fill audited
content"; CodeParser = "codeRead*, …") requires the earlier cut. Detailed above
under "Note on the cut declaration".
