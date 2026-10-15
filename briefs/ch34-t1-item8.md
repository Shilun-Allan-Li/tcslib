# 12.2c tranche T1 — Item 8 (CH34-D2): the format-parameterized machine-code parse layer (new `CodeFormat.lean` + `CodeParser` + `MathlibBridge` + `NDCodes` + `Codes2Tape`)

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib` and check out branch
  **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor c1f9181cea266340e0e699a08d57ef414fd71a1c HEAD` succeeds. That
  commit archives the pre-ship probes cited below and the order list. If the
  check fails, **stop**.
- Create a working branch (suggested: `refactor/ch34-t1-codeformat`). Record the
  base commit hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push**: `ch34-t1-codeformat.zip` with `REPORT.md`,
  the full modified sources (new file included), a `git format-patch` series
  against your base, a bundle, the sweep, axiom and freeze logs, both copy-text
  screens, and `SHA256SUMS`.
- Integration (no action for you): side branch, a PR for the user's merge, and a
  separate audit gate.

## What this is

A 12.2c refactor discharging the **human-acknowledged debt CH34-D2**: `backlog.md`
§1, the Codes2Tape row of `audits/duplication-ledger.md`, and plan §4d, 12.2c
item 8.

After ZF-B2, **23 privates of `Codes2Tape.lean` are two-tape adaptations of the
one-tape top layer**: 20 of `CodeParser.lean` and 3 of `MathlibBridge.lean`. They
cover the record reader, table, parse, decode, scan and canonize, and their laws.
`NDCodes`' group-C fill would need a third copy.

You build the layer once, in three levels. **Level T** is a structure
`Turing.CodeFormat` over the *table* grammar (the formats differ in nesting depth,
and the ND table puts the choice bit outermost). **Level R** is a record reader
generic in the work-tape count `k`, via `codeReadVec` over `Action.workTapes`.
**Level W** is the shared 27-record two-work-tape table.

The one-tape and two-tape formats become instances. **The ND instance is not in
this batch**; it is `NDCodes`' group-C fill. **Zero `error:`, and no `sorry`
beyond the base's, after every commit.**

**Pre-ship checks** (maintainer, executed with `lean`, no .olean written; each 0
errors and 0 warnings):

- **`audits/evidence/ch34-t1/Item8PreShip.lean.txt`** imports `Codes2Tape`: every
  Level R/T/W declaration under its final name, both instances, the generic primrec
  layer and the transports D7a–D11; all 18 `#print axioms` within the triple.
- **`audits/evidence/ch34-t1/Item8MovePreShip.lean.txt`** imports only `CodeParser`
  and `Nondeterministic`: `workPair`/`actionBits₂` moved verbatim, the bridge,
  `NDCodes`' remainder, `Code2TM.serialize` and the 354-bit regression.
- **`audits/evidence/ch34-t1/Item8ContextPreShip.lean.txt`**: the `CodeFormat.lean`
  content under its single import, `CodeParser`.

**The main probe is the statement contract.** Every declaration it defines under
a final name must land with exactly that signature and statement. Its proofs are
working references; you may restructure them. The probe-only names are
`probeDecode`, `probeDecode2`, `probeFallback2`,
`probeFallback2_serialize_length`, `codePrimSkipAction'`, `probe_*` and the
`example`s. Read `policy.md` and `workflow.md` §4.

## Owned files (lines at the issue commit)

| File | Change |
|---|---|
| **new** `TuringMachine/CodeFormat.lean` | Import `TCSlib.Complexity.TuringMachine.CodeParser` **only**. Contents: Levels R, T and W; the moved `workPair` and `actionBits₂`; the one-tape instance; the 5 moved one-tape publics. At most 600 lines. |
| `TuringMachine/CodeParser.lean` | Delete 16 privates; move 5 publics out. |
| `TuringMachine/MathlibBridge.lean` | Swap the import `CodeParser` → `CodeFormat`; add the generic primrec layer; delete 3 privates; turn `codeCanonical_machine` into a wrapper. |
| `TuringMachine/NDCodes.lean` | **Sanctioned move**: `workPair` (l. 98–101) and `actionBits₂` (l. 103–110) leave verbatim; add `import …CodeFormat`. Nothing else changes. |
| `TuringMachine/Codes2Tape.lean` | Delete 21 privates; add the private `twoTapeFormat`; retarget ZF-B3; change one public proof. |
| `TuringMachine.lean` (facade) | Add `import …CodeFormat` and one `## Contents` bullet. |

## Design (binding; the statements are in the main probe)

**Level R**, in `CodeFormat`, public: the definitions `actionBitsK`,
`codeReadWork`, `codeReadActionK`, `codeSkipWork`, `codeSkipActionK`; the laws
`codeReadWork_append`, `codeReadActionK_append`, `codeReadWork_sound`,
`codeReadActionK_sound`, `codeEraseWork`, `codeEraseActionK` and
`codeActionK_length : 4 * k + 5 ≤ (actionBitsK a).length`; the moved `workPair`
and `actionBits₂` (byte-identical, docstrings included); and the bridges
`actionBits_eq_actionBitsK`, `actionBits₂_eq_actionBitsK` and
`codeSkipAction_eq_codeSkipActionK : codeSkipAction n xs = codeSkipActionK 1 n xs`.
Private: `codeReadActionK_one_append`, `codeReadActionK_one_sound`,
`codeEraseActionK_one`.

**Level T**, in `CodeFormat`, public. The structure, as probed:

```lean
structure CodeFormat where
  Code : Type
  Table : ℕ → Type
  numStates : Code → ℕ
  assemble : (n : ℕ) → Fin (n + 1) → Table n → Code
  serialize : Code → List Bool
  tableBits : {n : ℕ} → Table n → List Bool
  readTable : (n : ℕ) → List Bool → Option (Table n × List Bool)
  skipTable : ℕ → List Bool → Option (List Bool)
  guard : ℕ
  fallback : Code
  numStates_assemble : ∀ n q t, numStates (assemble n q t) = n
  serialize_assemble : ∀ n q (t : Table n),
    serialize (assemble n q t) = pairEncode n.bits (unaryFin q ++ tableBits t)
  assemble_surj : ∀ M, ∃ n q t, assemble n q t = M
  readTable_append : ∀ n (t : Table n) xs, readTable n (tableBits t ++ xs) = some (t, xs)
  readTable_sound : ∀ n xs (t : Table n) rest,
    readTable n xs = some (t, rest) → xs = tableBits t ++ rest
  readTable_erase : ∀ n xs, (readTable n xs).map Prod.snd = skipTable n xs
  tableBits_length : ∀ n (t : Table n), guard * (n + 1) ≤ (tableBits t).length
```

Definitions: `CodeFormat.parseFull`, `scan`, `canonical`, and
`decode := ((F.parseFull xs).map Prod.fst).getD F.fallback` (so no `parse_full`).
Theorems: `parseFull_serialize_pad`, `decode_serialize_pad`, `parseFull_sound`,
`scan_full`, `canonical_eq`. B5-facing corollaries: `serialize_decode_length_le`,
`numStates_decode_le`, `decode_of_parseFull_none`, `decode_of_guard_lt`.

**Level W**, in `CodeFormat`, public: `CodeTable2` (an `abbrev`),
`codeTable2Bits`, `codeReadTable2`, `codeSkipTable2`, and the laws
`codeReadTable2_append`, `codeReadTable2_sound`, `codeEraseTable2`,
`codeTable2Bits_length` (351).

**`oneTapeFormat`**, in `CodeFormat`, public, fields exactly as probed:
`serialize := CodeTM.serialize`; `tableBits` is the nested flatMap over the
frozen `actionBits`, so `serialize_assemble` is `rfl`; `readTable` uses
`codeReadActionK 1 n`; `skipTable` uses **the frozen public `codeSkipAction`**,
which keeps the new `codeScan` definitionally the old one; `guard := 81`;
`fallback := codeFallback`.

**MathlibBridge.** Public: `codePrimSkipWork`, `codePrimSkipActionK`,
`CodeFormat.primrec_scan`, `CodeFormat.primrec_canonical`,
`CodeFormat.exists_canonizer`, `codePrimSkipTable2`. Private:
`codePrimSkipTable1 : Primrec₂ oneTapeFormat.skipTable`, built from
`codePrimSkipActionK 1` and the `codeSkipAction` bridge.

**Codes2Tape**, private: `twoTapeFormat`, with fields as probed except
`fallback := zfBFallback`; declare it after `zfBFallback`.

No new lemma carries `@[simp]`. Every public declaration gets a docstring with
`[AB09, §1.4]` attribution. `parseFull_serialize_pad`, `parseFull_sound`,
`scan_full` and `codeTable2Bits_length` each carry a "Proof sketch", adapted
from the deleted originals'.

## Tasks

**Task 1 — the layer and the one-tape side** (CodeFormat, CodeParser, NDCodes,
MathlibBridge, facade).

1. Create `CodeFormat.lean`. Order: a header with `CodeParser`'s `set_option`s;
   Level R; the moved definitions; the bridges; Level T; Level W; the private
   corollaries; `oneTapeFormat`; the moved one-tape publics.
2. In NDCodes, delete the two moved definitions and add the import.
3. In CodeParser, delete the 16 privates and the 5 moved publics.
4. In MathlibBridge, put the generic layer and `codePrimSkipTable1/2` where
   `codePrimCanonical` stood (after `codePrimPrefix`, before `BridgeAlphabet`).
   Delete `codePrimSkipAction` (l. 178), `codePrimScan` (230) and
   `codePrimCanonical` (269). Re-prove the private `codeCanonical_machine` (1078)
   as `oneTapeFormat.exists_canonizer codePrimSkipTable1` (D10). Its statement is
   unchanged, so `exists_effectiveMachineCode` stays **byte-identical**.
5. **Checkpoint**: replay, freeze, axioms. Codes2Tape must still elaborate
   unchanged, reaching the moved definitions through NDCodes → CodeFormat. A
   Task-1-complete partial delivery is acceptable.

**Task 2 — the two-tape side** (Codes2Tape).

1. Add `twoTapeFormat`. Keep `zfBDecode` as the typed alias
   `private def zfBDecode (xs : List Bool) : Code2TM := twoTapeFormat.decode xs`,
   so every ZF-B3 statement that mentions it stays byte-identical.
2. Delete the 21 privates.
3. Re-prove `zfB3_decode_length`, `zfB3_decode_states` and `zfB3_guard_failure`
   by instantiation, statements unchanged
   (`change … at h; rwa [zfBFallback_serialize_length] at h`, D9). In
   `zfB3Answer_malformed` the hypothesis becomes
   `(hparse : twoTapeFormat.parseFull α = none)` and `hd` becomes
   `twoTapeFormat.decode_of_parseFull_none α hparse`.
4. Re-prove `zfB3_uniform_of_simulator` and `exists_effectiveMachineCode2` via
   `twoTapeFormat.exists_canonizer codePrimSkipTable2`, with
   `decode_encode_pad := twoTapeFormat.decode_serialize_pad` (D11). Every other
   ZF-B3 private stays byte-identical.

**Priority on exhaustion:** Task 1, then Task 2; partial means Task 2 unstarted,
never an admission.

## Ground rules (binding)

1. **Ownership**: exactly the six files above.
2. **Statement freeze.** Every public declaration of the six files keeps its
   signature, statement, docstring and proof byte-identical, except:
   - **(a) Moved**, chunk otherwise unchanged: `workPair` and `actionBits₂`
     (NDCodes → CodeFormat); `codeDecode`, `codeDecode_serialize_pad`, `codeScan`,
     `codeCanonical` and `codeCanonical_eq` (CodeParser → CodeFormat).
   - **(b) Definition bodies:** `codeDecode`, `codeScan` and `codeCanonical`
     become `oneTapeFormat.decode/scan/canonical xs`.
   - **(c) Proof bodies:** `codeDecode_serialize_pad` and `codeCanonical_eq`
     become `oneTapeFormat.decode_serialize_pad M m` and
     `oneTapeFormat.canonical_eq xs`; `exists_effectiveMachineCode2` (Task 2).
   - **(d) Flagged, prefix-preserving "Item-8 appendix" paragraphs**, on
     `exists_effectiveMachineCode2`'s docstring (its ZF-B appendix stays) and on
     the module docstrings of CodeParser, MathlibBridge, NDCodes and Codes2Tape.
   - **(e)** Codes2Tape's section comment `/-! ### Private parser and canonizer
     implementation (ZF-B) … -/` (l. 151–162) may be rewritten. **(f)** The only
     private statement change is `zfB3Answer_malformed`'s hypothesis.

   Everything else stays byte-identical, in particular `codeFallback`,
   `codeSkipAction`, `exists_effectiveMachineCode`, and every NDCodes statement.
   The freeze comparison runs over the **union of the six files**, since names
   move between files.
3. **Transports are term-mode.** Derive per-format facts from generic ones by
   `exact`/application, or `change`/`show` first. `rw`/`simp` with a generic
   lemma on a per-format term matches syntactically and fails (probed:
   D7a/c/e, D9–D11).
4. **Deletions (exact).**
   - **CodeParser:** `codeReadAction`, `codeParse`, `codeReadAction_append`,
     `codeAction_length`, `codeTable_length`, `codeReadTable_append`,
     `codeParse_serialize_pad`, `codePairDecode_sound` (twins the public
     `eq_pairEncode_of_pairDecode`; cite that instead), `codeReadAction_sound`,
     `codeAllTrue_eq` and `codeParse_sound` (both dead), `codeEraseAction`,
     `codeParseFull`, `codeParse_full`, `codeScan_full`, `codeParseFull_sound`.
   - **MathlibBridge:** the three listed in Task 1.
   - **Codes2Tape:** `zfBReadAction`, `zfBParse`, `zfBReadAction_append`,
     `zfBAction_length`, `zfBTable_length`, `zfBReadTable_append`,
     `zfBParse_serialize_pad`, `zfBDecode_serialize_pad`, `zfBReadAction_sound`,
     `zfBSkipAction`, `zfBEraseAction`, `zfBParseFull`, `zfBScan`,
     `zfBParse_full`, `zfBScan_full`, `zfBParseFull_sound`, `zfBCanonical`,
     `zfBCanonical_eq`, `zfBPrimSkipAction`, `zfBPrimScan`, `zfBPrimCanonical`.
   - **Kept:** `zfBFallback`, `zfBFallback_serialize_length`, and `zfBDecode`
     (as the alias).
5. **Imports**: exactly the four changes in the table; Codes2Tape's imports are
   unchanged. No cycle can arise: CodeFormat's upstream is CodeParser's plus
   itself, and none of its importers is upstream of CodeParser.
6. **Counts** (public/private, base → target; justify any deviation): CodeParser
   46/16 → 41/0; CodeFormat → 45 (38 new + 7 moved)/3; MathlibBridge 15/62 →
   21/60; NDCodes 9/0 → 7/0; Codes2Tape 9/40 → 9/20.
7. **Escalation**: if a probed statement fails in situ, restore the original,
   record it, and continue. Never weaken a statement or add an admission.

## Duplication governance (binding)

Run the screen **before** (omitting the new file) and **after**:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/CodeParser.lean \
  TCSlib/Complexity/TuringMachine/CodeFormat.lean \
  TCSlib/Complexity/TuringMachine/Codes2Tape.lean \
  TCSlib/Complexity/TuringMachine/NDCodes.lean \
  TCSlib/Complexity/TuringMachine/MathlibBridge.lean \
  TCSlib/Complexity/TuringMachine/Encoding.lean
```

**At the base: 169 declarations, 117 pairs, 29,824 characters.**

- **CH34-D2 must collapse.** All 44 directed `CodeParser↔Codes2Tape` pairs and
  all 7 `Codes2Tape↔MathlibBridge` pairs (the `zfBPrim*` against their originals
  and `codePrimSkipFin`) must be gone, along with their in-file companions.
  About 71 base pairs involve a deleted, moved or re-proved declaration.
- **No new cross-file pair**, except those below. Each is pre-classified from
  the probe text as a generic definition paired with the frozen instance it
  bridges, or as a declaration relabelled by the move.

  `actionBitsK` ↔ `Encoding::actionBits` 78/62; `codeSkipActionK` ↔
  `codeSkipAction` 85/68; `codeTable2Bits` ↔ `Code2TM.serialize` 88/66,
  `CodeNDTM.serialize` 88/59, `CodeTM.serialize` 57/53; `oneTapeFormat` →
  `Code2TM.serialize` 62, `CodeTM.serialize` 58, `CodeNDTM.serialize` 55;
  `actionBits₂` ↔ `Encoding::actionBits` 100/67 (the base's NDCodes pair, carried
  by the move); `codeReadVec_sound → codeReadWork_sound` 52;
  `codeEraseVec → codeEraseWork` 52; `codeEraseWork`/`codeEraseActionK →
  codeEraseSymbols` 51.

- **Expected in-file pairs.** CodeFormat: `oneTapeFormat → codeTable2Bits` 89,
  `parseFull ↔ scan` 75/65, `codeEraseActionK → codeEraseWork` 77,
  `actionBits₂ ↔ actionBitsK` 62/53, `codeReadActionK_sound → codeReadWork_sound`
  52. MathlibBridge: `CodeFormat.primrec_scan → codePrimSkipFin` 73, replacing
  `codePrimScan`'s pair. Codes2Tape:
  `zfB3_uniform_of_simulator → exists_effectiveMachineCode2` (base 95%) may persist,
  since both assemble the same literal; `zfB3Answer_malformed → zfB3Answer_zero`
  (55%) is pre-existing.
- **Any other new pair**: report it with both declarations and its share; one at
  90% or more that is not listed here is a copy, so factor it. **The total must
  decrease** (probe-text prediction: about 75–80 pairs, 12,500–15,000 characters).
- Quote both outputs. The expected ledger line is Codes2Tape adaptations 23 → 1
  (`zfBFallback`, a one-line literal), with **"new copies: none"**.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**.
  Use `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-t1-codeformat.txt`, with the C1
  briefs' loop. Record the base sorry-warning set first. Once `CodeFormat`
  exists, check it right after `CodeParser`.
- **Final replay**, in dependency order, over the 23 modules: CodeFormat,
  CodeParser, MathlibBridge, NDCodes, Codes2Tape;
  `CircuitComplexity/{UHaltMachine, PSubsetPPoly, PAdviceSubsetPPoly, Meyer}`,
  `TimeHierarchy/{Diagonal, Separation}`,
  `Diagonalization/{EXPCOM, Relativization, NotTimeConstructible, NTimeHierarchy}`,
  `Randomized/PolyTimeModel` and `SpaceComplexity/Hierarchy`, with their five
  facades; and the `TuringMachine` facade. All must have zero errors, and sorry
  warnings exactly the base's (`exists_effectiveNDMachineCode`,
  `exists_uniformMachineCode2`, EXPCOM's, NTimeHierarchy's, any landed C1 fills').
  **Check Codes2Tape directly**: neither a facade nor `TCSlib.lean` imports it.
  The root `TCSlib` is excluded.
- **Axiom prints** for every public declaration of the six files, 123 in all
  (41 + 45 + 21 + 7 + 9). Pre-existing prints must be identical to the baseline,
  and new ones within `[propext, Classical.choice, Quot.sound]`. `sorryAx` may
  appear only for `exists_effectiveNDMachineCode` and
  `exists_uniformMachineCode2`, as at the base. Also run both
  `audits/programs/ch1-infra-*Axioms.lean`.
- **Lint**: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`
  must report 0 FAIL. MathlibBridge's size WARN predates this batch.
- **Blueprint**: do not edit it. At integration the maintainer regenerates
  `CodeParser.tex` and `MathlibBridge.tex` (whose `\lean`/`\uses` cite 20 of the
  deleted privates) and adds `CodeFormat.tex`.

## REPORT.md checklist

- [ ] The base hash and ancestor check; tasks done, or the Task-1 checkpoint.
- [ ] `freeze.log` over the six-file union: the moves; exactly the sanctioned
      bodies (2b–c) and appendices (2d–e); the private change (2f); every
      deletion and new declaration with its role; the counts against rule 6.
- [ ] Imports: the four changes only; probe statements verbatim, or justified.
- [ ] Duplication: both screens, the CH34-D2 pairs gone, every new pair
      classified, "new copies: none".
- [ ] The final sweep tail (23 modules, plus Codes2Tape checked directly), the
      123 axiom prints with the two audit programs, and the lint line.
- [ ] The diff touches only the six owned files.

## Known pitfalls at this pin (from the pre-ship iterations)

- **A structure field named `mk` clashes with the constructor `CodeFormat.mk`.**
  That is why the field is `assemble`.
- **`parseFull_sound`**: the `readTable_sound` term carries an unreduced
  `(q, r₁).2`. Do `have htable := F.readTable_sound _ _ _ _ ht; dsimp only at
  htable` before `rw`, as `zfBParseFull_sound` does.
- **`parseFull_serialize_pad`**: the final `simp only` needs no `bind`,
  `Option.bind` or `Bool.or_true`; the unused-argument linter flags them. `omega`
  treats `F.guard * (n + 1)` as an atom.
- **`show X from e` split across lines** inside a `by` nested in a term ends the
  tactic block. Use `have he : … := funext F.canonical_eq; rw [he] at hM` instead.
- **Write structure-instance literals one field per line**; a `{ a := …, b := …,`
  line continued at a smaller column fails to parse. **The 354-bit regression**
  needs the *named* fallback plus `dsimp only` before `norm_num`.
- **Dot notation on `F.Code`-typed terms resolves**, e.g.
  `(twoTapeFormat.decode α).toFinTM`. The aliases exist only to keep frozen text
  byte-identical.
- **`twoTapeFormat`**: `serialize_assemble` is
  `simp [Code2TM.serialize, codeTable2Bits, actionBits₂_eq_actionBitsK, workPair]`;
  `assemble_surj` is `congr 1` twice, then `fin_cases i <;> simp [workPair]` (the
  one-tape analogue uses `Subsingleton.elim` on `Fin 1`).
- **Primrec**: `codeSkipActionK` has three binds, so its state argument sits under
  **four** `Primrec.fst`. `CodeFormat.primrec_scan` is `codePrimScan` with
  `Primrec.const F.guard` and the hypothesis in place of the nested
  `codePrimRepeat`. Deleting a declaration takes its docstring with it; moving
  one moves the docstring byte-identically.
