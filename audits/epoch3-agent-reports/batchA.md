# Epoch 3, Batch A — concrete effective machine code

## Result and checklist

- [x] `Turing.exists_effectiveMachineCode` is filled, with no new admissions.
- [x] The decoder implements Argument A's exact serialization grammar, including the canonical state-count test, bounded unary fields, fixed dictionaries, exact table size, and all-true padding.
- [x] An up-front minimum-length test rejects oversized declared tables before record recursion.
- [x] A genuine finite binary canonizer computes `(decode input).serialize`; its arbitrary time bound is extracted from total termination.
- [x] All 138 new handwritten declarations are private and listed below.
- [x] Shared-lemma requests, the file-size escalation, and the docstring appendix are recorded below.
- [x] The final 25-module sweep passes with exit status 0, zero error diagnostics, and exactly the three permitted sorry warnings.
- [x] All three requested axiom checks are admission-free.
- [x] The repository diff touches only `TCSlib/Complexity/TuringMachine/Encoding.lean`.

## Repository and revisions

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested source branch: `complexity/arora-barak-ch1`.
- Verified base: `71721842a2336d5562ef831a19b0e86e063dddaa`.
- Work branch: `fill/epoch3-A`.
- Final commit: `9b72099264dbdb9d0acd607c29096d4723555bf0`.
- Two commits above the base: `4c31f01d` (parser and syntax laws), then `9b720992` (finite canonizer and integration).
- No push or pull request was performed.

The final source contains 2,262 lines. The base-relative diff is 1,768 insertions and 2 deletions in one file. The existing declaration blocks are unchanged except the body of the target theorem. The original target sketch remains, with the explicitly flagged appendix described below. The three standard `set_option` headers remain unchanged. Added imports are the precise modules `Mathlib.Computability.TMToPartrec` and `Mathlib.Data.Fintype.Vector`.

## Parser and relation to Argument A

`encode` is exactly `CodeTM.serialize`. `codeDecode` uses `codeParse`, falling back on the fixed one-state silent immediately halting machine for every rejection.

1. Reuse the original aligned `pairDecode` to read doubled bits and the first aligned false/true separator. Interpret the count bits LSB first and require exact equality with `Nat.bits` of the recovered number. Thus redundant most-significant zeros are rejected, and zero has the required empty count region.
2. Before reading the initial state or enumerating any table records, test `81 * (numStates + 1) > remaining.length`. Each record needs at least nine bits and there are nine records per state. An oversized declaration returns `none` immediately. The bounded vector recursion is reached only after this guard; incomplete or malformed fields also short-circuit via `Option.bind`.
3. Read the initial state as true bits terminated by false, checking its value is below `numStates + 1`.
4. Read exactly `9 * (numStates + 1)` actions, in the same state/input/work-symbol order as serialization. The two head movements, work write, output, and successor use the unchanged serialization dictionaries. Live successor indices are range checked; halted successors consume their single false tag.
5. Accept the remainder only when every bit is true. Invalid field codes, invalid indices, incomplete records, noncanonical count bits, and non-true trailing junk all select the fallback.

The field inverse lemmas combine into `codeParse_serialize_pad` and `codeDecode_serialize_pad`, proving the exact machine round trip for every amount of true padding. Field soundness lemmas also reconstruct the exact consumed prefix. `codeParseFull_sound` retains its precise suffix, which is essential when a valid serialization itself ends in true bits: the canonizer copies the parsed prefix, rather than merely trimming all final true bits.

## Canonizer construction and time-bound route

The canonizer follows the validity-scan/prefix-copy route described in the brief, compiled through a proved general machine construction.

- The erased field readers retain only the unconsumed suffix. `codeEraseFin`, `codeEraseState`, `codeEraseAction`, `codeEraseSymbols`, and `codeEraseVec` relate them to the value-producing parser. `codeScan_full` relates the entire scan to `codeParseFull`.
- `codeCanonical` returns the prefix ending at the parsed table boundary, or the constant fallback serialization. `codeCanonical_eq` proves this is exactly `(codeDecode input).serialize` on every input.
- Private primitive-recursion proofs cover aligned-pair parsing, unary parsing, binary arithmetic and `Nat.bits`, the erased field readers, bounded record iteration, the padding test, and prefix selection. `codePrimCanonical` proves total primitive recursiveness of the canonization function. The pure parser and scanner both retain the up-front guard; no polynomial running-time claim is made about the generic compiled implementation.
- `ToPartrec.Code.exists_code` provides a program, and Mathlib's proved `PartrecToTM2.tr_eval` and finite-support theorem provide its terminating stack-machine execution. These are used as proved library theorems, not as an appeal to this project's admitted `universal`.
- The new four-work-tape `bridgeTM` implements each source stack with its top at the current work head and its occupied cells ending at position -1. Finite control uses only statements in the program's finite support and a finite register. Push uses two native transitions; the remaining elementary instructions use one before their continuation. `bridge_statement` and `bridge_simulate` prove the simulation.
- A high true sentinel in the natural-number encoding preserves empty inputs and arbitrary trailing false bits. Input scanning loads that encoding. The output controller delays one bit, dropping only the sentinel when it encounters the list terminator. `bridge_compiles` combines loading, simulation, and emission into total native computation.
- `bridge_binary` chooses a halting time for each binary input, takes the finite maximum over `List.Vector Bool n`, and then applies the already proved alphabet-reduction theorem. This is the same finite-input argument as `FinTM.Computes.exists_computesFunInTime`, adapted privately to the `ComputesFunInTimeVia` interface before alphabet reduction.
- `codePrim_machine` and `codeCanonical_machine` supply the finite binary machine and its arbitrary length-dependent bound. The target bundles them with the proved scheme laws.

There is no use of `universal`, `timed_universal`, a new axiom, an unsafe proof mechanism, or a native-evaluation axiom. Classical choices select finite data and halting-time witnesses; the selected machine has finite states and an ordinary transition table in the repository's model. Neither polynomiality nor monotonicity of the extracted bound is asserted.

## Requested shared lemmas

These remain private, as the batch owns only `Encoding.lean`:

1. `codePrim_machine`, with the `bridge*` support: a reusable theorem that a primitive recursive binary-string function is computed by a finite binary machine. A future dedicated computability bridge module could own the compiler simulation, stack representation, and input/output coding lemmas.
2. The finite maximum argument inside `bridge_binary`: a `ComputesFunInTimeVia` variant of the existing untimed-to-timed theorem in `TCSlib/Complexity/Uncomputability/Computable.lean`. The proof is a private adaptation of that repository proof; the existing theorem is unchanged.
3. `codePrimBit`, `codePrimBits`, `codePrimDrop`, `codePrimPrefix`, and `codePrimRepeat`: general primitive-recursion closure facts that may be useful in a shared auxiliary module. The grammar-specific readers and their erasure laws should remain with the encoding construction.

## Escalations and docstring appendices

**Split escalation:** the file is now 2,262 lines, exceeding policy §1's approximate 1,000-line threshold. Per this batch's explicit instruction, no shared structure was split. Suggested future boundaries are a generic finite-machine computability bridge and the concrete serialization/parser implementation. Such a split would involve imports and ownership outside this batch.

**Docstring appendix:** the target's original sketch is preserved. The new paragraph labeled **Epoch 3 implementation note** states that this proof uses the permitted arbitrary-time compiler route and finite maxima, rather than establishing the sketch's optional polynomial bound through the composition combinators. The fixed serialization, statement, and effectivity contract are unchanged. New nontrivial helper proofs have adjacent English sketches.

No statement-change escalation was needed.

## Verification evidence

Environment: Lean 4.25.0, matching `lean-toolchain`. `lake exe cache get` was invoked once. Its initial dependency-cache extraction encountered archive ownership errors; the already-built cache executable was then used to recover the required cache, with ownership restoration disabled. No `lake build` was run.

The final sweep used exactly:

```bash
( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )
```

Result: exit 0 across all 25 modules. The checker removes each old output before compilation and requires a fresh nonempty `.olean`. `final-sweep.log` contains the complete output: zero `error:` or `error(...)` diagnostics and exactly these three sorry warnings:

| Declaration | Warning location |
| --- | --- |
| `Complexity.oblivious_of_mem_DTIME` | `TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean:109:8` |
| `Turing.universal` | `TCSlib/Complexity/TuringMachine/Universal.lean:102:8` |
| `Turing.timed_universal` | `TCSlib/Complexity/TuringMachine/Universal.lean:165:8` |

The log also contains ordinary style/unused-simp-argument warnings; these are not admissions or errors. `Encoding.lean` has no remaining sorry warning.

A scratch file outside the repository imported `TCSlib.Complexity.Uncomputability.Diagonalization` and ran the three requested `#print axioms` commands using the check script's `LEAN_PATH`. Exit status was 0. The complete `axioms.log` is:

```text
'Turing.exists_effectiveMachineCode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.UC_not_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.pairEncode_injective' depends on axioms: [propext, Quot.sound]
```

The last regression theorem needs even fewer axioms than the allowed set. No check contains `sorryAx`.

Additional checks:

- `git diff --check` passed.
- The only base-relative modified path is the owned `Encoding.lean`.
- All 138 new handwritten declarations are private and precede the target.
- Existing declaration blocks compare identically with the base, excluding the target's replaced proof and its separately checked docstring appendix.
- `git bundle verify` passed against the required base prerequisite.
- The two-commit format-patch was replayed with `git am` in an isolated checkout of `71721842`; the resulting tree equals the final commit. Complete output is in `artifact-verification.log`.

## Archive contents and use

The ZIP contains this report, the complete modified source at its repository path, `epoch3-A.patch`, `epoch3-A.bundle`, `final-sweep.log`, `axioms.log`, `artifact-verification.log`, and `SHA256SUMS`.

The patch was generated by `git format-patch 71721842 --stdout`. The bundle was generated by `git bundle create epoch3-A.bundle 71721842..fill/epoch3-A` and requires the base commit's history. Apply the patch series with `git am epoch3-A.patch` from the base, or fetch the bundle's `fill/epoch3-A` branch into a repository containing the base.

`SHA256SUMS` covers every payload file in the ZIP. As with a standard checksum manifest, it excludes itself to avoid a self-referential digest. Verify extracted payloads with `sha256sum -c SHA256SUMS`.

## New private declarations

The following list inventories every new handwritten declaration, with final source line numbers. Compiler-generated equations, recursors, and the private `BridgeState` constructors and derived instances are generated from the listed declarations. `BridgeState` has constructors `scan`, `startCons`, `startBit`, `back`, `pushInput`, `exec`, `push`, and `emit`, and derives `Fintype` and `DecidableEq`.

| Declaration | Kind | Line |
| --- | --- | ---: |
| `Turing.codeReadUnary` | def | 441 |
| `Turing.codeReadUnary_append` | lemma | 447 |
| `Turing.codeReadFin` | def | 456 |
| `Turing.codeReadSign` | def | 461 |
| `Turing.codeReadOutput` | def | 468 |
| `Turing.codeReadWrite` | def | 475 |
| `Turing.codeReadState` | def | 483 |
| `Turing.codeReadAction` | def | 489 |
| `Turing.codeReadSymbols` | def | 499 |
| `Turing.codeReadVec` | def | 508 |
| `Turing.codeBitsNat` | def | 518 |
| `Turing.codeFallback` | def | 521 |
| `Turing.codeParse` | def | 527 |
| `Turing.codeDecode` | def | 540 |
| `Turing.codeReadFin_append` | lemma | 543 |
| `Turing.codeReadSign_append` | lemma | 548 |
| `Turing.codeReadOutput_append` | lemma | 553 |
| `Turing.codeReadWrite_append` | lemma | 560 |
| `Turing.codeReadState_append` | lemma | 568 |
| `Turing.codeReadAction_append` | lemma | 575 |
| `Turing.codeReadSymbols_append` | lemma | 589 |
| `Turing.codeReadVec_append` | lemma | 610 |
| `Turing.codeBitsNat_bits` | lemma | 634 |
| `Turing.codeAction_length` | lemma | 642 |
| `Turing.codeFlatMap_length` | lemma | 660 |
| `Turing.codeTable_length` | lemma | 675 |
| `Turing.codeReadTable_append` | lemma | 699 |
| `Turing.codeParse_serialize_pad` | lemma | 718 |
| `Turing.codeDecode_serialize_pad` | lemma | 748 |
| `Turing.codeReadUnary_sound` | lemma | 755 |
| `Turing.codeReadFin_sound` | lemma | 777 |
| `Turing.codePairDecode_sound` | lemma | 790 |
| `Turing.codeReadSign_sound` | lemma | 816 |
| `Turing.codeReadOutput_sound` | lemma | 826 |
| `Turing.codeReadWrite_sound` | lemma | 836 |
| `Turing.codeReadState_sound` | lemma | 848 |
| `Turing.codeReadAction_sound` | lemma | 872 |
| `Turing.codeReadSymbols_sound` | lemma | 886 |
| `Turing.codeReadVec_sound` | lemma | 906 |
| `Turing.codeAllTrue_eq` | lemma | 928 |
| `Turing.codeParse_sound` | lemma | 947 |
| `Turing.codeSkipPair` | def | 981 |
| `Turing.codeSkipFin` | def | 984 |
| `Turing.codeSkipState` | def | 987 |
| `Turing.codeSkipAction` | def | 990 |
| `Turing.codeSkipRepeat` | def | 997 |
| `Turing.codeEraseFin` | lemma | 1001 |
| `Turing.codeEraseSign` | lemma | 1008 |
| `Turing.codeEraseOutput` | lemma | 1017 |
| `Turing.codeEraseWrite` | lemma | 1026 |
| `Turing.codeEraseState` | lemma | 1035 |
| `Turing.codeErase_bind` | lemma | 1045 |
| `Turing.codeEraseAction` | lemma | 1050 |
| `Turing.codeEraseSymbols` | lemma | 1063 |
| `Turing.codeEraseVec` | lemma | 1068 |
| `Turing.codeParseFull` | def | 1080 |
| `Turing.codeScan` | def | 1092 |
| `Turing.codeParse_full` | lemma | 1101 |
| `Turing.codeScan_full` | lemma | 1113 |
| `Turing.codeParseFull_sound` | lemma | 1133 |
| `Turing.codeCanonical` | def | 1162 |
| `Turing.codeCanonical_eq` | lemma | 1165 |
| `Turing.codePrimUnary` | lemma | 1176 |
| `Turing.codePrimBit` | lemma | 1190 |
| `Turing.codePrimBitsNat` | lemma | 1198 |
| `Turing.codePrimPair` | lemma | 1203 |
| `Turing.codePrimBits` | lemma | 1238 |
| `Turing.codePrimSkipPair` | lemma | 1269 |
| `Turing.codePrimSkipFin` | lemma | 1278 |
| `Turing.codePrimSkipState` | lemma | 1285 |
| `Turing.codePrimSkipAction` | lemma | 1293 |
| `Turing.codeSkipRepeat_iter` | lemma | 1306 |
| `Turing.codePrimRepeat` | lemma | 1321 |
| `Turing.codePrimAll` | lemma | 1330 |
| `Turing.codePrimScan` | lemma | 1340 |
| `Turing.codePrimDrop` | lemma | 1361 |
| `Turing.codePrimPrefix` | lemma | 1372 |
| `Turing.codePrimCanonical` | lemma | 1376 |
| `Turing.BridgeAlphabet` | abbrev | 1381 |
| `Turing.bridgeIndex` | def | 1383 |
| `Turing.bridgeStack` | def | 1389 |
| `Turing.bridgeStack_read` | lemma | 1392 |
| `Turing.bridgeStack_nil` | lemma | 1397 |
| `Turing.bridgeStack_push` | lemma | 1401 |
| `Turing.bridgeStack_pop` | lemma | 1418 |
| `Turing.bridgeKey` | def | 1429 |
| `Turing.bridgeKey_index` | lemma | 1432 |
| `Turing.bridgeIndex_key` | lemma | 1435 |
| `Turing.BridgeState` | inductive | 1443 |
| `Turing.bridgeSupp` | noncomputable def | 1451 |
| `Turing.BridgeQ` | abbrev | 1454 |
| `Turing.bridgeBit` | def | 1456 |
| `Turing.bridgeExec` | noncomputable def | 1460 |
| `Turing.bridgeIdle` | def | 1466 |
| `Turing.bridgeOne` | def | 1469 |
| `Turing.bridgeTM` | noncomputable def | 1478 |
| `Turing.bridgeCfg` | def | 1525 |
| `Turing.bridgeCfg_read` | lemma | 1532 |
| `Turing.bridgeReach` | def | 1540 |
| `Turing.bridgeReach_refl` | lemma | 1543 |
| `Turing.bridgeReach_step` | lemma | 1546 |
| `Turing.bridgeReach_trans` | lemma | 1549 |
| `Turing.bridgeCfg_idle` | lemma | 1556 |
| `Turing.bridgeCfg_pop` | lemma | 1563 |
| `Turing.bridgeCfg_push` | lemma | 1599 |
| `Turing.bridgeCfg_pop_any` | lemma | 1636 |
| `Turing.bridgeExec_mem` | lemma | 1665 |
| `Turing.bridge_step` | lemma | 1671 |
| `Turing.bridge_sub` | lemma | 1679 |
| `Turing.bridge_none` | lemma | 1683 |
| `Turing.bridge_statement` | lemma | 1688 |
| `Turing.bridge_label` | lemma | 1788 |
| `Turing.bridge_simulate` | lemma | 1800 |
| `Turing.bridgeNumber` | def | 1823 |
| `Turing.bridgeWord` | def | 1825 |
| `Turing.bridgeNumber_pos` | lemma | 1828 |
| `Turing.bridgeWord_number` | lemma | 1835 |
| `Turing.bridgeCfg_push_input` | lemma | 1859 |
| `Turing.bridgeStore` | def | 1874 |
| `Turing.bridgeStore_push` | lemma | 1877 |
| `Turing.bridge_back` | lemma | 1883 |
| `Turing.bridgeStore_nil` | lemma | 1937 |
| `Turing.bridgeStore_at` | lemma | 1941 |
| `Turing.bridge_scan` | lemma | 1953 |
| `Turing.bridge_seed` | lemma | 1983 |
| `Turing.bridge_start` | lemma | 2019 |
| `Turing.bridgeCfg_pop_emit` | lemma | 2028 |
| `Turing.bridge_emit_step` | lemma | 2044 |
| `Turing.bridge_emit` | lemma | 2061 |
| `Turing.bridge_compiles` | lemma | 2095 |
| `Turing.bridge_binary` | lemma | 2130 |
| `Turing.bridgeNumber_bits` | lemma | 2145 |
| `Turing.bridgeUnnumber` | def | 2153 |
| `Turing.bridgeUnnumber_number` | lemma | 2155 |
| `Turing.bridgePrimNumber` | lemma | 2158 |
| `Turing.bridgePrimUnnumber` | lemma | 2162 |
| `Turing.codePrim_machine` | lemma | 2167 |
| `Turing.codeCanonical_machine` | lemma | 2178 |
