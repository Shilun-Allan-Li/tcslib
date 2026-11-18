# EF-H1 `ef-h1-arith` · final r1 · phase-1 (static) maintainer review

**Provisional verdict (phase 1 only): ACCEPT WITH LANDING EDITS for the series. The brief's headline
is not in the series: it depends on the reader ruling EF-W1-R.** Phase 1 found no blocker and no major.

**What the series proves** (five commits, the three new files plus the facade):
- `polyTimeComputable_sizeStr`, the field itself;
- `PrimesInP` with its reader `primesInP_iff`;
- the reader-free half of the bridge, `polyTimeComputable_primeStr_iff_bitsVal`;
- the other six cheap fields and `xgcd` (extended Euclid, every modulus) in the **re-paired form**
  `PolyTimeComputable fun z => f ⟨pairFstD z, pairSndD z⟩`.

**What it does not prove.** It does not prove `PolyTimeComputable f` for those seven fields, nor
`ArithmeticFP.ofPrimesInP` or `arithmeticFP_iff_primesInP`. All three need nine one-line readers in frozen
files (E-SCOPE).
- **Where the readers would go.** Seven belong in `Candidates/Arithmetic.lean`, which is this campaign's
  file. Two belong in `Complexity/Randomized/Primality{,Math}.lean`, which are read-only for wave 1 and
  owned elsewhere.
- **The E-SCOPE is genuine** (§ *The E-SCOPE*).
- **The worker's overlay.** The final carries a compiled overlay, outside `patches/`, that adds the nine
  readers and the 13 remaining declarations. I reproduced it hash-exactly. Its evidence has two gaps,
  F01 and F02, which phase 2 closes.

**Whether the overlay lands is not decided here.** It is question **EF-W1-R**, framed jointly with
EF-D1-R1 and EF-H12-W1 because all three jobs hit the same problem.

**Findings:**
- **Minors:** EFH1-F01 to EFH1-F06.
- **Information:** EFH1-I1 to EFH1-I7.

Phase 2 (Lean) has not run. Its plan is § *Phase 2 plan*.

## What was reviewed

- **Delivery.** `inbox/fills/ef-h1-arith/` on `exchange/pass-shelat-ch5-8`, at commit
  `0e18bf6df1ef27feba575bbb1e910cc2a8c36aa2` ("fill ef-h1-arith: final").
  - **The commit.** Its parent is `36d9ac03` (the EF-H12 final). It is unsigned (0 `gpgsig`) and
    touches 1,486 paths, all under the unit's folder.
  - **It is the origin tip at review time.** The local `exchange/pass-shelat-ch5-8` ref is stale at
    `47f548ec`; I used the pinned hash.
  - **The tree.** I extracted it with `git archive` into a fresh directory. It has 1,768 files:
    - `REPORT.md` (324 lines);
    - 5 patches with `COMMITS.tsv`;
    - `src/` (4 files);
    - `evidence/` (1,755 files plus its `SHA256SUMS`), which includes the overlay under
      `evidence/scope-request/`.
  - **Manifests.** The top-level `SHA256SUMS` is `736539b3…`; `evidence/SHA256SUMS` is `903a00eb…`.
- **Checkpoint 1** (`9a5cc15a`) had the same Lean head `0a73fc9c`. The final adds the overlay, the root
  sweep and the REPORT updates.
- **Contract.**
  - `briefs/efficiency-gaps/wave1/EF-H1/brief.md`, `COMMON.md`, `rulings.md` and `README.md` at the
    records pin `54dcb3021a389831e7f94c3f82616cb7594fa574`. Between the pin and the records tip, the
    brief, `COMMON.md` and `rulings.md` are unchanged; `README.md` and the dispatch prompt changed only
    in their pin and status lines.
  - Rulings Q-H1-1 A and Q5 A.
  - Handoff §2, rules 15 and 16.
- **Background.**
  - Decision-log rows 903 (EF-H12 checkpoint 1, `Bridge.lean`), 904 (this job's checkpoint 1 and its
    E-SCOPE) and 907 (EF-D1 review, EF-D1-R1).
  - The method precedent `EF-D1/final-r1/review.md`.
  - EF-H12's final `REPORT.md` (exchange `36d9ac03`), for the joint question only.
- **Base.** REC = `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62`, tree `d52cf05b…`, both checked.
- **Method.** Static only: `git`, and `python3 -I` for my own scripts and the repository's `decls2.py`
  and `style_lint.py`. No Lean was run.
  - My scratch is a sparse detached worktree at
    `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/efh1/amwt`. It is
    kept for phase 2 and now sits at the overlay head.
  - The extracted delivery is in `…/scratchpad/efh1/deliv/`.

## Checks

| Check | Result |
|---|---|
| **Integrity** | **PASS.**<br>• Both manifests pass `sha256sum -c`.<br>• Top level: 1,767 entries, which equal the delivered files minus the manifest itself.<br>• Evidence: 1,755 entries, likewise.<br>• Nothing missing, nothing extra, no leading `./`, no duplicates, and neither manifest lists itself. |
| **Patches (C13)** | **PASS: 5/5 hashes reproduced.**<br>• Method: `git am` at the base, with signing off and the committer name, e-mail and date from each `COMMITS.tsv` row.<br>• Hashes: `4f9bba64`, `8d26ba1d`, `58165f50`, `bba10dd8`, `0a73fc9c1a743954e30676982ed721ba7e573679` (= REPORT's head).<br>• No commit has a `gpgsig`.<br>• `src/` equals the head byte for byte, 4 of 4 files. |
| **Scope** | **PASS.** `git diff --stat cf6a2266 0a73fc9c` lists exactly the brief's four files:<br>• `ArithmeticDischarge.lean` +236 (new);<br>• `ExtendedEuclidMachine.lean` +496 (new);<br>• `PrimesInP.lean` +96 (new);<br>• `Candidates.lean` +12.<br>That is 840 insertions and 0 deletions. **`Arithmetic.lean` and every consumer are untouched.** The facade change is 3 imports and 9 `## Contents` lines, nothing else (my diff; C7 agrees). |
| **Overlay integrity (separate)** | **PASS (reproduction).**<br>• `git am` of `evidence/scope-request/patches/` on `0a73fc9c`, with its own `COMMITS.tsv`, gives `b3eba391` and `f5e67909ff8a61f67f254217e8de90782a0eb4f6`, hash-exact.<br>• Its `src/` equals that head byte for byte, 6 of 6 files.<br>• It is not in `patches/` and not in the series. |
| **decls2 (C3)** | **PASS.**<br>• Pinned `decls2.py` (`0ba6f6a1`), run by me at `0a73fc9c` against the base: **50 ADDED, 0 CHANGED, 0 REMOVED**. My output is byte-identical to the delivered `C3-decls2.txt`.<br>• Overlay against the fill head: **22 ADDED**. This is the same row set as the delivered file (order differs with argument order). |
| **Merge with the records tip** (information) | `git merge-tree --write-tree` with `bff0567b` is clean for both heads:<br>• series → tree `16371c0e…`;<br>• overlay → tree `050a20b1…`.<br>Between `cf6a2266` and `bff0567b`, 12 Lean files changed. None is among this job's files or in the 160-module TCSlib import closure of `PrimesInP` (my static count on tree `050a20b1`). |
| **Disjointness** | **PASS.** I checked every remote head that has a merge base with REC (283 of 285 refs), diffing from each one's merge base. None has changed `Candidates/Arithmetic.lean`, `Randomized/Primality.lean` or `Randomized/PrimalityMath.lean`.<br>• Positive control: `ClassP/BinaryArith/{Div,ModPow,Mul}` are found changed on `complexity/arora-barak-ch3-4`, as the brief says.<br>• None of these three files is in `scope.tsv` or `s2a-items.tsv`. Those list only `NumberTheory/Primality.lean`, a different file. |
| **Clashes (C10)** | **PASS.**<br>• I grepped all **285 remote heads** (`TCSlib/`, `audits/`) for every new name of the series and the overlay: the `xgcdLoop*`, `xgcdState`, `XgcdLoopInv`, `modExpModulus*`, `PrimesInP`, `primesInP_*`, `ofPrimesInP` and `toLE_pair*` families, `fromLEPoly_var*`, `primeBit_eq_*`, `mem_PRIMES{,Bin}`, the seven `*Str_eq`, and every `polyTimeComputable_*Str{,_pairEncode}`.<br>• **0 hits.** The control `mulStr_pairEncode` hits on 128 heads. |
| **Admissions (C4)** | **PASS.** 0 `sorry`, `admit`, `native_decide`, `axiom` and `opaque` tokens in the code of the 3 new files and the facade, at both heads; the only `axiom` is prose in `PrimesInP`'s docstring. No existing file's code changed in the series. |
| **Hygiene** | **PASS.**<br>• Sizes: A 236, B 496, C 96 and facade 79 lines; maximum width 99, 100, 97 and 95 (overlay: 271, 502 and 150 lines, at most 100 wide).<br>• No `@[simp]`, no `attribute`, no `private`, no `unfold`.<br>• Mathlib-style headers with the repository copyright, `relaxedAutoImplicit false` and `autoImplicit false`. `maxHeartbeats 0` is the house form.<br>• `style_lint.py` (my run, on an untracked copy in the scratch worktree): **0 findings in the 4 series files, and 0 in the 7 overlay files**, which include `Arithmetic.lean` and both `Primality*` files.<br>• Two proofs lack a sketch: F05. |
| **Citations** | **PASS, with F04.** Each anchor checked against the ingested text:<br>• [PS10] Algorithm 43.2 (l. 987), Claim 43.3 (l. 1005), Algorithm 45.5 (l. 1082), Theorem 45.6 (l. 1094) and p. 33 (l. 512–520), in `pass-shelat-2010-ch2.raw.md`;<br>• the AKS remark (l. 1286–1288), which lies under §2.6.5 (heading at l. 1215);<br>• [AB09] `p003-b004` (the §7.2 opening with the AKS sentence; `b003` is Definition 7.4, as the worker says).<br>The chapter-notes anchor is wrong in both the brief and the REPORT: F04. |

## Brief targets: proved in the series, or needing the overlay

| Brief target | Series (`0a73fc9c`) | With the overlay (`f5e67909`) |
|---|---|---|
| `polyTimeComputable_sizeStr` | **proved**, verbatim | unchanged |
| `polyTimeComputable_{mul,add,sub,divMod,le}Str` | proved in re-paired form (`…_pairEncode`) | **proved** verbatim, each a one-line `congr` through `f_pairEncode` and the new `f_eq` |
| `polyTimeComputable_modExpStr` | proved in re-paired triple form | **proved** verbatim |
| `polyTimeComputable_xgcdStr` | proved in re-paired form | **proved** verbatim |
| `def PrimesInP := Randomized.PRIMESBin ∈ Complexity.P`, `primesInP_iff` | **proved**, verbatim (Q-H1-1 A) | unchanged |
| `polyTimeComputable_primeStr_of_primesInP` and its converse | only the reader-free half, `polyTimeComputable_primeStr_iff_bitsVal` | **proved**, through `primesInP_iff_polyTimeComputable_primeBit` (`test_of_mem_P`, `mem_P_of_test`, `mem_PRIMESBin`, `mem_PRIMES`) |
| `ArithmeticFP.ofPrimesInP` | not stated | **proved**: 8 fields unconditional, `prime` from `h` |
| `arithmeticFP_iff_primesInP` | not stated | **proved** |
| H1-P2 (consumer smoke test) | n/a | `H1P2.log`: `ofPrimesInP h` is accepted as `H` by `factoringCollection_oneWay`, `rsaCollection_oneWay`, `dlCollection_oneWay` and `polyTimeComputable_expEval`. No error lines; 13 targets `[propext, Classical.choice, Quot.sound]`. |

**Note.** The series' `PrimesInP` and the field theorems are exactly the brief's statements. No target is
weakened silently.

## The E-SCOPE (checkpoint 1, carried to the final)

**It is genuine.**
- **`Arithmetic.lean` (base).** It publishes readers of `mulStr`, `addStr`, `subStr`, `divModStr`,
  `xgcdStr`, `modExpStr` and `leStr` only on `pairEncode` inputs (`:338–452`). Every-input readers exist
  only for `sizeStr_eq` (`:369`) and `primeStr_eq` (`:455`).
- **No every-input equation of the seven exists anywhere.** I grepped REC, IO and `bff0567b` for any
  `*Str z = …` theorem or any reader named after them outside `Arithmetic.lean`.
- **Why a field needs one.** A field `PolyTimeComputable mulStr` is a statement about every word,
  malformed pairs included. Its only link to the re-paired form is `mulStr z = mulStr ⟨pairFstD z,
  pairSndD z⟩`, which needs `mulStr`'s body. That is a foreign read (Rule 10). The worker's NEG4 control
  shows it fails sealed.
- **`PRIMESBin` and `PRIMES`.** `PRIMESBin` (`Primality.lean:63`) and `PRIMES`
  (`PrimalityMath.lean:77`) have no membership lemma in their own files or anywhere else. The four
  `PRIMESBin` theorems are class statements (`inCoRP_PRIMESBin`, `inBPP_PRIMESBin`,
  `PRIMESBin_mem_coRP_PTM`, `PRIMESBin_mem_BPP_PTM`).
- **So there is no reader-free route** from `PRIMESBin ∈ P` to a primality test.

**What the overlay changes, exactly:**
- **R1** (`b3eba391`, "not part of the fill series") adds:
  - to `Arithmetic.lean`: `mulStr_eq`, `addStr_eq`, `subStr_eq`, `divModStr_eq`, `xgcdStr_eq`,
    `modExpStr_eq` and `leStr_eq`, each `f z = <body> := rfl` (+44 lines, one new section header);
  - to `PrimalityMath.lean`: `Randomized.mem_PRIMES (N) : N ∈ PRIMES ↔ N.Prime := Iff.rfl` (+3);
  - to `Primality.lean`: `Randomized.mem_PRIMESBin (x) : x ∈ PRIMESBin ↔ bitsVal x ∈ PRIMES := Iff.rfl`
    (+4).

  Nothing else in those files changes.
- **R2** (`f5e67909`) touches only the three new files:
  - the 7 field theorems;
  - `primeBit_eq_indicator`, `primesInP_iff_polyTimeComputable_primeBit`, the bridge pair,
    `ofPrimesInP` and the equivalence;
  - module docstrings.

  The facade is not updated: F06.
- **Whether it compiles (worker's evidence).** `scope-request/build/summary.txt` gives the 7 changed
  modules rc 0, 0/0 errors and 0 `sorry`, with sources bound by SHA-256 to the overlay head. Seals coe-A
  and strict-B pass on the three new files. The worker's pool log disagrees with REPORT's account of it
  (F01), and the downstream check covers 16 of 66 modules (F02).

## `xgcd`: extended Euclid for every modulus

**The loop is extended Euclid, with no Fermat inverse.** File B has no `powMod`. The loop follows Mathlib's
`Nat.xgcdAux` exactly:
- the round is `Nat.xgcdAux_rec`, with the Bézout coefficient kept modulo `b` (`xgcd_coef_residue`);
- it starts from the arguments of `Nat.xgcd (a mod b) b`;
- at `r = 0` it reads `gcdA` through `Nat.xgcd_zero_left`, `Nat.xgcdAux_val` and `Nat.xgcd_val`.

The agreement is with Mathlib's `Nat.gcdA`/`ZMod.inv`, as the brief asks, not with a private
re-definition. The round bound is `extEuclidCalls_le` [PS10, Claim 43.3]: at most `2|b| + 1 ≤ 2(|z| + 1)`
rounds of `BinArith.polyTimeComputable_iterate`, on states of at most `11(|z| + 1)` bits.

**Degenerate moduli, checked against the field spec** (`xgcdStr` at `Arithmetic.lean:277`) **and Mathlib**
(`ZMod.inv`, `Mathlib/Data/ZMod/Basic.lean:695`):
- **`⟦b⟧ = 0`.**
  - `xgcdInvWord` takes the sign branch: `bits 0` for `⟦a⟧ = 0`, else `bits 1`. This matches
    `ZMod 0 = ℤ`, `inv = Int.sign`, `val = natAbs` (`Int.natAbs_sign`).
  - The gcd is `BinArith.gcd`. `gcd_pairEncode` is unconditional (`ModPow.lean:261`), so `gcd(a, 0) = a`.
  - Both are written at width `|b|`, so they truncate: at `|b| = 0` both are `[]`, and at `|b| = 2`,
    `a = 4` gives gcd `0` and inv `1`.
  - The loop is never used here: its start state has `r = 0` and is fixed.
- **`⟦b⟧ = 1`.**
  - **The gcd component is `1`, not `0`.** The brief's edge-case note "at `⟦b⟧ = 1` everything is `0`"
    is wrong for the gcd (I1). The inverse is `0` (`gcdA (a mod 1) 1 = gcdA 0 1 = 0`).
  - The delivery follows the spec, so it is right.
- **Composite `b` and non-units.** The value is `gcdA (a mod b) b mod b`. For example, `8⁻¹ mod 12 = 11`.
- **Probe recount.** I recomputed all **144 rows** of the delivered `H1P1.log` table with an independent
  Python model of Mathlib's `Nat.xgcdAux` and the two `ZMod.inv` cases. The rows are `⟦b⟧ ∈
  {0,1,2,4,6,9,12} × ⟦a⟧ < 16` at width 4, plus `b = 0` at widths 0 and 2.
  - **0 mismatches.**
  - Every unit row satisfies `a·inv ≡ 1 (mod b)`.
  - The summary lines give 0 mismatches over 1,088 inputs for each pair function, and 4,463 for
    `modExpStr`.

**The `modExpStr` modulus-0 edge.**
- **The problem.** `BinArith.powMod_pairEncode` requires `p ≠ 0` (`ModPow.lean:57`), and `powMod`
  returns `0` at modulus `0`. That is not `modExpStr`'s value.
- **The fix.** `modExpModulus N` is `bits (2^{|N|})` when `⟦N⟧ = 0`, else `toLE N`. Its spec gives
  `M ≠ 0` and `⟦a^x mod M⟧_{|N|} = ⟦a^x mod ⟦N⟧⟧_{|N|}`, via `natToList_mod_two_pow` and
  `Nat.mod_zero`.
- **The result.** At `⟦N⟧ = 0` the value is the low `|N|` bits of `a^x`, with `a^x` never materialized,
  exactly as the brief requires. At `|N| = 0` the modulus is `1` and the output is `[]`, which is right.
- **The `2^{|N|}` word** comes from the registered `BinArith.polyTimeComputable_powerOfTwo`
  (`Unary.lean:43`). The worker found it and disclosed it.

**The other cheap fields.**
- At `⟦b⟧ = 0`, `div`/`mod` agree with Lean's `a / 0 = 0` and `a mod 0 = a`. `div_pairEncode` and
  `mod_pairEncode` are unconditional.
- The widths are taken from the template word's length through `fromLEPoly .var`:
  - `|a| + |b|` through `pairConcat`;
  - `|a|`, `|b|` and `|N|` through the projections.
- `sizeStr` is `1^{|toLE w|}`, using `toLE_eq_natBits` and Mathlib's `Nat.size_eq_bits_len`.

## Rule 15 (uniform forms)

- **Every efficiency statement is `PolyTimeComputable f` of an explicit string map.** That holds for
  the series, the overlay and every helper.
- **No `NUPPT` occurs** in any of the three files at either head, so there is no bare
  `∃ A : NUPPT, A.Computes`.
- **The machines use registered hosts only:**
  - `BinArith.polyTimeComputable_iterate`, with `iterate_invariant` and `iterate_measure_eq_zero`;
  - `polyTimeComputable_ite`;
  - the `BinArith` arithmetic machines;
  - the `Encoding.BinaryArith` adapters.

  There is no private loop or runner.
- **The only hypothesis is `h : PrimesInP`,** the standing exception of ruling Q5 A. It is a `def` of a
  true `Prop`, documented as such, never an axiom, and taken as an explicit argument.
- **`ArithmeticFP` appears only as a target.** In the overlay it is the conclusion of `ofPrimesInP` and
  the left side of the iff. It is never a new hypothesis of a construction.

## Duplication sweep (binding)

**Searches.** I searched REC, IO `5ed465f6` and `bff0567b`, plus Mathlib `029db123dd`:
- `ClassP/BinaryArith` (`AddSub`, `Div`, `Mul`, `ModPow`, `Unary`, `Iterate`);
- `Encoding/BinaryArith.lean` (all 19 declarations);
- `NumberTheory/Euclid.lean`;
- every `*Str` theorem in TCSlib;
- `gcdA|xgcdAux|Nat.xgcd|ZMod 0)⁻¹|natAbs_sign|ZMod.inv`;
- Mathlib's `ZMod/Basic.lean` and `Int/GCD.lean`.

I also read the EF-R2/R3 toolkit, `inbox/fills/ef-r23-regev/src/…/Encoding/ModularArithmetic.lean`
(730 lines, exchange `0e18bf6d`).

**Results.**
- **No undisclosed re-proof.** No public TCSlib or Mathlib lemma is restated.
- **Must-reuse items.** All are used, or bypassed for a stated and correct reason:
  - **Used:** the `BinArith` machines and their `*_pairEncode`; `polyTimeComputable_iterate`,
    `iterate_invariant` and `iterate_measure_eq_zero`; `toLE`, `toLE_eq_natBits`, `bitsVal_toLE`,
    `fromLEPoly` and `fromLEPoly_pairEncode`; `mulStr_pairEncode` and the other `*_pairEncode`;
    `natToList_mod_two_pow`; `extEuclidCalls_le` and `extEuclidCalls_of_mod_ne_zero`;
    `test_of_mem_P` and `mem_P_of_test` (overlay).
  - **`GcdInv`, `gcdMeasure`, `gcdInv_step`** (`ModPow.lean:279–306`) are not reused. The reason is
    right: `gcdStep`, `GcdInv` and `gcdMeasure` publish no readers. So the loop's `⟨r', r⟩` slot cannot
    be identified with a `gcdStep` state without unfolding `gcdStep`. The textbook count
    `extEuclidCalls` has published equations and the cited bound.
  - **`extEuclid_spec` and `extEuclid_inv`** are not used, correctly: the field's value is
    `ZMod.inv`, not `extEuclid`.
  - **`normalizeWidthPoly`** is not needed, because `fromLEPoly` does the width.
- **The disclosed near-relatives are accurate:**
  - the `toLE (pairFstD …)` compositions inside `DyadicArithmetic` proofs (local `have`s);
  - `CoinSampling/Efficiency.lean`'s inline `fromLEPoly .var` (IO);
  - `DiscreteLogHardcore.lean:1053` (private, a different statement);
  - `xgcd_coef_residue`, a short `Int.ModEq` computation;
  - `length_xgcdState_le`;
  - `primeBit_eq_primeStr_fromLEPoly` against `fromLEPoly_pairEncode`'s internal `hvalue`.
- **Two near-relatives are not disclosed** (F03). Neither is a re-proof.
- **The ruled-out Fermat inverse** is absent (brief).
- **EF-R2/R3 versus EF-H1: no duplication in either direction.**
  - EF-R2/R3's `addMod` (`ModularArithmetic.lean:76`) uses the same composition
    (`toLE` → `BinArith.add`/`mod` → `fromLEPoly .var`). It inlines what EF-H1 states as
    `fromLEPoly_var_bits`, in `simp only [fromLEPoly_pairEncode, bitsVal_bits, eval_var]`.
  - Neither job publishes a declaration the other restates.
  - EF-R2/R3 has no gcd, inverse, `powMod` or `*Str` use. EF-H1 has no modular addition. File B's
    `xgcdCoefStep` (residue subtraction) is internal to the loop.
  - The shared composition helpers are a later consolidation candidate (I4).

## Statement changes (disclosed, REPORT §5 and §7a)

1. **The re-paired form** for the six pair fields and `xgcd`, with the triple form for `modExpStr`.
   - **Disclosed and justified** by the E-SCOPE.
   - **No weakening is hidden.** The re-paired functions agree with the fields on every word: the
     overlay's one-line `congr` proofs show it, and H1-P1 tests the raw form as well.
   - **Weaker as a library statement.** In the series alone, the re-paired theorem is strictly weaker
     than the field. That is why the series does not discharge `ArithmeticFP`.
2. **The bridge is split.** The reader-free `primeStr ⇔ little-endian test` half is in the series; the
   `PRIMESBin` half is in the overlay. Disclosed.
3. **Additional public declarations:** 50 in the series and 22 in the overlay. Both counts are
   recounted (C3). Among them, outside the brief's list:
   - in the series: the glue helpers and the loop pieces;
   - in the overlay: `primeBit_eq_indicator` and `primesInP_iff_polyTimeComputable_primeBit`.

   All are disclosed, and both overlay names are reasonable.

The series is 840 lines, within the brief's 900–1,600 ±40%. With the overlay it is 1,002.

## Recount of the worker's evidence

I recounted from the raw files, binding them to the reproduced sources by SHA-256.

- **Build (C1).** `build/summary.txt`:
  - 4/4 rc 0, 0/0 errors and 0 `sorry`.
  - The source hashes equal my reproduced head (`9283869d…`, `8c3e0ff1…`, `51c49532…`, `1b38a302…`).
  - The 4 raw logs carry only `/usr/bin/time` lines, ending `Exit status: 0`.
- **C2 root sweep.** I parsed all 1,431 logs in `logs/rootsweep/` against `build/order-root.txt`
  (1,449 modules):
  - **1,428 rc 0, 3 rc 1, and 18 have no log.**
  - The 3 failures are each `unknown module prefix 'PFR'`: `NewmanTheorem/{Newman, Entropy/Basic,
    FuncDisjointnessLowerBound/HardSample}`.
  - The 18 without a log are downstream of those failures, ending in the root `TCSlib`.
  - **Errors.** There are 3 `error:` lines (the PFR ones) and 0 `error(` lines.
  - **`sorry` warnings.** There are 192, in 44 modules, **none of them a delivery module**.
  - `audits/pass-shelat/Checks` is rc 0.
  - The facade's only importers at the base are `TCSlib.lean` and `audits/pass-shelat/Checks.lean`
    (checked). So the root is the only unchecked importer: question W2, closed by phase 2.
- **C3.** Byte-identical (above).
- **C5.** `C5-axioms-summary.txt`:
  - **50 declarations, with 0 non-standard axioms.**
  - The sets are `[propext, Classical.choice, Quot.sound]` and, for definitional items, subsets of it.
  - Overlay `H1P2.log`: 13 targets, all exactly standard.
- **Seals (C6).**
  - **The worker's seal lists.** `seals/results/`: coe-A and strict-A have 443, 444 and 1,111
    candidates for A, B and C; coe-B and strict-B have 444, 445 and 1,112. All are `PASS (rc=0, error
    lines=0)`.
  - **I compared the lists themselves.** coe-A equals strict-A byte for byte for each owner. B differs
    from A by exactly `Complexity.PolyExpr.eval`.
  - **Coverage of the foreign definitions.** I checked that the lists contain those the files read:
    - A: `mulStr`…`sizeStr`, `natToList`, `listToNat`, `toLE`, `fromLEPoly`, the `BinArith`
      machines, `bitsVal` and the projections;
    - B: `xgcdStr`, `BinArith.{gcd,mod,div}`, and A's `modExpModulus`;
    - C: `Randomized.PRIMESBin`, `Randomized.PRIMES`, `primeStr`, and every A and B definition.
  - **One gap: `extEuclidCalls` is in no list.** It is defined by well-founded recursion
    (`termination_by`), and so is irreducible by default. It is read here only through its published
    equations, and the unfold scan below finds no foreign unfold. Phase 2 confirms its reducibility
    status (I2).
  - **Not my canonical harness.** These are the worker's `tools/seal.py` lists, not the gate-04 recipe
    harness, and the raw sealed-run logs are not delivered: only the result lines are. Phase 2 re-runs
    coe-A with the recipe harness.
- **Paired controls.** `controls-Sealed.log` has exactly 4 errors, at `Sealed.lean` lines 8, 15, 20
  and 24. These are NEG1 (`modExpModulus`), NEG2 (`xgcdState`), NEG3 (`PrimesInP`) and NEG4 (the base's
  `mulStr`, which is the scope request).
  - POS1–POS4 (lines 11, 18, 21, 26) produce no error.
  - `controls-Unsealed.log` is empty.
  - `Sealed.lean` minus its `attribute` line equals `Unsealed.lean`.
  - **ALL_OK.** There is one pair per owner. 7 of B's 8 definitions have no isolated pair (I2).
- **Explicit-unfold scan.** The delivered scan reports 0 foreign, with a control of exactly 1.
  - **My scan agrees.** I ran my own static scan of every `rw`/`simp`/`unfold`/`dsimp` argument
    against all 5,686 TCSlib definition names at the base, at both heads. It finds **0 foreign
    definitions**.
  - **Two owner-file unfolds.** It also finds `rw [xgcdLoopMeasure, …]` and `rw [xgcdInvWord, …]`,
    each inside its owner file (allowed).
- **Lint (C8).** `campaign-base.txt` and `campaign-head.txt`:
  - 92 FAIL / 103 WARN each, over 531 and 534 files;
  - the FAIL and WARN line sets are identical (my diff);
  - these equal the maintainer's REC figures;
  - `style_lint.txt` reports 0 findings in 4 files.
- **C7/C9.** C7's "base 68 → head 80 lines" is off by one each way: `wc -l` gives 67 → 79, and C9
  itself says 79. The 12 inserted lines and the control are right. This is a nit, folded into F01.
- **H1-P1.** The table was recounted independently (above). The kernel `decide` examples are on
  `mulStr` and `leStr` only, and no `native_decide` is used.
- **H1-P2.** Read (above); it runs on the overlay only.

## Findings

**Blockers: none. Majors: none.**

- **EFH1-F01 (minor; the overlay's build evidence is misdescribed).**
  - **What REPORT says.** §7a states that the 16 affected modules were "rebuilt in order, all rc 0
    (`build-pool.log`)".
  - **What the log says.** `build-pool.log` ends `done=14 failed=1 blocked=1 total=16`:
    - `PrimesInP` failed with `Unknown constant Turing.MultiTapeTM.indicator_eq_true_iff` and an
      unsolved goal, from an earlier draft of R2;
    - the facade was blocked behind it.
  - **What the final shows.** The per-module run at the overlay head (`scope-request/build/summary.txt`,
    sources bound by SHA-256) has all 7 changed modules rc 0, so the final overlay sources do compile.
  - **What stays unbound.** The 9 consumer rebuilds in the pool log (`Concrete`, `Factoring`, `RSA`,
    `Rabin`, `DDH`, `DiscreteLog{,Hardcore}`, `ElGamal`, `Encoding/BinaryArith`) carry no source
    hashes.
  - **Smaller nits.** The headline table still says "State at this checkpoint", and C7's line counts
    are off by one.
  - **Fix.** None for the worker. Phase 2 rebuilds the overlay's full downstream from bound sources.
- **EFH1-F02 (minor; the overlay's downstream check is partial).**
  - **The real downstream.** The overlay changes three existing files. Their downstream is 66 modules
    at REC, and 71 at `bff0567b` including both `audits/*/Checks` and the root.
  - **What the worker checked.** 16 modules: the closure of the delivery's own files.
  - **The risk is low.** The additions are 9 new `rfl`/`Iff.rfl` theorems, and their names clash with
    nothing on any remote head (C10). Even so, a facade-level change to `Arithmetic.lean` and two
    Complexity files needs the full sweep.
  - **Fix.** Phase 2, run B.
- **EFH1-F03 (minor; disclosure).** Two near-relatives are missing from REPORT §8. Neither is a re-proof.
  - **`fromLEPoly_var_bits`.** It is a one-line specialization of the public `fromLEPoly_pairEncode`
    (`Encoding/BinaryArith.lean:216`) with `LogProg.bitsVal_bits` and `PolyExpr.eval_var`. REPORT
    lists it among the glue helpers, not as a specialization. EF-R2/R3's `addMod_pairEncode` derives
    the same inline.
  - **The `ZMod 0` branch of `xgcdInvWord_spec`.** It derives `((a : ZMod 0)⁻¹).val = [a ≠ 0]` inline
    by `Int.natAbs_sign`. This is the reading `Arithmetic.lean:438`'s `val_inv_natCast_zmod_zero_le`
    makes. That lemma states only `≤ 1`, so it cannot be cited; Mathlib has no equality lemma.
  - **Fix.** A ledger note, together with I4.
- **EFH1-F04 (minor; attribution).**
  - **(a) The chapter-notes anchor.** It is **`pdf-26d95080dbde-p017-b002`** ("Chapter notes and
    history … later AKS proved PRIMES ∈ P"), not `p017-b001`, which is "What have we learned?".
    - Both the brief and the worker's W3 "confirmation" have `b001`.
    - The Lean cites no block id, so this is a records-only correction.
  - **(b) Five "Glue" declarations carry a book tag.** `polyTimeComputable_{mul,add,sub,divMod,le}
    Str_pairEncode` say "Glue." and also cite "[AB09, §7.2]".
    - COMMON §4.6 says Glue carries no tag.
    - The house form in `ClassP/BinaryArith` is "infrastructure for [AB09 §7.2]; not itself a result
      of the book".
  - **Fix.** A wording edit; no Lean change.
- **EFH1-F05 (minor; form).**
  - **Two proofs of about 20 lines lack a labelled `**Proof sketch.**`:** `xgcd_coef_residue` (19
    lines) and `polyTimeComputable_xgcdLoopStep` (20 lines). The docstring of the second describes the
    composition, but without the label.
  - **One definition lacks an every-input reader.** `xgcdLoopMeasure` has only the state reader
    `xgcdLoopMeasure_state`. It is internal, and is read in-file only.
  - **Fix.** A landing edit: the labels, and optionally `xgcdLoopMeasure_eq`.
- **EFH1-F06 (minor; overlay landing edits, if the overlay lands under EF-W1-R (A) or (B)).**
  - **The facade's `## Contents` is stale.** It still describes the pair fields as "(on re-paired
    inputs)" and names no field theorem, `ofPrimesInP` or the iff.
  - **Process notes in owner files.** R1 puts "(scope request EF-H1, S8/S9)" and "(scope request
    EF-H1, `ef-h1-arith`)" into the docstrings and section header of the owner files. Drop these.
  - **Blank lines.** R2 leaves three double blank lines before its new sections. `style_lint` does not
    flag them.

**Information:**

- **EFH1-I1 (brief erratum).** The brief's edge-case list says "at `⟦b⟧ = 1` everything is `0`". In
  fact the gcd component is `natToList |b| 1`; only the inverse is `0`. The delivery follows the field's
  spec (`Nat.gcd a 1 = 1`). Record this in the brief's errata if the brief is reused.
- **EFH1-I2 (seal coverage).**
  - `extEuclidCalls` (and `extEuclid`) are defined by well-founded recursion. They are therefore
    irreducible by default and absent from B's seal list. They are read only through
    `extEuclidCalls_of_mod_ne_zero` and `extEuclidCalls_le`.
  - The controls cover one definition per owner. B's other 7 definitions are sealed in C's run, and
    each has an `_eq`, `_iff` or `_spec` reader.
  - Phase 2 adds a reducibility probe for `extEuclidCalls` and NEG/POS pairs for `xgcdLoopStep` and
    `xgcdInvWord`.
- **EFH1-I3 (Euclid machinery).** If `ModPow.lean` later publishes `gcdStep_eq` and the `GcdInv` and
  `gcdMeasure` readers, a round bound through `gcdInv_step` becomes possible. It would not change this
  job's statements. No action.
- **EFH1-I4 (cross-job helpers).** EF-H1's `polyTimeComputable_fromLEPoly_var`,
  `fromLEPoly_var_bits` and `polyTimeComputable_toLE_pair{,FstD,SndD}` are generic `Encoding.BinaryArith`
  glue. EF-R2/R3 composes the same pieces inline.
  - **Recommendation.** A ledger follow-up, as in EF-D1-W2: at the next shared-file window, promote them
    to `Encoding/BinaryArith.lean` and re-point both jobs.
  - **Not now.** That file is frozen for wave 1.
- **EFH1-I5 (overlay file ownership).**
  - `Candidates/Arithmetic.lean` is a Pass–shelat ch. 2–4 file, owned by this maintainer.
  - `Complexity/Randomized/Primality{,Math}.lean` are Complexity files: read-only for wave 1, and owned
    elsewhere.
  - No remote head has changed any of the three since its merge base with REC, and none is in S2-A's
    scope. So adding the readers carries no textual conflict risk.
- **EFH1-I6 (worker's question W2, PFR).** The root `TCSlib` was not elaborated because the PFR oleans
  are missing (the same as EFD1-F05). Phase 2 on snapshot #11, which has the PFR oleans, closes it. No
  exception to the `lake build` ban is needed.
- **EFH1-I7 (trailers).** The worker's commits carry the worker's own `Claude-Session` trailer
  (`session_01PqpVTmt1X8tSZsuU89aou6`). As in earlier landings, the cherry-picks keep the messages
  verbatim. The overlay commits' subjects begin "SCOPE REQUEST"; if they land, reword them as landing
  edits.

## Phase 2 plan (Lean; one job, after a slot frees)

Run it under the snapshots recipe, exactly as `EF-D1/final-r1/phase2.md`. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

**Rules for the run:**
- One Lean process at a time (`runner.py`/`runner_full.py` are sequential), at most 3 on the host. Log
  the slot counts at the start of each phase.
- No `lake build`, no cache get.
- Wait only on this job's own PIDs.
- Never touch the other `olean-replay-*` directories or `olean-snapshot-10`.
- **Disk.** It had 3.6 GB free at phase-1 time. Check for at least 2 GB free before the copy, and stop
  if there is less.

**Steps:**

- **P2-0 Inputs.**
  - Snapshot #11 is `$SP/olean-snapshot`. Its map `olean-snapshot.map-bff0567b.tsv` must be
    `e7bb03b4…` (checked in phase 1) and its files manifest `olean-snapshot.files-bff0567b.txt`.
  - Run `snapmap.py verify` before the copy: it must give 0/0/0.
  - The recipe tools come from `olean-advance-a6d01b1b/tools-used/`, extracted fresh, as for EF-D1.
  - Confirm the records tip is Lean-equal to `bff0567b`, with `git diff --name-only bff0567b <tip>`
    over `TCSlib`, `TCSlib.lean`, `audits`, the lake files and `lean-toolchain`.
- **P2-1 Scratch merges** (never pushed). Use a sparse detached worktree at `bff0567b`; REC is an
  ancestor of `bff0567b`, so the merge is a plain stack.
  - **Head A (series).** Unsigned cherry-picks of the 5 commits. Its tree must equal
    **`16371c0ea7693881d33d20b15996cf66214aa717`** (`git merge-tree --write-tree 0a73fc9c bff0567b`).
  - **Head B (series + overlay).** Head A plus the 2 overlay commits. Its tree must equal
    **`050a20b11c84c9380ff1650aeb80f51ea02debb6`**.
  - **The diffs against `bff0567b`.** For A, exactly the 4 delivery files. For B, also
    `Candidates/Arithmetic.lean` and `Randomized/Primality{,Math}.lean`.
- **P2-2 Replay A.**
  - `cp -al $SP/olean-snapshot $SP/olean-replay-efh1`, then `mloverlay.sh` and `mathlibextra.sh` as
    the recipe requires.
  - Export Head A's tree with `git archive`.
  - Run `stateplan init` at `bff0567b`, then `downorder.py`, `fullorder.py` (roots `TCSlib` and both
    `Checks`) and `stateplan plan`.
  - **Expected:** 6 to build (the 3 new modules, the facade, the root `TCSlib` and
    `audits/pass-shelat/Checks`; my static import count on tree `16371c0e`). Everything else is
    reused.
  - **Pass:** all rc 0; 0 `error:`/`error(`; 0 `sorry`; `permod.py` clean.
  - **Accept:** `stateplan update`, then `check` over the full order.
- **P2-3 Replay B,** on a second copy `$SP/olean-replay-efh1-ovl`, so A's accepted state stays intact.
  - **Expected:** 76 to build. That is the 7 changed modules and their 69 downstream modules, including
    the root and both `audits/*/Checks`, from my static count on tree `050a20b1`. Every downstream
    module of `Arithmetic.lean` and the two `Primality` files is included.
  - **Pass:** the same criteria as A. **This closes F01 and F02.**
- **P2-4 Axioms and probes.** Run them through `runner_full.py` (`-DmaxErrors=0`, no `-o`).
  - **`AxiomsHead`** on A: all stored constants of the 3 new modules, plus a `sorry` control. It must
    find 0 non-standard axioms, and the control must report `sorryAx`.
  - **The same on B,** adding the 9 owner-file readers and the 13 overlay targets.
  - **On B, re-run the delivered `H1P2.lean` unchanged.** On A, run the same file; it must fail only on
    `ofPrimesInP` and `arithmeticFP_iff_primesInP`, which shows that the series alone does not
    discharge the bundle.
  - **Re-run `H1P1.lean` on A** and compare its output with the delivered log, byte for byte.
  - **I2 probes:**
    - `#eval Lean.getReducibilityStatus` for `NumberTheory.extEuclidCalls` and `extEuclid`, plus an
      `example : extEuclidCalls 3 2 = 1 := rfl` that is expected to fail;
    - NEG/POS control pairs for `xgcdLoopStep` (`xgcdLoopStep_eq`) and `xgcdInvWord`
      (`xgcdInvWord_spec`).
- **P2-5 Seals.**
  - **Canonical coe-A with the recipe harness** (`mkcollect`, `mkseals_coe`, `sealsum`) on the 3 new
    owners, at A and at B. Each must give 0 errors.
  - **The delivered paired controls,** re-run at A. Expect exactly NEG1–NEG4 sealed and 0 unsealed.
  - **At B, two control changes:**
    - NEG4's body read still fails sealed, and a new POS4' (`mulStr_eq z`) passes sealed;
    - add NEG/POS pairs for `PRIMESBin` and `PRIMES` with `mem_PRIMESBin` and `mem_PRIMES`.
- **P2-6 Lint.** Run `campaign_style_lint.py --check8b` on both exports. Expected: 92 FAIL / 103 WARN,
  with line sets equal to `bff0567b`'s, and `style_lint.py` on the 7 B files.
- **P2-7 Snapshot.** `snapmap.py verify` must give 0/0/0 after each build and at the end. Keep
  `$SP/olean-replay-efh1` for the PR gate. Delete `-ovl` after the verdict, unless EF-W1-R (A) makes B
  the landing head.
- **P2-8 Landing (after the verdict and EF-W1-R).**
  - **Branch.** `land/ef-h1-arith` from the records branch, with maintainer-signed cherry-picks of the
    5 commits and messages kept verbatim (I7).
  - **Landing edits:** F04(b), F05 and F06.
  - **Under EF-W1-R (A):** S1–S7 and R2's seven field theorems as maintainer landing edits; F06's
    facade text. `Randomized/Primality{,Math}` readers go in an owner PR; the `PRIMESBin` bridge,
    `ofPrimesInP` and the iff follow as one commit after it merges.
  - **Draft PR.** If any landing edit changes Lean, re-run P2-2 to P2-6 on the changed files first.

## Questions for Seyoon (recommended option first)

- **EF-W1-R (joint: EF-H1-W1, EF-D1-R1, EF-H12-W1). Where do missing one-line readers of frozen files
  go?**
  - **The situation.** Three wave-1 jobs hit the same E-SCOPE and solved it three ways.
    - **EF-D1:** a hypothesis (`CenteredSampleEq`), with 2 `rfl` readers proposed for
      `LWE/BitNoise.lean`.
    - **EF-H12:** 27 `rfl`/`Iff.rfl` readers of Complexity files and `NP.lean`, stated in a quarantined
      `LevinHardness/Bridge.lean` inside the job. The worker cites a "readers in our files" ruling that
      `wave1/rulings.md` does not record; decision-log row 903 says it is still to confirm.
    - **EF-H1:** no exception in the series. A separate overlay edits the owner files directly (7
      readers in `Candidates/Arithmetic.lean`, 2 in `Complexity/Randomized/Primality{,Math}.lean`) and
      adds the 13 dependent declarations.
  - **(A, recommended) Readers go into their owner files, never into a job file, routed by owner.**
    - **Our own campaign file, in no open PR and not in S2-A scope**
      (`Candidates/Arithmetic.lean`, `LWE/BitNoise.lean`): the maintainer adds the readers as a
      **landing edit on the job's PR**, using the worker's text, and the dependent declarations land in
      the same PR.
      - EF-H1: S1–S7 plus R2's `polyTimeComputable_{mul,add,sub,divMod,modExp,le,xgcd}Str`.
      - EF-D1: EF-D1-R1 (A).
    - **A file under `TCSlib/Complexity/**`, or another campaign's file:** one small owner PR per owner,
      filed now from the workers' tables. The dependent declarations follow once it merges.
      - EF-H1: `mem_PRIMES` and `mem_PRIMESBin`, then the bridge, `ofPrimesInP` and
        `arithmeticFP_iff_primesInP`.
      - EF-H12: its table, then delete `Bridge.lean` and re-point one-for-one.
    - *Why:* Rule 10 wants readers beside their definitions. A bridge file publishes a second name for
      each fact, and needs a dedup pass once the owner adds its own. Landing edits to files we own cost
      one replay.
    - *Why the wait costs nothing for EF-H1:* EF-H1's headline `ofPrimesInP` has no consumer before
      EF-H2, which waits for S2-A (ruling Q11 A).
  - **(B) Quarantined bridge files (EF-H12's pattern) in every job,** as a recorded, time-boxed Rule-10
    exception, deleted when owner readers land. EF-H1 would resubmit with the nine readers in a new
    `Candidates/ArithmeticBridge.lean`; EF-D1 would add a `BitNoise` bridge.
  - **(C) Owner PRs only, including for our own files.** The jobs land as delivered (EF-H1: re-paired
    forms only, no `ofPrimesInP`; EF-D1: the hypothesis form), and follow-ups complete the targets
    after each owner PR.
  - **(D) Inline Rule-10 exceptions** (`rfl` reads of foreign bodies in the new files). Not recommended:
    it defeats the seals.
- **EF-H1-R2 (only if EF-W1-R is (A) and the Complexity owners decline or delay `mem_PRIMES` and
  `mem_PRIMESBin`).**
  - **(A, recommended) Wait.** Land the series with S1–S7 and the seven field theorems now. The
    `PRIMESBin` bridge, `ofPrimesInP` and the iff wait for the owner PR (no consumer before EF-H2).
  - **(B)** A two-line quarantined bridge for those two readers only (EF-W1-R (B) in miniature).
  - **(C)** Restate `PrimesInP` reader-free as `{x | (bitsVal x).Prime} ∈ Complexity.P`. This departs
    from Q-H1-1 A's literal `PRIMESBin ∈ P` and loses the link to `inCoRP_PRIMESBin`. Not recommended.
- **EF-H1-W2 (the worker's question; PFR root gap).**
  - **(A, recommended)** Closed by phase 2 on snapshot #11, which has the PFR oleans, as EFD1-F05 was.
    No exception to the `lake build` ban.
  - (B) Authorize a narrowed PFR build for wave-1 fills.
- **EF-H1-W3 (the worker's question; anchors).**
  - **(A, recommended)** Accept [AB09] block `p003-b004` (the §7.2 opening; the ingested draft numbers
    it 7.2.1, while TCSlib cites the published §7.2.2) and [PS10, p. 33 and §2.6.5]. Correct the
    chapter-notes anchor to **`p017-b002`**: neither the brief's nor the worker's `b001` is right
    (F04a). Records only; no Lean change.
  - (B) Keep the brief's anchors.

**Not yet clear to merge.** Phase 2 has not run. EF-W1-R is open. Without it, the series lands only the
re-paired forms, `sizeStr` and `PrimesInP`, not the `ArithmeticFP` split.
