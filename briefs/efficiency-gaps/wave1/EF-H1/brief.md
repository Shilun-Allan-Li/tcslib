# EF-H1 · Discharge 8 `ArithmeticFP` fields; `ArithmeticFP` from `PrimesInP`

**Unit** `ef-h1-arith` · **Route** Claude fill (lead, up to 2 sub-agents on disjoint files) ·
**Base** REC `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62` · **Size** 900–1,600 new Lean lines (±40%) ·
**Rulings** Q5 A (discharge 8 fields incl. `xgcd`; split so only `PrimesInP` remains), Q11 A (start now,
new files only; re-threading consumers is EF-H2, held until S2-A merges).

Read `../COMMON.md` first; it is part of this brief.

## Scope

`Candidates.ArithmeticFP` (`TCSlib/Cryptography/Candidates/Arithmetic.lean:314`) is the D11 hypothesis
bundle of nine `PolyTimeComputable` fields. It conditions 25 honest-algorithm rows and 10 reduction rows
(audit §1 item 6; inventory §4.1). This job proves eight of them **unconditionally**, in new files, from
the proved binary arithmetic of `TCSlib/Complexity/ClassP/BinaryArith` and the MSB↔LE adapters of
`Encoding/BinaryArith.lean`, and builds the bundle from the ninth alone:

1. the seven cheap fields: `mul`, `add`, `sub`, `divMod`, `modExp`, `le`, `size`;
2. `xgcd` (gcd and `ZMod` inverse, for **every** modulus);
3. `PrimesInP` (a named `Prop`) and `ArithmeticFP.ofPrimesInP : PrimesInP → ArithmeticFP`, with the
   equivalence `ArithmeticFP ↔ PrimesInP`.

`Arithmetic.lean` and every consumer stay frozen. Re-threading (`H : ArithmeticFP` replaced by the proved
fields or `PrimesInP` in Factoring, RSA, Rabin, DDH, Concrete, DiscreteLog*, ElGamal, the DL hash and BB1)
is EF-H2, after S2-A (J2 owns `Candidates/{Factoring,RSA,Rabin,DDH,Concrete}`).

## The `xgcd` check (maintainer, static): a Fermat inverse does **not** fit the field

The field is `xgcd : PolyTimeComputable xgcdStr` (`Arithmetic.lean:325`), with (`:277`)

```
xgcdStr ⟨a, b⟩ = ⟨ natToList |b| (gcd(⟦a⟧, ⟦b⟧)),
                   natToList |b| (ZMod.val ((⟦a⟧ : ZMod ⟦b⟧)⁻¹)) ⟩
```

for **every** pair of words, composite and degenerate moduli included. A Fermat inverse
`a^{b-2} mod b` agrees with the second component only when `⟦b⟧` is prime (and fails even then at
`⟦b⟧ = 2`, `⟦a⟧ ≡ 0`: `0^0 = 1 ≠ 0 = ZMod.inv 0`), and it does not give the gcd. RSA (`rsaTrapdoor`, the
inverse of `e` modulo `Φ(N)`, a composite) and the unit tests of `RSA.lean:685–730` use the general
form. **So the field needs extended Euclid**; a Fermat route may not stand in for it, and this job adds no
Fermat-inverse lemma (none is needed by any field). The prime-modulus users (B6, B7, BB1) are served by the
general field.

## Targets (proposed; the worker may refine with disclosure)

Namespace `TCSlib.Cryptography.Candidates` throughout.

**File A** `Candidates/ArithmeticDischarge.lean`:
- `theorem polyTimeComputable_mulStr : PolyTimeComputable mulStr`
- `theorem polyTimeComputable_addStr : PolyTimeComputable addStr`
- `theorem polyTimeComputable_subStr : PolyTimeComputable subStr`
- `theorem polyTimeComputable_divModStr : PolyTimeComputable divModStr`
- `theorem polyTimeComputable_modExpStr : PolyTimeComputable modExpStr`
- `theorem polyTimeComputable_leStr : PolyTimeComputable leStr`
- `theorem polyTimeComputable_sizeStr : PolyTimeComputable sizeStr`

**File B** `Candidates/ExtendedEuclidMachine.lean`:
- `theorem polyTimeComputable_xgcdStr : PolyTimeComputable xgcdStr`

**File C** `Candidates/PrimesInP.lean`:
- `def PrimesInP : Prop := Randomized.PRIMESBin ∈ Complexity.P` (Q-H1-1 A; under B,
  `PolyTimeComputable primeStr`), with `theorem primesInP_iff`.
- `theorem polyTimeComputable_primeStr_of_primesInP (h : PrimesInP) : PolyTimeComputable primeStr`
  and its converse `theorem primesInP_of_polyTimeComputable_primeStr` (A only; glue through `toLE`,
  `test_of_mem_P`, `mem_P_of_test`).
- `theorem ArithmeticFP.ofPrimesInP (h : PrimesInP) : ArithmeticFP` (the eight theorems above plus the
  bridge).
- `theorem arithmeticFP_iff_primesInP : ArithmeticFP ↔ PrimesInP`.

The docstring of `PrimesInP` records it as the **standing exception** of ruling Q5 A: a true statement
(AKS), left a named hypothesis because the library has no deterministic primality test; it is not an
axiom and is never used as one.

## Edge cases to settle against Mathlib's definitions (do not trust this list; check each)

- Widths come from input lengths, not values: `mulStr`, `addStr` write at `|a| + |b|`; `subStr` at `|a|`;
  `divModStr` at `|a|` and `|b|`; `xgcdStr` and `modExpStr` at `|b|`, `|N|`. Leading zeros are allowed on
  input; malformed pairs go through the total `pairFstD`/`pairSndD`.
- `⟦b⟧ = 0`: `a / 0 = 0`, `a % 0 = a` written at width `|b|` (truncated low bits). `modExpStr` with
  `⟦N⟧ = 0` writes the low `|N|` bits of `a^x`, i.e. `a^x mod 2^{|N|}`: compute it with
  `BinArith.powMod` at modulus `2^{|N|}` (never materialize `a^x`). `BinArith.powMod` returns `0` at
  modulus `0` (`ModPow.lean`, "Divergences"), which is not `modExpStr`'s value.
- `xgcdStr` at `⟦b⟧ = 0`: `ZMod 0 = ℤ`, `ZMod.inv 0 = Int.sign`, `ZMod.val = Int.natAbs`, so the
  second component is `1` for `⟦a⟧ > 0` and `0` for `⟦a⟧ = 0`, written at width `|b|`; at `⟦b⟧ = 1`
  everything is `0`. For `⟦b⟧ ≥ 1` the inverse is `Nat.gcdA (⟦a⟧ mod ⟦b⟧) ⟦b⟧` cast to `ZMod ⟦b⟧`
  (Mathlib's `ZMod.inv`); a loop that tracks the Bézout coefficient **modulo `⟦b⟧`** along the exact
  `Nat.xgcdAux` recursion computes its residue (the recurrence is linear). Prove the agreement with
  Mathlib's `Nat.xgcd`/`Nat.gcdA`, not with a private re-definition.
- `sizeStr w = 1^{Nat.size ⟦w⟧}`: `(Nat.bits N).length = Nat.size N` (Mathlib), and `toLE w` is
  `Nat.bits ⟦w⟧` (`toLE_eq_natBits`), so `sizeStr` is a constant map over `toLE w`.

## Sources

- [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010: Algorithm 43.2 and
  Claims 43.3, 44.5 (extended Euclid, its call bound and correctness), Algorithm 45.5 and Theorem 45.6
  (modular exponentiation), p. 33 remark (AKS), §2.6.1–§2.6.6 — the anchors `Arithmetic.lean` and
  `NumberTheory/Euclid.lean` already cite (`pass-shelat-2010-ch2` ingested).
- [AB09] Arora–Barak, ch. 7 (ingested `arora-barak-ch07-randomized-computation`): §7.2.2 opening
  ("Agrawal–Kayal–Saxena later gave a deterministic polynomial-time algorithm", around anchor
  `pdf-26d95080dbde-p003-b003`) and the chapter notes ("later AKS proved PRIMES ∈ P", around
  `pdf-26d95080dbde-p017-b001`); confirm the exact block. Also §7.2 and Exercise 7.3, as
  `ClassP/BinaryArith.lean` cites them, for the machines.
- Everything else is Glue (representation adaptation), cited as such.

## Must reuse

- `Complexity.BinArith`: `add`/`sub` (`AddSub.lean:141`, `:144`; `polyTimeComputable_add` `:162`,
  `_sub` `:239`), `le`/`lt` (`:186`, `:183`; `:219`, `:211`), `mul` (`Mul.lean`), `div`/`mod`
  (`Div.lean:52`, `:55`; `:230`, `:245`), `powMod` (`ModPow.lean:52`, `:214`), `gcd` (`:257`, `:348`),
  their public readers `*_pairEncode`, `polyTimeComputable_iterate` (`Iterate.lean:190`) with
  `iterate_invariant`/`iterate_measure_eq_zero`, and Euclid's potential `GcdInv`, `gcdMeasure`,
  `gcdInv_step` (`ModPow.lean:279–306`) for the round bound of the xgcd loop.
- `Encoding.BinaryArith`: `toLE`, `toLE_eq_natBits`, `bitsVal_toLE`, `normalizeWidthPoly`, `fromLEPoly`,
  `fromLEPoly_pairEncode` and their `polyTimeComputable_*` (`Encoding/BinaryArith.lean`).
- `Candidates` readers: `mulStr_pairEncode` and the other `*_pairEncode`/`*_natToList` lemmas of
  `Arithmetic.lean`, `listToNat_natToList`, `natToList_mod_two_pow`.
- `NumberTheory/Euclid.lean`: `extEuclid_spec`, `extEuclid_inv`, `extEuclidCalls_le` ([PS10, Claim 43.3]),
  if the loop follows the text's recursion; otherwise Mathlib's `Nat.gcd_eq_gcd_ab`, `Nat.xgcd` lemmas.
- `Randomized.PRIMESBin` (`TCSlib/Complexity/Randomized/Primality.lean:63`), `test_of_mem_P`,
  `mem_P_of_test` (`TCSlib/Complexity/ClassNP/PClosure.lean:82`, `:75`).
- Precedent for the composition style: `Encoding/DyadicArithmetic.lean` (`addPoly`, `mulPoly`, `subPoly`).

## Duplication sweep (maintainer, static, at `b1219429` and IO `5ed465f6`)

- `PolyTimeComputable (mulStr|addStr|subStr|divModStr|xgcdStr|modExpStr|leStr|sizeStr|primeStr)`: only the
  field declarations (`Arithmetic.lean:316–333`) and `polyTimeComputable_samplePrimeL (hP : …primeStr)`
  (`Factoring.lean:1117`). **No discharge exists**; no `ArithmeticFP` value is constructed anywhere
  (`ArithmeticFP.mk`, `: ArithmeticFP :=`: none).
- Extended Euclid: `NumberTheory/Euclid.lean` (`extEuclid`, mathematical, with the call bound) and
  Mathlib's `Nat.xgcd`; **no machine** computes Bézout coefficients or `ZMod.inv` (grep `gcdA|xgcd`: only
  docstrings and `xgcdStr` consumers). `BinArith.gcd` computes the gcd only.
- `PrimesInP`, `PRIMES ∈ P`: no such declaration (only `inCoRP_PRIMESBin`, `PRIMESBin_mem_BPP_PTM`).
- Near-relatives to disclose, not copy: on IO, `CoinSampling/Efficiency.lean` has **private** readers
  `binArith_{lt,sub,mod}_pairEncode` on words (not on this base). Use BinArith's public `*_pairEncode`
  readers (on `Nat.bits` inputs, `AddSub.lean:147–206`, `Div.lean:58–62`) with `toLE_eq_natBits`; do not
  re-create word-level readers privately (GF-F02). If a word-level reader is truly needed, request it.
- Name check: `ArithmeticDischarge`, `ExtendedEuclidMachine`, `PrimesInP`, `ofPrimesInP` are unused on
  every remote branch (scan of all 280 remote heads, 2026-11-18).

## Files (create or change only these)

| File | Kind |
|---|---|
| `TCSlib/Cryptography/Candidates/ArithmeticDischarge.lean` | new |
| `TCSlib/Cryptography/Candidates/ExtendedEuclidMachine.lean` | new |
| `TCSlib/Cryptography/Candidates/PrimesInP.lean` | new (imports A and B) |
| `TCSlib/Cryptography/Candidates.lean` | facade: three imports and `## Contents` entries |

**Disjointness check (maintainer, mechanical).** None of the four paths is an owner file of
`cleanup-stage2/scope.tsv` or `s2a-items.tsv` (203 owner paths; J2's Candidates files are `Concrete`,
`DDH`, `Factoring`, `RSA`, `Rabin`), none is changed on `cleanup/stage2-s2a` (head `c119a3c4…`, 26 Lean
paths), none is touched by #376 (`LWE/BitEncoding.lean`) or #377 (head `7563734a…`: GSW, `LWE.lean`,
`LWE/Ratio.lean`), and none is under any `complexity/arora-barak-*` or `codex/ab34-*` diff. Imported
read-only files that others are changing: `ClassP/BinaryArith/{Div,ModPow,Mul}` (touched on the Arora–Barak
ch. 3–4 branch) and `Randomized/PPT.lean` (S2-A, proof-level); replay risk only, handled at landing.

## Checks and evidence (in addition to COMMON C1–C13)

- **H1-P1 probes** (kernel `decide` where it reduces, else `#eval` as evidence): each of the eight string
  functions against its BinArith composition on all pairs of words of length ≤ 4, including malformed
  pairs and zero moduli; `xgcdStr` on `⟦b⟧ ∈ {0, 1, 2, 4, 6, 9, 12}`.
- **H1-P2 consumer smoke test** (probe file, not library): `ArithmeticFP.ofPrimesInP h` elaborates where a
  consumer expects `H : ArithmeticFP`, e.g. `fun h => Candidates.dlHash_crh … (ArithmeticFP.ofPrimesInP h)`
  or any `*_oneWay` headline, by `example`.
- **C5** must show standard axioms for all eight field theorems and for `ofPrimesInP`.

## Size

Cheap fields 500–900 (seven compositions with widths and edge cases); `xgcd` 300–600 (a loop with
invariant, potential and the Mathlib agreement); `PrimesInP` and the split 80–150. Total 900–1,600.

## Questions for Seyoon

**Q-H1-1. Form of `PrimesInP`.**
- **A (recommended).** `Randomized.PRIMESBin ∈ Complexity.P`: the literal "PRIMES ∈ P" in the library's
  language form, which is what AKS proves; the bridge to `primeStr` (MSB, `listToNat`) is proved here.
- **B.** `PolyTimeComputable primeStr`: the field verbatim, no bridge.
