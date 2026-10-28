/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Cryptography.NumberTheory.Primality
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The polynomial-time arithmetic hypothesis bundle

The candidate one-way functions of [PS10, §2.3, §2.7–§2.12] are "easy to compute", "easy to
sample" and their reductions run in polynomial time because binary multiplication, addition,
(truncated) subtraction, division with remainder, the extended Euclidean algorithm
[PS10, Algorithm 43.2], modular exponentiation [PS10, Algorithm 45.5], comparison, the bit
length and primality testing [PS10, §2.6.5, Remark on p. 33 (AKS)] are polynomial-time
computable on binary numerals.
The repository has no machines for binary arithmetic (inventory finding F1), so, by the
campaign's decision (plan `PassShelatChapter2-4Plan.md`, decision log "conditional
candidates", foundation decision D11), these facts are taken as an **explicit hypothesis
bundle** `ArithmeticFP`, never as axioms: every number-theoretic candidate theorem of the
campaign is stated under `H : ArithmeticFP`, and `#print axioms` stays clean.

Conventions. Numbers on tapes are binary numerals, most significant bit first, read by
`TCSlib.Cryptography.NumberTheory.listToNat` (leading zeros allowed) and written in a
prescribed width by `natToList k N` (the `k` low-order bits of `N`, most significant first;
exact when `N < 2^k`). The typed `k`-bit strings `Fin k → Bool` of the experiments are read
by `TCSlib.Cryptography.bitsToNat` and written by `natToBits k N`; the two conventions agree
through `List.ofFn` (`bitsToNat_eq_listToNat`, `natToList`). Arguments of the arithmetic
functions are paired with `Turing.pairEncode`.

**Deviation:** [PS10] treats the arithmetic algorithms as given (§2.6 gives their operation
counts; the `NumberTheory` modules formalize those); here their polynomial-time
computability on strings is a hypothesis, discharged by a future machine-building campaign.

## Main definitions

* `TCSlib.Cryptography.Candidates.natToBits`, `natToList` — fixed-width binary numerals.
* `TCSlib.Cryptography.Candidates.mulStr`, `addStr`, `subStr`, `divModStr`, `xgcdStr`,
  `modExpStr`, `leStr`, `sizeStr`, `primeStr` — the string functions of the bundle
  (`addStr`, `subStr`, `sizeStr` added by the run-3 audit repair P7-1: the reductions of
  §2.9–§2.12 decrement, add and subtract numerals and read bit lengths).
* `TCSlib.Cryptography.Candidates.ArithmeticFP` — the hypothesis bundle (a `Prop`
  structure).

## Main results

* `TCSlib.Cryptography.Candidates.listToNat_natToList`,
  `TCSlib.Cryptography.Candidates.bitsToNat_natToBits`,
  `TCSlib.Cryptography.Candidates.natToBits_bitsToNat` — the encodings are mutually
  inverse on numbers below `2^k`.
* `TCSlib.Cryptography.Candidates.natToBits_injOn` — `natToBits k` is injective below `2^k`.
* `TCSlib.Cryptography.Candidates.listToNat_addStr`,
  `TCSlib.Cryptography.Candidates.listToNat_subStr` — addition and truncated subtraction of
  numerals are lossless at the widths of the bundle.
* `TCSlib.Cryptography.Candidates.val_units_pow` — `(x^e).val = x.val^e mod M` in `Z_M^*`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3 (multiplication), §2.6.1–§2.6.6 (Euclid, modular exponentiation, primality
  testing), Remark on p. 33 (AKS).)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009 (the string-function class FP, `Complexity.PolyTimeComputable`).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory

/-! ## Fixed-width binary numerals -/

/-- The `k`-bit binary numeral of `N`, most significant bit first: bit `i` is the
`(k - 1 - i)`-th binary digit of `N` (the `k` low-order digits of `N`; exact when
`N < 2^k`). The inverse of `TCSlib.Cryptography.bitsToNat` on `Fin k → Bool`. -/
def natToBits (k N : ℕ) : Fin k → Bool := fun i => N.testBit (k - 1 - i)

/-- The `k`-bit binary numeral of `N` as a string (most significant bit first). -/
def natToList (k N : ℕ) : List Bool := List.ofFn (natToBits k N)

/-- `natToList` has length `k`. -/
@[simp] theorem length_natToList (k N : ℕ) : (natToList k N).length = k := by
  simp [natToList]

/-- The `0`-bit numeral is empty (moved from `RSA.lean`, run-3 audit P7-6). -/
theorem natToList_zero (N : ℕ) : natToList 0 N = [] := by simp [natToList]

/-- Dropping the last bit of a `(k+1)`-bit numeral of `N` gives the `k`-bit numeral of
`N / 2`. -/
theorem natToBits_succ_castSucc (k N : ℕ) (i : Fin k) :
    natToBits (k + 1) N (Fin.castSucc i) = natToBits k (N / 2) i := by
  simp only [natToBits, Fin.coe_castSucc]
  have h : k + 1 - 1 - (i : ℕ) = (k - 1 - i) + 1 := by have := i.2; omega
  rw [h, Nat.testBit_succ]

/-- The last bit of a `(k+1)`-bit numeral of `N` is the parity of `N`. -/
theorem natToBits_succ_last (k N : ℕ) : natToBits (k + 1) N (Fin.last k) = N.testBit 0 := by
  simp [natToBits]

/-- `listToNat` of the `k`-bit numeral of `N` is `N mod 2^k` (the numeral keeps the `k`
low-order digits). -/
theorem listToNat_natToList_eq_mod (k N : ℕ) : listToNat (natToList k N) = N % 2 ^ k := by
  induction k generalizing N with
  | zero => simp [natToList, listToNat, Nat.mod_one]
  | succ k ih =>
    rw [natToList, List.ofFn_succ', List.concat_eq_append]
    simp only [natToBits_succ_castSucc, natToBits_succ_last]
    rw [listToNat, List.foldl_concat, ← listToNat, ← natToList, ih, pow_succ', Nat.mod_mul]
    have h0 : (if N.testBit 0 then 1 else 0) = N % 2 := by
      have := Nat.toNat_testBit N 0
      simp only [pow_zero, Nat.div_one] at this
      rw [← this]
      cases N.testBit 0 <;> rfl
    rw [h0]
    omega

/-- **The encodings are inverse** (reading): `listToNat (natToList k N) = N` for `N < 2^k`. -/
theorem listToNat_natToList {k N : ℕ} (h : N < 2 ^ k) : listToNat (natToList k N) = N := by
  rw [listToNat_natToList_eq_mod, Nat.mod_eq_of_lt h]

/-- `bitsToNat` of the `k`-bit numeral of `N` is `N` for `N < 2^k`. -/
theorem bitsToNat_natToBits {k N : ℕ} (h : N < 2 ^ k) : bitsToNat (natToBits k N) = N := by
  rw [bitsToNat_eq_listToNat]
  exact listToNat_natToList h

/-- **The encodings are inverse** (writing): the `k`-bit numeral of `bitsToNat b` is `b`. -/
theorem natToBits_bitsToNat {k : ℕ} (b : Fin k → Bool) : natToBits k (bitsToNat b) = b :=
  bitsToNat_injective (bitsToNat_natToBits (bitsToNat_lt b))

/-- `natToBits k` is injective on numbers below `2^k`. -/
theorem natToBits_injOn {k M N : ℕ} (hM : M < 2 ^ k) (hN : N < 2 ^ k)
    (h : natToBits k M = natToBits k N) : M = N := by
  rw [← bitsToNat_natToBits hM, ← bitsToNat_natToBits hN, h]

/-- `natToList k` is injective on numbers below `2^k`. -/
theorem natToList_injOn {k M N : ℕ} (hM : M < 2 ^ k) (hN : N < 2 ^ k)
    (h : natToList k M = natToList k N) : M = N :=
  natToBits_injOn hM hN (List.ofFn_injective h)

/-- `listToNat` of an `n`-bit string is below `2^n`. -/
theorem listToNat_lt_two_pow (w : List Bool) : listToNat w < 2 ^ w.length := by
  have h := bitsToNat_lt (fun i : Fin w.length => w.get i)
  rw [bitsToNat_eq_listToNat] at h
  simpa using h

/-! ## The string functions of the bundle -/

/-- Binary multiplication: `⟨a, b⟩ ↦ a · b` as an `(|a| + |b|)`-bit numeral (lossless: the
product of an `|a|`-bit and a `|b|`-bit number has at most `|a| + |b|` bits). -/
def mulStr (z : List Bool) : List Bool :=
  natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) * listToNat (pairSndD z))

/-- Binary addition: `⟨a, b⟩ ↦ a + b` as an `(|a| + |b|)`-bit numeral (lossless,
`listToNat_addStr`: `a + b < 2^{|a|} + 2^{|b|} ≤ 2^{|a| + |b|}` when both numerals are nonempty,
and `a + b = b` when `a` is empty). Repair (run-3 audit P7-1): added to the bundle; the
reductions of [PS10, §2.12] add numerals (the CRT sum of Theorem 58.3, the increment
`(p+1)/4`). -/
def addStr (z : List Bool) : List Bool :=
  natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) + listToNat (pairSndD z))

/-- Truncated subtraction: `⟨a, b⟩ ↦ a ∸ b` (`0` when `b > a`) as an `|a|`-bit numeral
(lossless, `listToNat_subStr`). The decrement `p − 1` of `Φ(N) = (p−1)(q−1)` [PS10, p. 47]
is `subStr ⟨p, [true]⟩`, and `(x − z) mod N` is `(x + (N ∸ (z mod N))) mod N`. Repair (run-3
audit P7-1): added to the bundle. -/
def subStr (z : List Bool) : List Bool :=
  natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z))

/-- Bit length: `w ↦ 1^{Nat.size N}` for `N = listToNat w`, the length of the numeral of `N`
with its leading zeros stripped (`Nat.size N = ⌈log₂ (N + 1)⌉`, `N < 2^{Nat.size N} ≤ 2N` for
`N ≥ 1`), written in unary — the form in which lengths drive the cuts
`Complexity.polyTimeComputable_pairTakePoly`. Repair (run-3 audit P7-1): added to the bundle;
the rejection samplers of [PS10, §2.9–§2.12, §3.x] read `k = Nat.size N` bits per trial. -/
def sizeStr (w : List Bool) : List Bool := List.replicate (Nat.size (listToNat w)) true

/-- Division with remainder: `⟨a, b⟩ ↦ ⟨a / b, a mod b⟩`, the quotient as an `|a|`-bit and
the remainder as a `|b|`-bit numeral (Lean's convention `a / 0 = 0`, `a mod 0 = a`). -/
def divModStr (z : List Bool) : List Bool :=
  pairEncode (natToList (pairFstD z).length (listToNat (pairFstD z) / listToNat (pairSndD z)))
    (natToList (pairSndD z).length (listToNat (pairFstD z) % listToNat (pairSndD z)))

/-- The extended Euclidean algorithm [PS10, Algorithm 43.2] in the form the candidates use:
`⟨a, b⟩ ↦ ⟨gcd(a, b), a⁻¹ mod b⟩`, both as `|b|`-bit numerals, where `a⁻¹ mod b` is
`ZMod.inv` (the Bézout coefficient of `a` reduced modulo `b`; the inverse of `a` in `Z_b^*`
when `gcd(a, b) = 1`, [PS10, Claim 44.5 and Theorem 46.8]). -/
def xgcdStr (z : List Bool) : List Bool :=
  pairEncode (natToList (pairSndD z).length (Nat.gcd (listToNat (pairFstD z)) (listToNat (pairSndD z))))
    (natToList (pairSndD z).length
      (ZMod.val ((listToNat (pairFstD z) : ZMod (listToNat (pairSndD z)))⁻¹)))

/-- Modular exponentiation [PS10, Algorithm 45.5]: `⟨a, ⟨x, N⟩⟩ ↦ a^x mod N` as an
`|N|`-bit numeral. -/
def modExpStr (z : List Bool) : List Bool :=
  natToList (pairSndD (pairSndD z)).length
    (listToNat (pairFstD z) ^ listToNat (pairFstD (pairSndD z)) % listToNat (pairSndD (pairSndD z)))

/-- Comparison: `⟨a, b⟩ ↦ [a ≤ b]`. -/
def leStr (z : List Bool) : List Bool :=
  [decide (listToNat (pairFstD z) ≤ listToNat (pairSndD z))]

/-- Primality test: `w ↦ [w is prime]` (the hypothesis of
`TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt`). -/
def primeStr (w : List Bool) : List Bool := [decide (listToNat w).Prime]

/-- **The polynomial-time arithmetic hypothesis bundle** (plan decision "conditional
candidates", D11; inventory items Rem-33.2, Rem-43.6, Rem-48.2 and findings F1/F6):
binary multiplication, addition, truncated subtraction, division with remainder, the
extended Euclidean algorithm [PS10, Algorithm 43.2, Claim 43.3], modular exponentiation
[PS10, Algorithm 45.5, Theorem 45.6], comparison, the bit length and primality testing
[PS10, p. 33 and §2.6.5] are polynomial-time computable on binary numerals
(`Complexity.PolyTimeComputable`).

**Deviation:** [PS10] uses these algorithms freely; the campaign states each candidate
result under this explicit hypothesis instead of building the machines, adding no axiom.

Repair (run-3 audit P7-1): the fields `add`, `sub` and `size` were added — the generators,
samplers and reductions of [PS10, §2.9–§2.12] decrement (`Φ(N) = (p−1)(q−1)`), subtract
modulo `N` (`gcd(x − z, N)`, Algorithm 62.9), add (the CRT root formula, Theorem 58.3) and
read bit lengths (`k = Nat.size N` bits per rejection trial); all three are derivable from
`mul` and `divMod` in principle (`a + b = ((2^{2k} + a)(2^{2k} + b) mod 2^{4k}) / 2^{2k}`, the
bit length by a search with `le`), but that is the machine building the campaign excludes.
Every field is a true statement about a total FP function, so the bundle is satisfiable. -/
structure ArithmeticFP : Prop where
  /-- Binary multiplication is polynomial-time. -/
  mul : PolyTimeComputable mulStr
  /-- Binary addition is polynomial-time (run-3 audit P7-1). -/
  add : PolyTimeComputable addStr
  /-- Truncated binary subtraction is polynomial-time (run-3 audit P7-1). -/
  sub : PolyTimeComputable subStr
  /-- Division with remainder is polynomial-time. -/
  divMod : PolyTimeComputable divModStr
  /-- The extended Euclidean algorithm (gcd and modular inverse) is polynomial-time
  [PS10, Claim 43.3]. -/
  xgcd : PolyTimeComputable xgcdStr
  /-- Modular exponentiation is polynomial-time [PS10, Theorem 45.6]. -/
  modExp : PolyTimeComputable modExpStr
  /-- Comparison of binary numerals is polynomial-time. -/
  le : PolyTimeComputable leStr
  /-- The bit length (in unary) of a binary numeral is polynomial-time (run-3 audit P7-1). -/
  size : PolyTimeComputable sizeStr
  /-- Primality testing is polynomial-time [PS10, p. 33, AKS]. -/
  prime : PolyTimeComputable primeStr

/-! ### Unfolding lemmas -/

/-- `mulStr` on an encoded pair. -/
@[simp] theorem mulStr_pairEncode (a b : List Bool) :
    mulStr (pairEncode a b) = natToList (a.length + b.length) (listToNat a * listToNat b) := by
  simp [mulStr]

/-- `mulStr` on the numerals of `M` and `N` (widths `k` and `l`) is the `(k + l)`-bit numeral
of `M · N`. -/
theorem mulStr_natToList (k l M N : ℕ) (hM : M < 2 ^ k) (hN : N < 2 ^ l) :
    mulStr (pairEncode (natToList k M) (natToList l N)) = natToList (k + l) (M * N) := by
  rw [mulStr_pairEncode, length_natToList, length_natToList, listToNat_natToList hM,
    listToNat_natToList hN]

/-- `addStr` on an encoded pair. -/
@[simp] theorem addStr_pairEncode (a b : List Bool) :
    addStr (pairEncode a b) = natToList (a.length + b.length) (listToNat a + listToNat b) := by
  simp [addStr]

/-- `subStr` on an encoded pair. -/
@[simp] theorem subStr_pairEncode (a b : List Bool) :
    subStr (pairEncode a b) = natToList a.length (listToNat a - listToNat b) := by
  simp [subStr]

/-- `sizeStr w` is the unary bit length of the number read from `w`. -/
@[simp] theorem length_sizeStr (w : List Bool) : (sizeStr w).length = Nat.size (listToNat w) := by
  simp [sizeStr]

/-- The sum of the numbers read from two numerals is below `2^{|a| + |b|}`.

**Proof sketch.** If one numeral is empty it reads as `0` and the claim is
`listToNat_lt_two_pow` of the other; otherwise `a, b ≤ 2^{|a|} − 1, 2^{|b|} − 1` and
`2^{|a|} + 2^{|b|} ≤ 2^{|a|} · 2^{|b|}` since both powers are at least `2`
(`(x − 1)(y − 1) ≥ 1`, `nlinarith`). -/
theorem listToNat_add_lt_two_pow (a b : List Bool) :
    listToNat a + listToNat b < 2 ^ (a.length + b.length) := by
  have ha := listToNat_lt_two_pow a
  have hb := listToNat_lt_two_pow b
  rcases Nat.eq_zero_or_pos a.length with h0 | hpos
  · rw [h0] at ha ⊢
    simp only [pow_zero, Nat.lt_one_iff] at ha
    rw [ha, zero_add, zero_add]
    exact hb
  rcases Nat.eq_zero_or_pos b.length with h0' | hpos'
  · rw [h0'] at hb ⊢
    simp only [pow_zero, Nat.lt_one_iff] at hb
    rw [hb, add_zero, add_zero]
    exact ha
  have h2a : 2 ≤ 2 ^ a.length := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a.length := Nat.pow_le_pow_right (by norm_num) hpos
  have h2b : 2 ≤ 2 ^ b.length := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b.length := Nat.pow_le_pow_right (by norm_num) hpos'
  rw [pow_add]
  nlinarith

/-- **Addition is lossless**: `addStr ⟨a, b⟩` reads back as `a + b`. -/
theorem listToNat_addStr (a b : List Bool) :
    listToNat (addStr (pairEncode a b)) = listToNat a + listToNat b := by
  rw [addStr_pairEncode, listToNat_natToList (listToNat_add_lt_two_pow a b)]

/-- **Truncated subtraction is lossless**: `subStr ⟨a, b⟩` reads back as `a ∸ b`. -/
theorem listToNat_subStr (a b : List Bool) :
    listToNat (subStr (pairEncode a b)) = listToNat a - listToNat b := by
  rw [subStr_pairEncode]
  exact listToNat_natToList (lt_of_le_of_lt (Nat.sub_le _ _) (listToNat_lt_two_pow a))

/-- `leStr` on an encoded pair. -/
@[simp] theorem leStr_pairEncode (a b : List Bool) :
    leStr (pairEncode a b) = [decide (listToNat a ≤ listToNat b)] := by
  simp [leStr]

/-- `modExpStr` on an encoded triple. -/
@[simp] theorem modExpStr_pairEncode (a x N : List Bool) :
    modExpStr (pairEncode a (pairEncode x N)) =
      natToList N.length (listToNat a ^ listToNat x % listToNat N) := by
  simp [modExpStr]

/-- `primeStr` is the primality test of `exists_samplePrime_nuppt`. -/
theorem primeStr_eq : primeStr = fun w : List Bool => [decide (listToNat w).Prime] := rfl

/-- The residue of `x^e` is `x.val^e mod M` for a unit `x` of `Z_M` (any modulus `M ≠ 0`): the
form in which the evaluators `modExpStr` compute the permutations `x ↦ x^e` and `x ↦ x²`
(moved from `RSA.lean`, run-3 audit P7-6). -/
theorem val_units_pow (M : ℕ) [NeZero M] (x : (ZMod M)ˣ) (e : ℕ) :
    ((x ^ e : (ZMod M)ˣ) : ZMod M).val = (x : ZMod M).val ^ e % M := by
  rw [Units.val_pow_eq_pow_val, ← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]

/-- The product of two `k`-bit numbers is below `2^(k + k)`. -/
theorem mul_lt_two_pow_add {k M N : ℕ} (hM : M < 2 ^ k) (hN : N < 2 ^ k) : M * N < 2 ^ (k + k) := by
  rw [pow_add]
  exact Nat.mul_lt_mul'' hM hN

end TCSlib.Cryptography.Candidates
