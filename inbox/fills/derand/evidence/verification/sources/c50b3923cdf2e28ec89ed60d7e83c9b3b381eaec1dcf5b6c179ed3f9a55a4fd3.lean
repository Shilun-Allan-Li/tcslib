/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.PrimalityMath
import TCSlib.Complexity.Randomized.PTMEquiv
import TCSlib.Complexity.ClassP.BinaryArith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Solovay–Strassen: `PRIMES ∈ coRP`

The class half of [AB09, §7.2.2]: the Solovay–Strassen test is a polynomial-time verifier, so
`PRIMES ∈ coRP` (its complement, the words whose value is not prime, is in `RP`), hence
`PRIMES ∈ BPP`, both in the certificate form over `Randomized.polyTimeModel` and in the PTM
form of [AB09, Def 7.2/7.6].
The error analysis is `TCSlib.Complexity.Randomized.PrimalityMath`; the arithmetic is
`TCSlib.Complexity.ClassP.BinaryArith`.

## Main definitions

* `Randomized.PRIMESBin` — `PRIMES` as a language of binary words.
* `Randomized.compositeVerifier` — the test with two rounds on `|x| + 3`-bit blocks.
* `Randomized.liarRound`, `Randomized.compositeTest` — their word-level implementations.

## Main results

* `Randomized.eff_compositeVerifier` — the verifier is polynomial-time.
* `Randomized.inCoRP_PRIMESBin`, `Randomized.inBPP_PRIMESBin` — certificate form.
* `Randomized.PRIMESBin_mem_coRP_PTM`, `Randomized.PRIMESBin_mem_BPP_PTM` — PTM form.

## Divergences

* `N` is written little-endian and read by `Complexity.LogProg.bitsVal`; every word is
  accepted as a representation, trailing zeros (leading zeros of `N`) included. The class is
  the same for the canonical encoding (`Nat.bits N`): canonical words form a language in `P`,
  and the canonical-encoding language is the intersection of `PRIMESBin` with it.
* The book assumes `N` odd; the verifier decides `N < 2`, `N = 2` and even `N`
  deterministically before the test.
* Two rounds of the test (`Randomized.eulerLiarRounds`) on `ℓ = |x| + 3` random bits each, so
  that `8N ≤ 2^ℓ` and the error is at most `1/3`; the remaining random bits of the
  `6(|x|+1)`-bit string are ignored.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity Turing
open Complexity.LogProg (bitsVal bitsVal_bits)

/-! ### The language and the verifier -/

/-- `PRIMES` as a language: the binary words (little-endian) whose value is prime.
[AB09, §7.2.2, p.128] -/
def PRIMESBin : Language Bool := {x | bitsVal x ∈ PRIMES}

/-- The Solovay–Strassen verifier for the non-primes: accept (`N` is not prime) when `N < 2`,
when `N > 2` is even, or when one of two rounds on `|x| + 3`-bit blocks of `r` finds a
witness. [AB09, §7.2.2, p.128] -/
def compositeVerifier (x r : List Bool) : Bool :=
  if bitsVal x < 2 then true
  else if bitsVal x = 2 then false
  else if bitsVal x % 2 = 0 then true
  else !eulerLiarRounds (bitsVal x) (x.length + 3) 2 r

/-! ### Word-level implementation -/

/-- One round on `⟨N, w⟩`: `A := 1 + (w mod (N − 1))`, then test `gcd(A, N) = 1` and
`(A/N) mod N = A^{(N−1)/2} mod N` with the binary arithmetic of `Complexity.BinArith`. -/
def liarRound (z : List Bool) : Bool :=
  let N := pairFstD z
  let N₁ := BinArith.sub (pairEncode N [true])
  let A := BinArith.add (pairEncode [true] (BinArith.mod (pairEncode (pairSndD z) N₁)))
  BinArith.beq (pairEncode (BinArith.gcd (pairEncode A N)) [true]) &&
    BinArith.beq (pairEncode (BinArith.jacobiModAlg (pairEncode A N))
      (BinArith.powMod (pairEncode A (pairEncode (N₁.drop 1) N))))

/-- A round is polynomial-time. -/
theorem polyTimeComputable_liarRound : PolyTimeComputable (fun z => [liarRound z]) := by
  have hN : PolyTimeComputable pairFstD := polyTimeComputable_pairFstD
  have hN₁ : PolyTimeComputable (fun z => BinArith.sub (pairEncode (pairFstD z) [true])) :=
    BinArith.polyTimeComputable_sub.comp (hN.pairEncode (polyTimeComputable_const _))
  have hA : PolyTimeComputable (fun z => BinArith.add (pairEncode [true]
      (BinArith.mod (pairEncode (pairSndD z) (BinArith.sub (pairEncode (pairFstD z) [true])))))) :=
    BinArith.polyTimeComputable_add.comp ((polyTimeComputable_const _).pairEncode
      (BinArith.polyTimeComputable_mod.comp (polyTimeComputable_pairSndD.pairEncode hN₁)))
  exact polyTimeComputable_and
    (BinArith.polyTimeComputable_beq.comp ((BinArith.polyTimeComputable_gcd.comp
      (hA.pairEncode hN)).pairEncode (polyTimeComputable_const _)))
    (BinArith.polyTimeComputable_beq.comp ((BinArith.polyTimeComputable_jacobiModAlg.comp
      (hA.pairEncode hN)).pairEncode (BinArith.polyTimeComputable_powMod.comp
        (hA.pairEncode ((polyTimeComputable_tail.comp hN₁).pairEncode hN)))))

/-- For odd `N > 1`, a round on `⟨bits N, w⟩` tests whether `eulerSample N w` is an Euler
liar.

**Proof sketch.** Evaluate the arithmetic on encoded numbers: `N − 1`, then
`A = 1 + (w mod (N − 1)) = eulerSample N w`, the gcd, `A^{(N−1)/2} mod N` (halving by dropping
the low bit), and `(A/N) mod N` (`N` odd). The comparisons are then the two conditions of
`isEulerLiar_iff_emod`, the Jacobi residue being a nonnegative integer. -/
theorem liarRound_pairEncode {N : ℕ} (hN : 1 < N) (hodd : Odd N) (w : List Bool) :
    liarRound (pairEncode (Nat.bits N) w) = decide (IsEulerLiar N (eulerSample N w)) := by
  have hsub : BinArith.sub (pairEncode (Nat.bits N) [true]) = Nat.bits (N - 1) := by
    simp [BinArith.sub, bitsVal_bits, bitsVal]
  have hA : BinArith.add (pairEncode [true] (BinArith.mod (pairEncode w (Nat.bits (N - 1))))) =
      Nat.bits (eulerSample N w) := by
    simp [BinArith.add, BinArith.mod, eulerSample, bitsVal_bits, bitsVal]
  have hpow : ∀ A : ℕ, BinArith.powMod (pairEncode (Nat.bits A)
      (pairEncode ((Nat.bits (N - 1)).drop 1) (Nat.bits N))) =
      Nat.bits (A ^ ((N - 1) / 2) % N) := by
    intro A
    simp only [BinArith.powMod, pairFstD_pairEncode, pairSndD_pairEncode,
      BinArith.bitsVal_drop_one, bitsVal_bits]
    simp [show N ≠ 0 by omega]
  simp only [liarRound, pairFstD_pairEncode, pairSndD_pairEncode, hsub, hA, hpow,
    BinArith.gcd_pairEncode, BinArith.jacobiModAlg_pairEncode _ _ hodd]
  have h1 : bitsVal [true] = 1 := rfl
  rw [Bool.eq_iff_iff, decide_eq_true_iff, isEulerLiar_iff_emod]
  have hnn : 0 ≤ jacobiSym (eulerSample N w) N % (N : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast (show N ≠ 0 by omega))
  simp only [BinArith.beq, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_bits, h1,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← Int.toNat_of_nonneg hnn, h2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, Int.toNat_natCast]⟩

/-- The verifier on `⟨x, r⟩`, assembled from polynomial-time pieces: the case split on
`N = bitsVal x`, then two rounds on the blocks `r.take (|x|+3)` and
`(r.drop (|x|+3)).take (|x|+3)`. -/
def compositeTest (z : List Bool) : Bool :=
  let N := Nat.bits (bitsVal (pairFstD z))
  let u := pairFstD z ++ [true, true, true]
  if BinArith.lt (pairEncode N [false, true]) then true
  else if BinArith.beq (pairEncode N [false, true]) then false
  else if !(pairFstD z).headD false then true
  else !(liarRound (pairEncode N (takePrefixByLen (pairEncode u (pairSndD z)))) &&
    liarRound (pairEncode N (takePrefixByLen (pairEncode u
      (dropPrefixByLen (pairEncode u (pairSndD z)))))))

/-- The implementation is polynomial-time.

**Proof sketch.** Normalization, appending three bits, the prefix operations
`takePrefixByLen`/`dropPrefixByLen`, the comparisons and the rounds are polynomial-time;
three nested `polyTimeComputable_ite` assemble the case split. -/
theorem polyTimeComputable_compositeTest :
    PolyTimeComputable (fun z => [compositeTest z]) := by
  have hN : PolyTimeComputable (fun z => Nat.bits (bitsVal (pairFstD z))) :=
    BinArith.polyTimeComputable_normBits.comp polyTimeComputable_pairFstD
  have hu : PolyTimeComputable (fun z => pairFstD z ++ [true, true, true]) :=
    polyTimeComputable_pairFstD.append (polyTimeComputable_const _)
  let two : List Bool := [false, true]
  have hb1 :=
    polyTimeComputable_takePrefixByLen.comp (hu.pairEncode polyTimeComputable_pairSndD)
  have hb2 := polyTimeComputable_takePrefixByLen.comp (hu.pairEncode
    (polyTimeComputable_dropPrefixByLen.comp (hu.pairEncode polyTimeComputable_pairSndD)))
  have h := polyTimeComputable_ite
    (BinArith.polyTimeComputable_lt.comp (hN.pairEncode (polyTimeComputable_const two)))
    (polyTimeComputable_const [true]) (polyTimeComputable_ite
      (BinArith.polyTimeComputable_beq.comp (hN.pairEncode (polyTimeComputable_const two)))
      (polyTimeComputable_const [false]) (polyTimeComputable_ite
        (polyTimeComputable_not (polyTimeComputable_headD.comp polyTimeComputable_pairFstD))
        (polyTimeComputable_const [true]) (polyTimeComputable_not (polyTimeComputable_and
          (polyTimeComputable_liarRound.comp (hN.pairEncode hb1))
          (polyTimeComputable_liarRound.comp (hN.pairEncode hb2))))))
  convert h using 1
  funext z
  dsimp only [compositeTest, Function.comp]
  split_ifs <;> rfl

/-- The implementation computes the verifier.

**Proof sketch.** The two blocks are `r.take (|x|+3)` and `(r.drop (|x|+3)).take (|x|+3)`,
the three tests read `N < 2`, `N = 2` and the parity of `N` off the low bit, and in the
remaining case `N` is odd and `> 2`, so `liarRound_pairEncode` turns the rounds into the two
conjuncts of `eulerLiarRounds N (|x|+3) 2 r`. -/
theorem compositeTest_pairEncode (x r : List Bool) :
    compositeTest (pairEncode x r) = compositeVerifier x r := by
  have hb1 :
      takePrefixByLen (pairEncode (x ++ [true, true, true]) r) = r.take (x.length + 3) := by
    simp [takePrefixByLen]
  have hb2 : takePrefixByLen (pairEncode (x ++ [true, true, true])
      (dropPrefixByLen (pairEncode (x ++ [true, true, true]) r))) =
      (r.drop (x.length + 3)).take (x.length + 3) := by
    simp [takePrefixByLen, dropPrefixByLen]
  have h2 : bitsVal [false, true] = 2 := rfl
  have hlt : BinArith.lt (pairEncode (Nat.bits (bitsVal x)) [false, true]) =
      decide (bitsVal x < 2) := by
    simp only [BinArith.lt, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_bits, h2]
  have heq : BinArith.beq (pairEncode (Nat.bits (bitsVal x)) [false, true]) =
      decide (bitsVal x = 2) := by
    simp only [BinArith.beq, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_bits, h2]
  have hev : (!x.headD false) = decide (bitsVal x % 2 = 0) := by
    rw [BinArith.bitsVal_mod_two]
    cases x.headD false <;> rfl
  unfold compositeTest compositeVerifier
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, hb1, hb2, hlt, heq, hev,
    decide_eq_true_eq]
  split_ifs with c1 c2 c3
  · rfl
  · rfl
  · rfl
  · have hodd : Odd (bitsVal x) := Nat.odd_iff.2 (by omega)
    rw [liarRound_pairEncode (by omega) hodd, liarRound_pairEncode (by omega) hodd]
    simp [eulerLiarRounds]

/-- **The Solovay–Strassen verifier is polynomial-time.** [AB09, §7.2.2, p.128] -/
theorem eff_compositeVerifier : polyTimeModel.Eff (boolVerifier compositeVerifier) :=
  eff_boolVerifier_of_test polyTimeComputable_compositeTest compositeTest_pairEncode

/-! ### `PRIMES ∈ coRP` -/

/-- **`PRIMES ∈ coRP`** (Solovay–Strassen), certificate form: `COMPOSITES ∈ RP`.
[AB09, §7.2.2, p.128]

**Proof sketch.** Random strings of length `6(|x|+1)`. If `N` is not prime and `N < 2` or `N`
is even (`≠ 2`), the verifier always accepts. If `N` is odd composite, it accepts unless both
rounds pass; these read only the first `2ℓ ≤ 6(|x|+1)` bits (`randProb_take`), and since
`N < 2^{|x|}` gives `8N ≤ 2^ℓ` for `ℓ = |x| + 3`, both pass with probability `≤ 1/3`
(`randProb_eulerLiarRounds_two_le`). If `N` is prime, it is `2` (rejected) or odd, and every
round passes (`eulerLiarRounds_of_prime`), so the verifier never accepts. -/
theorem inCoRP_PRIMESBin : InCoRP polyTimeModel PRIMESBin := by
  refine ⟨compositeVerifier, 6, 1, eff_compositeVerifier, fun x => ⟨fun hx => ?_, fun hx r => ?_⟩⟩
  · have hx' : ¬ (bitsVal x).Prime := hx
    by_cases hdet : bitsVal x < 2 ∨ bitsVal x % 2 = 0
    · have h2 : bitsVal x ≠ 2 := fun h => hx' (h ▸ Nat.prime_two)
      rw [randProb_congr (B := fun _ => True) (fun r => by
        rcases hdet with h | h <;> simp [compositeVerifier, h, h2]), randProb_true]
      norm_num
    · push_neg at hdet
      have hodd : Odd (bitsVal x) := Nat.odd_iff.2 (by omega)
      have hℓ : 8 * bitsVal x ≤ 2 ^ (x.length + 3) := by
        have := LogProg.bitsVal_lt_two_pow x
        rw [pow_add]
        omega
      have key : randProb (polyLen 6 1 x.length) (fun r => compositeVerifier x r = true) =
          1 - randProb ((x.length + 3) * 2)
            (fun r => eulerLiarRounds (bitsVal x) (x.length + 3) 2 r = true) := by
        rw [← randProb_take (m₁ := (x.length + 3) * 2) (m := polyLen 6 1 x.length)
          (by simp only [polyLen, pow_one]; omega), ← randProb_not]
        exact randProb_congr fun r => by
          simp [compositeVerifier, eulerLiarRounds_two_take, show ¬ bitsVal x < 2 by omega,
            show bitsVal x ≠ 2 by omega, show bitsVal x % 2 ≠ 0 by omega]
      rw [key]
      have := randProb_eulerLiarRounds_two_le (by omega) hodd hx' hℓ
      linarith
  · have hp : (bitsVal x).Prime := not_not.1 hx
    have := hp.two_le
    unfold compositeVerifier
    by_cases h2 : bitsVal x = 2
    · simp [h2]
    · have hodd := Nat.odd_iff.1 (hp.odd_of_ne_two h2)
      simp [show ¬ bitsVal x < 2 by omega, h2, hodd, eulerLiarRounds_of_prime hp h2]

/-- **`PRIMES ∈ BPP`**, certificate form. [AB09, §7.2.2, p.128] -/
theorem inBPP_PRIMESBin : InBPP polyTimeModel PRIMESBin :=
  InCoRP.inBPP_polyTime inCoRP_PRIMESBin

/-- **`PRIMES ∈ coRP`**, PTM form. [AB09, §7.2.2, p.128] -/
theorem PRIMESBin_mem_coRP_PTM : PRIMESBin ∈ coRP_PTM :=
  (mem_coRP_PTM_iff _).2 inCoRP_PRIMESBin

/-- **`PRIMES ∈ BPP`**, PTM form. [AB09, §7.2.2, p.128] -/
theorem PRIMESBin_mem_BPP_PTM : PRIMESBin ∈ BPP_PTM :=
  (mem_BPP_PTM_iff _).2 inBPP_PRIMESBin

end Randomized
