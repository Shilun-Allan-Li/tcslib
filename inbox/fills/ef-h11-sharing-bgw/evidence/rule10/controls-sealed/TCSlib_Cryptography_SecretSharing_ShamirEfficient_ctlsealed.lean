/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecretSharing.Efficient
import TCSlib.Cryptography.SecretSharing.Sharing
import TCSlib.Complexity.ClassP.BinaryArith.ModPow
import TCSlib.Complexity.ClassP.BinaryArith.Loops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
attribute [local irreducible] Complexity.PolyTimeComputable Complexity.pairFstD Complexity.pairSndD Turing.pairEncode Complexity.BinArith.beq Complexity.BinArith.countW Complexity.BinArith.div Complexity.BinArith.encWords Complexity.BinArith.forLoop Complexity.BinArith.mod Complexity.BinArith.mul Complexity.LogProg.bitsVal Complexity.NUPPT.advInput Complexity.PolyExpr.eval Complexity.PrefixByLength.take TCSlib.SecretSharing.DealerSamples TCSlib.SecretSharing.addModW TCSlib.SecretSharing.invModW TCSlib.SecretSharing.mulModW TCSlib.SecretSharing.resWord TCSlib.SecretSharing.subModW TCSlib.Shamir.poly TCSlib.Shamir.recombine TCSlib.Shamir.scheme TCSlib.Cryptography.Candidates.natToList TCSlib.Cryptography.CoinSampling.SamplesEfficiently TCSlib.Cryptography.CoinSampling.modulusWord TCSlib.Cryptography.CoinSampling.residueEnc TCSlib.Cryptography.NumberTheory.listToNat TCSlib.SecretSharing.AccessStructure.threshold TCSlib.SecretSharing.EfficientScheme.Correct TCSlib.SecretSharing.EfficientScheme.LocalReconstruct TCSlib.SecretSharing.EfficientScheme.PerfectPrivacy TCSlib.SecretSharing.Scheme.Correct TCSlib.SecretSharing.Scheme.LocalReconstruct TCSlib.SecretSharing.Scheme.PerfectPrivacy TCSlib.SecretSharing.Scheme.restrict TCSlib.SecretSharing.ShamirParams.encode TCSlib.Cryptography.Encoding.BinaryArith.fromLEPoly TCSlib.Cryptography.Encoding.BinaryArith.toLE

/-!
# Shamir's scheme over `ℤ_p` as an efficient secret-sharing scheme

[PS10, Prot 154.4]'s `k`-out-of-`n` scheme over `ℤ_p`, as an instance of the efficient interface
`SecretSharing.EfficientScheme`. The typed maps are `Shamir.scheme k (ZMod p)` restricted to the
parties `1, …, n` (`shamirScheme`, through `Scheme.restrict`), so correctness and perfect privacy
are **transferred** from `Shamir.correct`, `Shamir.localReconstruct` and `Shamir.perfectPrivacy`,
not re-proved. The dealer's `k − 1` random coefficients are one uniform residue `r < p^{k−1}`,
read as its base-`p` digits (`coinEquiv`), so that one bucket draw
(`CoinSampling.samplesEfficiently_residue`) samples them exactly.

The machines are built from the residue layer of `SecretSharing.Efficient` (`addModW`,
`subModW`, `mulModW`, `invModW` on `Complexity.BinArith`) and the registered counted loop
`Complexity.BinArith.forLoop` (host H16), with `BinArith.countW` counters:

* `shareRaw`: one party's share, `sec + ∑_{t<k−1} digit_t(r) · x^{t+1}`, one digit per round;
* `recombineRaw`: Lagrange recombination at `0` from a listed set, two nested loops, with
  inverses `x^{p−2}` by Fermat (ruling Q-H11-2);
* `dealerWord`: the bucket sampler's parameter word `p^{k−1}`.

## Main definitions

* `Shamir.coinEquiv`, `Shamir.partyEmb`, `Shamir.shamirScheme`: the coins, the listed parties
  and the typed scheme.
* `Shamir.shareRaw`, `Shamir.recombineRaw`, `Shamir.dealerWord`: the machines.
* `Shamir.shamirAdm`, `Shamir.shamirEfficient`: admissible parameters and the instance.

## Main results

* `Shamir.shamirScheme_correct`, `Shamir.shamirScheme_perfectPrivacy`: transferred.
* `Shamir.shareRaw_spec`, `Shamir.polyTimeComputable_shareRaw`: the share map.
* `Shamir.recombine_toFinset_eq`, `Shamir.recombineRaw_spec`,
  `Shamir.polyTimeComputable_recombineRaw`: reconstruction.
* `Shamir.dealerSamples_shamir`: the dealer's coins are sampled efficiently.
* `Shamir.shamirEfficient_correct`, `Shamir.shamirEfficient_localReconstruct`,
  `Shamir.shamirEfficient_perfectPrivacy`: the instance's security.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979, §2–3.
* [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011, §2.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.1.1–6.1.3 (Definition 152.1, Lemma 153.2, Fact 153.3, Protocol 154.4, Proposition 154.5).
-/

namespace TCSlib.Shamir

open Finset Polynomial Complexity Turing TCSlib.SecretSharing
open Complexity.LogProg (bitsVal bitsVal_bits)

/-! ### The parameters, the coins and the parties -/

/-- Shamir's public parameters carry a prime modulus. -/
instance (π : ShamirParams) : Fact π.p.Prime := ⟨π.prime⟩

/-- **Residues by representatives**: `Fin p ≃ ZMod p`, `a ↦ (a : ℕ)`, inverse `x ↦ x.val`.
Glue; a near-relative of Mathlib's `ZMod.finEquiv`, stated with explicit formulas so that its
values are readable. -/
def finZModEquiv (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun a := ((a : ℕ) : ZMod p)
  invFun x := ⟨x.val, ZMod.val_lt x⟩
  left_inv a := Fin.ext (ZMod.val_cast_of_lt a.2)
  right_inv x := ZMod.natCast_zmod_val x

/-- `finZModEquiv p a = (a : ℕ)`. -/
theorem finZModEquiv_apply (p : ℕ) [NeZero p] (a : Fin p) :
    finZModEquiv p a = ((a : ℕ) : ZMod p) := rfl

/-- `(finZModEquiv p).symm x = x.val`. -/
theorem finZModEquiv_symm_apply_val (p : ℕ) [NeZero p] (x : ZMod p) :
    (((finZModEquiv p).symm x : Fin p) : ℕ) = x.val := rfl

/-- **The dealer's coins as one residue**: `r < p^{k−1}` read as the coefficient polynomial whose
`j`-th coefficient is the `j`-th base-`p` digit `⌊r / p^j⌋ mod p` of `r`
(`finFunctionFinEquiv`, `finZModEquiv`, `Polynomial.degreeLTEquiv`). It turns one uniform draw
from `Fin (p^{k−1})` into uniform coins of `Shamir.scheme`. Glue. -/
noncomputable def coinEquiv (π : ShamirParams) :
    Fin (π.p ^ (π.k - 1)) ≃ degreeLT (ZMod π.p) (π.k - 1) :=
  finFunctionFinEquiv.symm.trans ((Equiv.piCongrRight fun _ => finZModEquiv π.p).trans
    (degreeLTEquiv (ZMod π.p) (π.k - 1)).toEquiv.symm)

/-- `coinEquiv π r = (degreeLTEquiv).symm (j ↦ ⌊r / p^j⌋ mod p)`. -/
theorem coinEquiv_apply (π : ShamirParams) (r : Fin (π.p ^ (π.k - 1))) :
    coinEquiv π r = (degreeLTEquiv (ZMod π.p) (π.k - 1)).symm
      fun j => finZModEquiv π.p (finFunctionFinEquiv.symm r j) := rfl

/-- The coefficients of the coin polynomial are the base-`p` digits of `r`. -/
theorem coeff_coinEquiv (π : ShamirParams) (r : Fin (π.p ^ (π.k - 1))) {j : ℕ}
    (hj : j < π.k - 1) :
    (coinEquiv π r).1.coeff j = ((r / π.p ^ j % π.p : ℕ) : ZMod π.p) := by
  have h := congrFun ((degreeLTEquiv (ZMod π.p) (π.k - 1)).apply_symm_apply
    fun j => finZModEquiv π.p (finFunctionFinEquiv.symm r j)) ⟨j, hj⟩
  rw [finZModEquiv_apply, finFunctionFinEquiv_symm_apply_val] at h
  exact h

/-- The coin polynomial evaluates to `∑_{j < k−1} digit_j(r) · x^j`. -/
theorem eval_coinEquiv (π : ShamirParams) (r : Fin (π.p ^ (π.k - 1))) (x : ZMod π.p) :
    (coinEquiv π r).1.eval x =
      ∑ j ∈ range (π.k - 1), ((r / π.p ^ j % π.p : ℕ) : ZMod π.p) * x ^ j := by
  set q := (coinEquiv π r).1 with hq
  have hdeg : q.degree < ((π.k - 1 : ℕ) : WithBot ℕ) := mem_degreeLT.1 (coinEquiv π r).2
  have hnat : q.natDegree < π.k - 1 + 1 := by
    rcases eq_or_ne q 0 with hq0 | hq0
    · rw [hq0, natDegree_zero]; exact Nat.succ_pos _
    · exact Nat.lt_succ_of_lt ((natDegree_lt_iff_degree_lt hq0).2 hdeg)
  rw [eval_eq_sum_range' hnat, Finset.sum_range_succ, coeff_eq_zero_of_degree_lt hdeg, zero_mul,
    add_zero]
  exact Finset.sum_congr rfl fun j hj => by rw [coeff_coinEquiv π r (Finset.mem_range.1 hj)]

/-- **The listed parties** `1, …, n` of [PS10, Prot 154.4] as parties of `Shamir.scheme`: party
`i : Fin n` is the nonzero residue `i + 1` (nonzero as `i + 1 ≤ n < p`). -/
def partyEmb (π : ShamirParams) : Fin π.n ↪ Party (ZMod π.p) :=
  ⟨fun i => ⟨(((i : ℕ) + 1 : ℕ) : ZMod π.p), fun h => by
      have := congrArg ZMod.val h
      rw [ZMod.val_cast_of_lt (by have := i.2; have := π.n_lt_p; omega), ZMod.val_zero] at this
      omega⟩,
    fun i j h => by
      have := congrArg (fun a : Party (ZMod π.p) => (label a).val) h
      simp only [ZMod.val_cast_of_lt
          (show (i : ℕ) + 1 < π.p by have := i.2; have := π.n_lt_p; omega),
        ZMod.val_cast_of_lt (show (j : ℕ) + 1 < π.p by have := j.2; have := π.n_lt_p; omega)]
        at this
      exact Fin.ext (by omega)⟩

/-- `label (partyEmb π i) = i + 1`. -/
theorem label_partyEmb (π : ShamirParams) (i : Fin π.n) :
    label (partyEmb π i) = (((i : ℕ) + 1 : ℕ) : ZMod π.p) := rfl

/-- The word of party `i`'s label is the numeral of `i + 1`. -/
theorem resWord_label_partyEmb (π : ShamirParams) (i : Fin π.n) :
    resWord (label (partyEmb π i)) = Nat.bits ((i : ℕ) + 1) := by
  rw [label_partyEmb, resWord_natCast_of_lt (by have := i.2; have := π.n_lt_p; omega)]

/-- **Shamir's scheme over `ℤ_p` with the listed parties** `1, …, n` and coins `Fin (p^{k−1})`:
`Shamir.scheme k (ZMod p)` restricted along `partyEmb π` and `coinEquiv π` (`Scheme.restrict`).
This is [PS10, Prot 154.4]'s `n`-party scheme, as the deviation note of `Shamir.scheme` says. -/
noncomputable def shamirScheme (π : ShamirParams) :
    Scheme (Fin π.n) (ZMod π.p) (ZMod π.p) (Fin (π.p ^ (π.k - 1))) :=
  (scheme π.k (ZMod π.p)).restrict (partyEmb π) (coinEquiv π) 0

/-- `shamirScheme π = (scheme k (ZMod p)).restrict (partyEmb π) (coinEquiv π) 0`. -/
theorem shamirScheme_eq (π : ShamirParams) :
    shamirScheme π = (scheme π.k (ZMod π.p)).restrict (partyEmb π) (coinEquiv π) 0 := rfl

/-- Party `i`'s share is `Shamir.scheme`'s share of party `i + 1` with the decoded coins. -/
theorem shamirScheme_share (π : ShamirParams) (sec : ZMod π.p) (r : Fin (π.p ^ (π.k - 1)))
    (i : Fin π.n) :
    (shamirScheme π).share sec r i = (scheme π.k (ZMod π.p)).share sec (coinEquiv π r)
      (partyEmb π i) := by
  rw [shamirScheme_eq, Scheme.restrict_share]

/-- Reconstruction by the listed set `A` is `recombine` over `A`'s parties, of any share
assignment agreeing with `f` there. -/
theorem shamirScheme_reconstruct (π : ShamirParams) (A : Finset (Fin π.n)) (f : Fin π.n → ZMod π.p)
    (g : Party (ZMod π.p) → ZMod π.p) (hfg : ∀ i ∈ A, g (partyEmb π i) = f i) :
    (shamirScheme π).reconstruct A f = recombine (A.map (partyEmb π)) g := by
  rw [shamirScheme_eq, Scheme.restrict_reconstruct_of_eqOn _ _ _ localReconstruct A f g hfg,
    recombine_eq_reconstruct]

/-- **Correctness** of the listed scheme: any `k` listed parties reconstruct, transferred from
`Shamir.correct` and `Shamir.localReconstruct` (`Scheme.restrict_correct`). [PS10, Prop 154.5] -/
theorem shamirScheme_correct (π : ShamirParams) :
    (shamirScheme π).Correct (AccessStructure.threshold π.k) := by
  rw [shamirScheme_eq]
  exact Scheme.restrict_correct _ _ _ (correct π.k_pos) localReconstruct
    fun A hA => (AccessStructure.threshold_map_auth π.k (partyEmb π) A).2 hA

/-- Reconstruction by a listed set reads only its shares (`Shamir.localReconstruct`,
`Scheme.restrict_localReconstruct`). -/
theorem shamirScheme_localReconstruct (π : ShamirParams) :
    (shamirScheme π).LocalReconstruct := by
  rw [shamirScheme_eq]
  exact Scheme.restrict_localReconstruct _ _ _ localReconstruct

/-- **Perfect privacy** of the listed scheme against at most `k − 1` listed parties, transferred
from `Shamir.perfectPrivacy` (`Scheme.restrict_perfectPrivacy`). [PS10, Prop 154.5] -/
theorem shamirScheme_perfectPrivacy (π : ShamirParams) :
    (shamirScheme π).PerfectPrivacy (AccessStructure.threshold π.k) := by
  rw [shamirScheme_eq]
  exact Scheme.restrict_perfectPrivacy _ _ _ perfectPrivacy
    fun B hB h => hB ((AccessStructure.threshold_map_auth π.k (partyEmb π) B).1 h)

/-! ### The share machine -/

/-- **One round of the share loop** on `⟨⟨p, x⟩, ⟨r, ⟨w, acc⟩⟩⟩`: the low base-`p` digit
`r mod p` of the remaining coins times the current power `w` of the point is added to `acc`, the
coins lose their low digit (`⌊r / p⌋`, cut to the length of `r`) and `w` is multiplied by `x`.
The context `⟨p, x⟩` is kept. The body of the counted loop `BinArith.forLoop`. -/
def shareStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d) (pairEncode
    (PrefixByLength.take (pairEncode (pairFstD (pairSndD d))
      (BinArith.div (pairEncode (pairFstD (pairSndD d)) (pairFstD (pairFstD d))))))
    (pairEncode
      (mulModW (pairEncode (pairFstD (pairFstD d))
        (pairEncode (pairFstD (pairSndD (pairSndD d))) (pairSndD (pairFstD d)))))
      (addModW (pairEncode (pairFstD (pairFstD d)) (pairEncode (pairSndD (pairSndD (pairSndD d)))
        (mulModW (pairEncode (pairFstD (pairFstD d)) (pairEncode
          (BinArith.mod (pairEncode (pairFstD (pairSndD d)) (pairFstD (pairFstD d))))
          (pairFstD (pairSndD (pairSndD d)))))))))))

/-- The defining equation of `shareStep`. -/
theorem shareStep_eq (d : List Bool) :
    shareStep d = pairEncode (pairFstD d) (pairEncode
      (PrefixByLength.take (pairEncode (pairFstD (pairSndD d))
        (BinArith.div (pairEncode (pairFstD (pairSndD d)) (pairFstD (pairFstD d))))))
      (pairEncode
        (mulModW (pairEncode (pairFstD (pairFstD d))
          (pairEncode (pairFstD (pairSndD (pairSndD d))) (pairSndD (pairFstD d)))))
        (addModW (pairEncode (pairFstD (pairFstD d)) (pairEncode
          (pairSndD (pairSndD (pairSndD d)))
          (mulModW (pairEncode (pairFstD (pairFstD d)) (pairEncode
            (BinArith.mod (pairEncode (pairFstD (pairSndD d)) (pairFstD (pairFstD d))))
            (pairFstD (pairSndD (pairSndD d))))))))))) := rfl

/-- **The state of the share loop after `j` rounds**, for prime `p`, coins `r`, point `x` and
secret `sec`: `⟨⟨p, x⟩, ⟨⌊r / p^j⌋, ⟨x^{j+1}, sec + ∑_{t<j} digit_t(r) · x^{t+1}⟩⟩⟩`, where
`digit_t(r) = ⌊r / p^t⌋ mod p`. -/
def shareState (p : ℕ) (sec x : ZMod p) (r j : ℕ) : List Bool :=
  pairEncode (pairEncode (Nat.bits p) (resWord x)) (pairEncode (Nat.bits (r / p ^ j))
    (pairEncode (resWord (x ^ (j + 1)))
      (resWord (sec + ∑ t ∈ range j, ((r / p ^ t % p : ℕ) : ZMod p) * x ^ (t + 1)))))

/-- The defining equation of `shareState`. -/
theorem shareState_eq (p : ℕ) (sec x : ZMod p) (r j : ℕ) :
    shareState p sec x r j = pairEncode (pairEncode (Nat.bits p) (resWord x))
      (pairEncode (Nat.bits (r / p ^ j)) (pairEncode (resWord (x ^ (j + 1)))
        (resWord (sec + ∑ t ∈ range j, ((r / p ^ t % p : ℕ) : ZMod p) * x ^ (t + 1))))) := rfl

/-- **One round advances the share loop** (`BinArith.div_pairEncode`, `mod_pairEncode`,
`mulModW_resWord`, `addModW_resWord`). -/
theorem shareStep_shareState {p : ℕ} [NeZero p] (sec x : ZMod p) (r j : ℕ) :
    shareStep (shareState p sec x r j) = shareState p sec x r (j + 1) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hdig : Nat.bits (r / p ^ j % p) = resWord ((r / p ^ j % p : ℕ) : ZMod p) :=
    (resWord_natCast_of_lt (Nat.mod_lt _ hp)).symm
  have hdiv : r / p ^ j / p = r / p ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
  have hlen : (Nat.bits (r / p ^ (j + 1))).length ≤ (Nat.bits (r / p ^ j)).length := by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, ← hdiv]
    exact Nat.size_le_size (Nat.div_le_self _ _)
  rw [shareStep_eq, shareState_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [BinArith.div_pairEncode, BinArith.mod_pairEncode, hdiv, PrefixByLength.take_def,
    pairFstD_pairEncode, pairSndD_pairEncode, List.take_of_length_le hlen, mulModW_resWord, hdig,
    mulModW_resWord, addModW_resWord, shareState_eq, Finset.sum_range_succ, ← pow_succ, ← add_assoc]

/-- The share loop after `j` rounds from the state with no digit consumed. -/
theorem iterate_shareStep {p : ℕ} [NeZero p] (sec x : ZMod p) (r j : ℕ) :
    shareStep^[j] (shareState p sec x r 0) = shareState p sec x r j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, shareStep_shareState]

/-- **The share machine** on `⟨π, ⟨sec, ⟨r, x⟩⟩⟩`: run `shareStep` once per letter of `1^{k−1}`
(the counted loop `BinArith.forLoop`, host H16) from `⟨⟨p, x⟩, ⟨r, ⟨x, sec⟩⟩⟩` and read the
accumulator. It evaluates the dealer's polynomial `sec + ∑_{t<k−1} digit_t(r) · x^{t+1}` at `x`
(`shareRaw_spec`). [Sha79, §2] -/
def shareRaw (z : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (pairSndD (BinArith.forLoop shareStep
    (pairEncode ((pairFstD (pairSndD (pairFstD z))).drop 1)
      (pairEncode (pairEncode (pairFstD (pairFstD z)) (pairSndD (pairSndD (pairSndD z))))
        (pairEncode (pairFstD (pairSndD (pairSndD z)))
          (pairEncode (pairSndD (pairSndD (pairSndD z))) (pairFstD (pairSndD z))))))))))

/-- The defining equation of `shareRaw`. -/
theorem shareRaw_eq (z : List Bool) :
    shareRaw z = pairSndD (pairSndD (pairSndD (pairSndD (BinArith.forLoop shareStep
      (pairEncode ((pairFstD (pairSndD (pairFstD z))).drop 1)
        (pairEncode (pairEncode (pairFstD (pairFstD z)) (pairSndD (pairSndD (pairSndD z))))
          (pairEncode (pairFstD (pairSndD (pairSndD z)))
            (pairEncode (pairSndD (pairSndD (pairSndD z))) (pairFstD (pairSndD z)))))))))) := rfl

/-- **The share machine computes the dealer's polynomial**: on `⟨π, ⟨sec, ⟨r, x⟩⟩⟩` it writes
`(poly sec (coinEquiv π r)).eval x`, for every evaluation point `x`. [Sha79, §2]

**Proof sketch.** The counter `1^{k−1}` runs `k − 1` rounds (`BinArith.forLoop_pairEncode`) from
the state `shareState … 0`, and each round advances the state (`iterate_shareStep`), so the
accumulator holds `sec + ∑_{t<k−1} digit_t(r) · x^{t+1}`. By `poly_eval` and `eval_coinEquiv`
the dealer's polynomial at `x` is `sec + x · ∑_{t<k−1} digit_t(r) · x^t`, the same sum. -/
theorem shareRaw_spec (π : ShamirParams) (sec : ZMod π.p) (r : Fin (π.p ^ (π.k - 1)))
    (x : ZMod π.p) :
    shareRaw (pairEncode π.encode (pairEncode (resWord sec)
      (pairEncode (Nat.bits r) (resWord x)))) = resWord ((poly sec (coinEquiv π r)).eval x) := by
  have h0 : pairEncode (pairEncode (Nat.bits π.p) (resWord x)) (pairEncode (Nat.bits r)
      (pairEncode (resWord x) (resWord sec))) = shareState π.p sec x r 0 := by
    rw [shareState_eq, pow_zero, Nat.div_one, zero_add, pow_one, Finset.sum_range_zero, add_zero]
  rw [shareRaw_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, ShamirParams.pairFstD_encode,
    ShamirParams.pairFstD_pairSndD_encode]
  rw [h0, BinArith.forLoop_pairEncode, List.length_drop, List.length_replicate,
    iterate_shareStep, shareState_eq]
  simp only [pairSndD_pairEncode]
  rw [poly_eval, eval_coinEquiv, Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl fun t _ => by ring

/-- `shareStep` keeps its context `⟨p, x⟩`. -/
theorem pairFstD_shareStep (d : List Bool) : pairFstD (shareStep d) = pairFstD d := by
  rw [shareStep_eq, pairFstD_pairEncode]

/-- `shareStep` grows a word by at most `3|⟨p, x⟩| + 6` letters: the coins only shrink, and the
two residues are cut to the length of `p` (`length_take_pairEncode_le`). -/
theorem length_shareStep_le (d : List Bool) :
    (shareStep d).length ≤ d.length + 6 * ((pairFstD d).length + 1) := by
  have h1 := length_pair_components_le d
  have h2 := length_pair_components_le (pairSndD d)
  have h3 := length_pairFstD_le (pairFstD d)
  have h4 := length_take_pairEncode_le (pairFstD (pairSndD d))
    (BinArith.div (pairEncode (pairFstD (pairSndD d)) (pairFstD (pairFstD d))))
  have h5 := length_mulModW_le (pairEncode (pairFstD (pairFstD d))
    (pairEncode (pairFstD (pairSndD (pairSndD d))) (pairSndD (pairFstD d))))
  have h6 := length_addModW_le (pairEncode (pairFstD (pairFstD d)) (pairEncode
    (pairSndD (pairSndD (pairSndD d))) (mulModW (pairEncode (pairFstD (pairFstD d)) (pairEncode
      (BinArith.mod (pairEncode (pairFstD (pairSndD d)) (pairFstD (pairFstD d))))
      (pairFstD (pairSndD (pairSndD d))))))))
  rw [pairFstD_pairEncode] at h5 h6
  rw [shareStep_eq, length_pairEncode, length_pairEncode, length_pairEncode]
  omega

/-- **The share machine is polynomial-time.**

**Proof sketch.** `shareStep` is a pairing of projections, `BinArith.div` cut to a length
(`polyTimeComputable_takePrefixByLength`) and the leaves `mulModW`, `addModW`, `BinArith.mod`.
It keeps its context and grows by at most `6(|context| + 1)` per round (`length_shareStep_le`),
so the counted loop is polynomial-time (`BinArith.polyTimeComputable_forLoop`,
`BinArith.forLoop_bound_of_ctx`); the counter, the initial state and the final projections are
projections and a `drop`. -/
theorem polyTimeComputable_shareRaw : PolyTimeComputable shareRaw := by
  have hP : PolyTimeComputable fun d => pairFstD (pairFstD d) :=
    polyTimeComputable_pairFstD.comp' polyTimeComputable_pairFstD
  have hR : PolyTimeComputable fun d => pairFstD (pairSndD d) := BinArith.polyTimeComputable_slot2
  have hW : PolyTimeComputable fun d => pairFstD (pairSndD (pairSndD d)) :=
    polyTimeComputable_pairFstD.comp' BinArith.polyTimeComputable_slot3
  have hA : PolyTimeComputable fun d => pairSndD (pairSndD (pairSndD d)) :=
    polyTimeComputable_pairSndD.comp' BinArith.polyTimeComputable_slot3
  have hX : PolyTimeComputable fun d => pairSndD (pairFstD d) :=
    polyTimeComputable_pairSndD.comp' polyTimeComputable_pairFstD
  have hstep : PolyTimeComputable shareStep :=
    (polyTimeComputable_pairFstD.pairEncode
      ((PolyTimeComputable.takeTo hR
        (BinArith.polyTimeComputable_div.comp' (hR.pairEncode hP))).pairEncode
        ((polyTimeComputable_mulModW.comp' (hP.pairEncode (hW.pairEncode hX))).pairEncode
          (polyTimeComputable_addModW.comp' (hP.pairEncode (hA.pairEncode
            (polyTimeComputable_mulModW.comp' (hP.pairEncode
              ((BinArith.polyTimeComputable_mod.comp' (hR.pairEncode hP)).pairEncode
                hW))))))))).congr fun d => (shareStep_eq d).symm
  have hloop := BinArith.polyTimeComputable_forLoop hstep _ _
    (BinArith.forLoop_bound_of_ctx 6 pairFstD_shareStep length_shareStep_le)
  have hK : PolyTimeComputable fun z => (pairFstD (pairSndD (pairFstD z))).drop 1 :=
    polyTimeComputable_tail.comp'
      (BinArith.polyTimeComputable_slot2.comp' polyTimeComputable_pairFstD)
  have hS3 : PolyTimeComputable fun z => pairSndD (pairSndD (pairSndD z)) := hA
  have hinit := hK.pairEncode ((hP.pairEncode hS3).pairEncode
    ((polyTimeComputable_pairFstD.comp' BinArith.polyTimeComputable_slot3).pairEncode
      (hS3.pairEncode BinArith.polyTimeComputable_slot2)))
  have hout := polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' (hloop.comp' hinit))))
  exact hout.congr fun z => (shareRaw_eq z).symm

/-! ### The recombination machine -/

section Lagrange

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The numerator of `a`'s Lagrange coefficient at `0`** over a listed set `l`:
`∏_{b ∈ l, b ≠ a} b`, written with the factor `1` at `b = a`. -/
def lagNum (l : List (Party F)) (a : Party F) : F :=
  (l.map fun b => if b = a then 1 else label b).prod

/-- `lagNum l a = ∏_{b ∈ l} (if b = a then 1 else b)`. -/
theorem lagNum_eq (l : List (Party F)) (a : Party F) :
    lagNum l a = (l.map fun b => if b = a then 1 else label b).prod := rfl

/-- **The denominator of `a`'s Lagrange coefficient at `0`** over a listed set `l`:
`∏_{b ∈ l, b ≠ a} (b − a)`, written with the factor `1` at `b = a`. -/
def lagDen (l : List (Party F)) (a : Party F) : F :=
  (l.map fun b => if b = a then 1 else label b - label a).prod

/-- `lagDen l a = ∏_{b ∈ l} (if b = a then 1 else b − a)`. -/
theorem lagDen_eq (l : List (Party F)) (a : Party F) :
    lagDen l a = (l.map fun b => if b = a then 1 else label b - label a).prod := rfl

/-- The denominator is nonzero: party labels are distinct. -/
theorem lagDen_ne_zero (l : List (Party F)) (a : Party F) : lagDen l a ≠ 0 := by
  rw [lagDen_eq]
  refine List.prod_ne_zero fun h => ?_
  obtain ⟨b, -, hb⟩ := List.mem_map.1 h
  by_cases hba : b = a
  · rw [if_pos hba] at hb; exact one_ne_zero hb
  · rw [if_neg hba] at hb
    exact hba (Subtype.ext (sub_eq_zero.1 hb))

/-- **Recombination over a listed set, as list arithmetic**: for a duplicate-free `l`,
`recombine l f = ∑_{a ∈ l} lagNum l a · (lagDen l a)⁻¹ · f a`, the Lagrange coefficients at `0`
being `∏_{b ≠ a} b / (b − a)`. [Sha79, §2]

**Proof sketch.** `recombine` is the Lagrange interpolant at `0`
(`recombine_eq_eval_interpolate`); expanding (`Lagrange.interpolate_apply`), the basis
polynomial of `a` is `∏_{b ≠ a} (X − b)/(a − b)`, which at `0` is `∏_{b ≠ a} b/(b − a)`. Splitting
off the factor `1` at `a` (`Finset.mul_prod_erase`) and passing between the finset and the
duplicate-free list (`List.prod_toFinset`, `List.sum_toFinset`) gives the two list products. -/
theorem recombine_toFinset_eq (l : List (Party F)) (hl : l.Nodup) (f : Party F → F) :
    recombine l.toFinset f = (l.map fun a => lagNum l a * (lagDen l a)⁻¹ * f a).sum := by
  rw [recombine_eq_eval_interpolate, Lagrange.interpolate_apply, eval_finset_sum,
    List.sum_toFinset _ hl]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  have has : a ∈ l.toFinset := List.mem_toFinset.2 ha
  have hbasis : eval 0 (Lagrange.basis l.toFinset label a) =
      ∏ b ∈ l.toFinset.erase a, label b * (label b - label a)⁻¹ := by
    change eval 0 (∏ b ∈ l.toFinset.erase a,
      C (label a - label b)⁻¹ * (X - C (label b))) = _
    rw [eval_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [eval_mul, eval_C, eval_sub, eval_X, eval_C,
      show label a - label b = -(label b - label a) by ring, inv_neg]
    ring
  have hnum : lagNum l a = ∏ b ∈ l.toFinset.erase a, label b := by
    rw [lagNum_eq, ← List.prod_toFinset _ hl, ← Finset.mul_prod_erase _ _ has, if_pos rfl,
      one_mul]
    exact Finset.prod_congr rfl fun b hb => if_neg (Finset.ne_of_mem_erase hb)
  have hden : lagDen l a = ∏ b ∈ l.toFinset.erase a, (label b - label a) := by
    rw [lagDen_eq, ← List.prod_toFinset _ hl, ← Finset.mul_prod_erase _ _ has, if_pos rfl,
      one_mul]
    exact Finset.prod_congr rfl fun b hb => if_neg (Finset.ne_of_mem_erase hb)
  rw [eval_mul, eval_C, hbasis, hnum, hden, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  ring

end Lagrange

/-- **One round of the coefficient loop** on `⟨⟨p, x⟩, ⟨rest, ⟨num, den⟩⟩⟩`, where `rest` is an
encoded list of entries `⟨b, s_b⟩`: drop the head entry; if its label `b` differs from `x`,
multiply `num` by `b` and `den` by `b − x` (mod `p`). The body of a counted loop. -/
def lagStep (d : List Bool) : List Bool :=
  if BinArith.beq (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD d))))
      (pairSndD (pairFstD d))) then
    pairEncode (pairFstD d) (pairEncode (pairSndD (pairFstD (pairSndD d))) (pairSndD (pairSndD d)))
  else
    pairEncode (pairFstD d) (pairEncode (pairSndD (pairFstD (pairSndD d)))
      (pairEncode (mulModW (pairEncode (pairFstD (pairFstD d)) (pairEncode
          (pairFstD (pairSndD (pairSndD d))) (pairFstD (pairFstD (pairFstD (pairSndD d)))))))
        (mulModW (pairEncode (pairFstD (pairFstD d)) (pairEncode
          (pairSndD (pairSndD (pairSndD d))) (subModW (pairEncode (pairFstD (pairFstD d))
            (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD d))))
              (pairSndD (pairFstD d))))))))))

/-- The defining equation of `lagStep`. -/
theorem lagStep_eq (d : List Bool) :
    lagStep d =
      if BinArith.beq (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD d))))
          (pairSndD (pairFstD d))) then
        pairEncode (pairFstD d) (pairEncode (pairSndD (pairFstD (pairSndD d)))
          (pairSndD (pairSndD d)))
      else
        pairEncode (pairFstD d) (pairEncode (pairSndD (pairFstD (pairSndD d)))
          (pairEncode (mulModW (pairEncode (pairFstD (pairFstD d)) (pairEncode
              (pairFstD (pairSndD (pairSndD d))) (pairFstD (pairFstD (pairFstD (pairSndD d)))))))
            (mulModW (pairEncode (pairFstD (pairFstD d)) (pairEncode
              (pairSndD (pairSndD (pairSndD d))) (subModW (pairEncode (pairFstD (pairFstD d))
                (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD d))))
                  (pairSndD (pairFstD d)))))))))) := rfl

/-- **An entry of the listed shares**: `⟨b, f b⟩`, both as residue words. -/
def entryWord {q : ℕ} [Fact q.Prime] (f : Party (ZMod q) → ZMod q) (b : Party (ZMod q)) :
    List Bool :=
  pairEncode (resWord (label b)) (resWord (f b))

/-- `entryWord f b = ⟨b, f b⟩`. -/
theorem entryWord_eq {q : ℕ} [Fact q.Prime] (f : Party (ZMod q) → ZMod q) (b : Party (ZMod q)) :
    entryWord f b = pairEncode (resWord (label b)) (resWord (f b)) := rfl

section Machines

variable {q : ℕ} [Fact q.Prime]

/-- The residue word of `1` is `[true]`. Glue. -/
theorem resWord_one : resWord (1 : ZMod q) = [true] := by
  have h := resWord_natCast_of_lt (p := q) (v := 1) (Fact.out : q.Prime).one_lt
  rw [Nat.cast_one] at h
  rw [h, Nat.one_bits]

omit [Fact q.Prime] in
/-- The residue word of `0` is empty. Glue. -/
theorem resWord_zero : resWord (0 : ZMod q) = [] := by
  rw [resWord_eq, ZMod.val_zero, Nat.zero_bits]

/-- The test of `lagStep` compares labels: `beq ⟨b, a⟩ = decide (b = a)`. -/
theorem beq_resWord_label (a b : Party (ZMod q)) :
    BinArith.beq (pairEncode (resWord (label b)) (resWord (label a))) = decide (b = a) := by
  rw [BinArith.beq_def, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_resWord,
    bitsVal_resWord]
  exact decide_eq_decide.2 ⟨fun h => Subtype.ext (ZMod.val_injective q h), fun h => h ▸ rfl⟩

/-- **The coefficient loop over the listed entries `l`**, for the point `a`: `|l|` rounds
multiply in `lagNum l a` and `lagDen l a`.

**Proof sketch.** Induction on `l`. A round reads the head entry `⟨b, f b⟩`; its test compares
labels (`beq_resWord_label`), so for `b = a` it only drops the entry, and otherwise it multiplies
`num` by `b` and `den` by `b − a` (`mulModW_resWord`, `subModW_resWord`), which is the head
factor of `lagNum` and `lagDen`. -/
theorem iterate_lagStep (f : Party (ZMod q) → ZMod q) (a : Party (ZMod q)) :
    ∀ (l : List (Party (ZMod q))) (n d : ZMod q),
      lagStep^[l.length] (pairEncode (pairEncode (Nat.bits q) (resWord (label a)))
        (pairEncode (BinArith.encWords (l.map (entryWord f))) (pairEncode (resWord n)
          (resWord d)))) =
        pairEncode (pairEncode (Nat.bits q) (resWord (label a))) (pairEncode []
          (pairEncode (resWord (n * lagNum l a)) (resWord (d * lagDen l a))))
  | [], n, d => by
    rw [List.length_nil, Function.iterate_zero, id_eq, List.map_nil, BinArith.encWords_nil]
    simp only [lagNum_eq, lagDen_eq, List.map_nil, List.prod_nil, mul_one]
  | b :: l, n, d => by
    rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, BinArith.encWords_cons,
      lagStep_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, entryWord_eq]
    rw [beq_resWord_label]
    by_cases hba : b = a
    · rw [if_pos (decide_eq_true hba), iterate_lagStep f a l n d]
      simp only [lagNum_eq, lagDen_eq, List.map_cons, List.prod_cons, if_pos hba, one_mul]
    · rw [if_neg (by simpa using hba), mulModW_resWord, subModW_resWord, mulModW_resWord,
        iterate_lagStep f a l]
      simp only [lagNum_eq, lagDen_eq, List.map_cons, List.prod_cons, if_neg hba, mul_assoc]

end Machines

/-- **The term of one listed party** on `⟨⟨p, L⟩, ⟨a, s⟩⟩`, with `L` the encoded entries: run the
coefficient loop `lagStep` over `L` (the counted loop `BinArith.forLoop`, host H16, counter
`BinArith.countW L`) from `num = den = 1`, and write `num · den^{p−2} · s mod p` (`invModW`). -/
def lagTerm (w : List Bool) : List Bool :=
  mulModW (pairEncode (pairFstD (pairFstD w)) (pairEncode (mulModW (pairEncode
    (pairFstD (pairFstD w)) (pairEncode
      (pairFstD (pairSndD (pairSndD (pairSndD (BinArith.forLoop lagStep (pairEncode
        (BinArith.countW (pairSndD (pairFstD w))) (pairEncode (pairEncode (pairFstD (pairFstD w))
          (pairFstD (pairSndD w))) (pairEncode (pairSndD (pairFstD w))
            (pairEncode [true] [true])))))))))
      (invModW (pairEncode (pairFstD (pairFstD w))
        (pairSndD (pairSndD (pairSndD (pairSndD (BinArith.forLoop lagStep (pairEncode
          (BinArith.countW (pairSndD (pairFstD w))) (pairEncode (pairEncode
            (pairFstD (pairFstD w)) (pairFstD (pairSndD w))) (pairEncode (pairSndD (pairFstD w))
              (pairEncode [true] [true])))))))))))))) (pairSndD (pairSndD w))))

/-- The defining equation of `lagTerm`, through the loop's final state `S w`. -/
theorem lagTerm_eq (w : List Bool) :
    lagTerm w =
      let S := pairSndD (BinArith.forLoop lagStep (pairEncode
        (BinArith.countW (pairSndD (pairFstD w))) (pairEncode (pairEncode (pairFstD (pairFstD w))
          (pairFstD (pairSndD w))) (pairEncode (pairSndD (pairFstD w))
            (pairEncode [true] [true])))))
      mulModW (pairEncode (pairFstD (pairFstD w)) (pairEncode (mulModW (pairEncode
        (pairFstD (pairFstD w)) (pairEncode (pairFstD (pairSndD (pairSndD S)))
          (invModW (pairEncode (pairFstD (pairFstD w)) (pairSndD (pairSndD (pairSndD S))))))))
        (pairSndD (pairSndD w)))) := rfl

/-- **One round of the recombination loop** on `⟨⟨p, L⟩, ⟨rest, acc⟩⟩`: drop the head entry
`⟨a, s⟩` of `rest` and add its term `lagTerm ⟨⟨p, L⟩, ⟨a, s⟩⟩` to `acc` (mod `p`). The body of
a counted loop. -/
def recStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d) (pairEncode (pairSndD (pairFstD (pairSndD d)))
    (addModW (pairEncode (pairFstD (pairFstD d)) (pairEncode (pairSndD (pairSndD d))
      (lagTerm (pairEncode (pairFstD d) (pairFstD (pairFstD (pairSndD d)))))))))

/-- The defining equation of `recStep`. -/
theorem recStep_eq (d : List Bool) :
    recStep d = pairEncode (pairFstD d) (pairEncode (pairSndD (pairFstD (pairSndD d)))
      (addModW (pairEncode (pairFstD (pairFstD d)) (pairEncode (pairSndD (pairSndD d))
        (lagTerm (pairEncode (pairFstD d) (pairFstD (pairFstD (pairSndD d))))))))) := rfl

/-- **The recombination machine** on `⟨p, L⟩`, `L` the encoded entries `⟨a, f a⟩`: run `recStep`
once per entry (the counted loop `BinArith.forLoop`, host H16, counter `BinArith.countW L`) from
`acc = 0` and read the accumulator: `∑_a (∏_{b ≠ a} b) · (∏_{b ≠ a} (b − a))^{p−2} · f a mod p`,
the Lagrange recombination at `0` with Fermat inverses (`recombineRaw_spec`). [Sha79, §2] -/
def recombineRaw (z : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (BinArith.forLoop recStep
    (pairEncode (BinArith.countW (pairSndD z)) (pairEncode z (pairEncode (pairSndD z) []))))))

/-- The defining equation of `recombineRaw`. -/
theorem recombineRaw_eq (z : List Bool) :
    recombineRaw z = pairSndD (pairSndD (pairSndD (BinArith.forLoop recStep
      (pairEncode (BinArith.countW (pairSndD z)) (pairEncode z (pairEncode (pairSndD z) [])))))) :=
  rfl

section Machines

variable {q : ℕ} [Fact q.Prime]

/-- **The term machine** writes `a`'s Lagrange coefficient at `0` over the listed `l`, times
`s` (`iterate_lagStep`, `invModW_resWord` with `lagDen_ne_zero`). -/
theorem lagTerm_spec (l : List (Party (ZMod q))) (f : Party (ZMod q) → ZMod q)
    (a : Party (ZMod q)) (s : ZMod q) :
    lagTerm (pairEncode (pairEncode (Nat.bits q) (BinArith.encWords (l.map (entryWord f))))
      (pairEncode (resWord (label a)) (resWord s))) =
      resWord (lagNum l a * (lagDen l a)⁻¹ * s) := by
  have hc : BinArith.countW (BinArith.encWords (l.map (entryWord f))) =
      List.replicate l.length true := by
    rw [BinArith.countW_eq, BinArith.decWords_encWords, List.length_map]
  rw [lagTerm_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [hc, ← resWord_one (q := q), BinArith.forLoop_pairEncode, List.length_replicate,
    iterate_lagStep f a l 1 1]
  simp only [pairSndD_pairEncode, pairFstD_pairEncode, one_mul]
  rw [invModW_resWord (lagDen_ne_zero l a), mulModW_resWord, mulModW_resWord]

/-- **The recombination loop over the listed entries** `l'`, inside the context of all entries
`l`: `|l'|` rounds add `∑_{a ∈ l'} lagNum l a · (lagDen l a)⁻¹ · f a` to the accumulator. -/
theorem iterate_recStep (l : List (Party (ZMod q))) (f : Party (ZMod q) → ZMod q) :
    ∀ (l' : List (Party (ZMod q))) (acc : ZMod q),
      recStep^[l'.length] (pairEncode (pairEncode (Nat.bits q)
          (BinArith.encWords (l.map (entryWord f))))
        (pairEncode (BinArith.encWords (l'.map (entryWord f))) (resWord acc))) =
        pairEncode (pairEncode (Nat.bits q) (BinArith.encWords (l.map (entryWord f))))
          (pairEncode [] (resWord (acc +
            (l'.map fun a => lagNum l a * (lagDen l a)⁻¹ * f a).sum)))
  | [], acc => by
    rw [List.length_nil, Function.iterate_zero, id_eq, List.map_nil, BinArith.encWords_nil,
      List.map_nil, List.sum_nil, add_zero]
  | a :: l', acc => by
    rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, BinArith.encWords_cons,
      recStep_eq]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [entryWord_eq, lagTerm_spec, addModW_resWord, iterate_recStep l f l', List.map_cons,
      List.sum_cons, add_assoc]

/-- **The recombination machine**: on `⟨p, [⟨a, f a⟩ : a ∈ l]⟩`, for `p` prime and a
duplicate-free list `l` of parties, it writes `recombine l.toFinset f`, the Lagrange
recombination at `0` of the listed shares. [Sha79, §2]

**Proof sketch.** The counter `countW L` has one letter per entry, so the loop runs `|l|` rounds
(`BinArith.forLoop_pairEncode`); each adds one term (`iterate_recStep`, `lagTerm_spec`), and the
sum of terms is `recombine` (`recombine_toFinset_eq`). -/
theorem recombineRaw_spec (l : List (Party (ZMod q))) (hl : l.Nodup)
    (f : Party (ZMod q) → ZMod q) :
    recombineRaw (pairEncode (Nat.bits q) (BinArith.encWords
      (l.map fun a => pairEncode (resWord (label a)) (resWord (f a))))) =
      resWord (recombine l.toFinset f) := by
  have hE : (l.map fun a => pairEncode (resWord (label a)) (resWord (f a))) =
      l.map (entryWord f) := rfl
  rw [hE, recombineRaw_eq, pairSndD_pairEncode, BinArith.countW_eq, BinArith.decWords_encWords,
    List.length_map, ← resWord_zero (q := q), BinArith.forLoop_pairEncode, List.length_replicate,
    iterate_recStep l f l 0]
  simp only [pairSndD_pairEncode]
  rw [zero_add, recombine_toFinset_eq l hl]

end Machines

/-- `lagStep` keeps its context `⟨p, x⟩`. -/
theorem pairFstD_lagStep (d : List Bool) : pairFstD (lagStep d) = pairFstD d := by
  rw [lagStep_eq]; split_ifs <;> rw [pairFstD_pairEncode]

/-- `lagStep` grows a word by at most `6(|⟨p, x⟩| + 1)` letters: the entries only shrink and the
two products are cut to the length of `p`. -/
theorem length_lagStep_le (d : List Bool) :
    (lagStep d).length ≤ d.length + 6 * ((pairFstD d).length + 1) := by
  have h1 := length_pair_components_le d
  have h2 := length_pair_components_le (pairSndD d)
  have h2' := length_pair_components_le (pairSndD (pairSndD d))
  have h3 := length_pairFstD_le (pairFstD d)
  have h4 := length_pairSndD_le (pairFstD (pairSndD d))
  rw [lagStep_eq]
  split_ifs
  · rw [length_pairEncode, length_pairEncode]; omega
  · have h5 := length_mulModW_le (pairEncode (pairFstD (pairFstD d)) (pairEncode
      (pairFstD (pairSndD (pairSndD d))) (pairFstD (pairFstD (pairFstD (pairSndD d))))))
    have h6 := length_mulModW_le (pairEncode (pairFstD (pairFstD d)) (pairEncode
      (pairSndD (pairSndD (pairSndD d))) (subModW (pairEncode (pairFstD (pairFstD d))
        (pairEncode (pairFstD (pairFstD (pairFstD (pairSndD d)))) (pairSndD (pairFstD d)))))))
    rw [pairFstD_pairEncode] at h5 h6
    rw [length_pairEncode, length_pairEncode, length_pairEncode]; omega

/-- `recStep` keeps its context `⟨p, L⟩`. -/
theorem pairFstD_recStep (d : List Bool) : pairFstD (recStep d) = pairFstD d := by
  rw [recStep_eq, pairFstD_pairEncode]

/-- `recStep` grows a word by at most `4(|⟨p, L⟩| + 1)` letters. -/
theorem length_recStep_le (d : List Bool) :
    (recStep d).length ≤ d.length + 4 * ((pairFstD d).length + 1) := by
  have h1 := length_pair_components_le d
  have h2 := length_pair_components_le (pairSndD d)
  have h3 := length_pairFstD_le (pairFstD d)
  have h4 := length_pairSndD_le (pairFstD (pairSndD d))
  have h5 := length_addModW_le (pairEncode (pairFstD (pairFstD d)) (pairEncode
    (pairSndD (pairSndD d)) (lagTerm (pairEncode (pairFstD d) (pairFstD (pairFstD (pairSndD d)))))))
  rw [pairFstD_pairEncode] at h5
  rw [recStep_eq, length_pairEncode, length_pairEncode]; omega

/-- **The recombination machine is polynomial-time.**

**Proof sketch.** Both loop bodies are pairings of projections and the leaves `mulModW`,
`subModW`, `addModW`, `invModW`, with a branch on `BinArith.beq` (`polyTimeComputable_ite`); both
keep their context and grow by a linear amount per round (`length_lagStep_le`,
`length_recStep_le`), so both counted loops are polynomial-time
(`BinArith.polyTimeComputable_forLoop`, `BinArith.forLoop_bound_of_ctx`), the inner one inside
the outer body through `lagTerm`. Counters are `BinArith.countW` of the entry list. -/
theorem polyTimeComputable_recombineRaw : PolyTimeComputable recombineRaw := by
  have f1 := polyTimeComputable_pairFstD
  have s1 := polyTimeComputable_pairSndD
  have hP : PolyTimeComputable fun d => pairFstD (pairFstD d) := f1.comp' f1
  have hX : PolyTimeComputable fun d => pairSndD (pairFstD d) := s1.comp' f1
  have hR : PolyTimeComputable fun d => pairFstD (pairSndD d) := f1.comp' s1
  have hB : PolyTimeComputable fun d => pairFstD (pairFstD (pairFstD (pairSndD d))) :=
    f1.comp' (f1.comp' hR)
  have hN : PolyTimeComputable fun d => pairFstD (pairSndD (pairSndD d)) := f1.comp' (s1.comp' s1)
  have hD : PolyTimeComputable fun d => pairSndD (pairSndD (pairSndD d)) := s1.comp' (s1.comp' s1)
  have hlag : PolyTimeComputable lagStep :=
    (polyTimeComputable_ite (BinArith.polyTimeComputable_beq.comp' (hB.pairEncode hX))
      (f1.pairEncode ((s1.comp' hR).pairEncode (s1.comp' s1)))
      (f1.pairEncode ((s1.comp' hR).pairEncode
        ((polyTimeComputable_mulModW.comp' (hP.pairEncode (hN.pairEncode hB))).pairEncode
          (polyTimeComputable_mulModW.comp' (hP.pairEncode (hD.pairEncode
            (polyTimeComputable_subModW.comp' (hP.pairEncode (hB.pairEncode hX)))))))))).congr
      fun d => (lagStep_eq d).symm
  have hloop := BinArith.polyTimeComputable_forLoop hlag _ _
    (BinArith.forLoop_bound_of_ctx 6 pairFstD_lagStep length_lagStep_le)
  have hS : PolyTimeComputable fun w => pairSndD (BinArith.forLoop lagStep (pairEncode
      (BinArith.countW (pairSndD (pairFstD w))) (pairEncode (pairEncode (pairFstD (pairFstD w))
        (pairFstD (pairSndD w))) (pairEncode (pairSndD (pairFstD w))
          (pairEncode [true] [true]))))) :=
    s1.comp' (hloop.comp' ((BinArith.polyTimeComputable_countW.comp' hX).pairEncode
      ((hP.pairEncode hR).pairEncode (hX.pairEncode (polyTimeComputable_const _)))))
  have hterm : PolyTimeComputable lagTerm :=
    (polyTimeComputable_mulModW.comp' (hP.pairEncode
      ((polyTimeComputable_mulModW.comp' (hP.pairEncode
        ((f1.comp' (s1.comp' (s1.comp' hS))).pairEncode (polyTimeComputable_invModW.comp'
          (hP.pairEncode (s1.comp' (s1.comp' (s1.comp' hS)))))))).pairEncode
        (s1.comp' s1)))).congr fun w => (lagTerm_eq w).symm
  have hrec : PolyTimeComputable recStep :=
    (f1.pairEncode ((s1.comp' hR).pairEncode (polyTimeComputable_addModW.comp' (hP.pairEncode
      ((s1.comp' s1).pairEncode (hterm.comp' (f1.pairEncode (f1.comp' hR)))))))).congr
      fun d => (recStep_eq d).symm
  have hloop' := BinArith.polyTimeComputable_forLoop hrec _ _
    (BinArith.forLoop_bound_of_ctx 4 pairFstD_recStep length_recStep_le)
  exact (s1.comp' (s1.comp' (s1.comp' (hloop'.comp' ((BinArith.polyTimeComputable_countW.comp'
    s1).pairEncode (polyTimeComputable_id.pairEncode (s1.pairEncode
      (polyTimeComputable_const _)))))))).congr fun z => (recombineRaw_eq z).symm

/-! ### The dealer's coins -/

/-- **One round of the power loop** on `⟨p, acc⟩`: `acc := acc · p`, cut to `|acc| + |p|`
letters (which a product never exceeds). The body of a counted loop. -/
def powStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d) (PrefixByLength.take (pairEncode (pairSndD d ++ pairFstD d)
    (BinArith.mul (pairEncode (pairSndD d) (pairFstD d)))))

/-- The defining equation of `powStep`. -/
theorem powStep_eq (d : List Bool) :
    powStep d = pairEncode (pairFstD d) (PrefixByLength.take (pairEncode (pairSndD d ++ pairFstD d)
      (BinArith.mul (pairEncode (pairSndD d) (pairFstD d))))) := rfl

/-- `j` rounds of the power loop from `⟨p, 1⟩` give `⟨p, p^j⟩` (`BinArith.mul_pairEncode`;
the numeral of a product is at most as long as the two numerals together). -/
theorem iterate_powStep (p j : ℕ) :
    powStep^[j] (pairEncode (Nat.bits p) (Nat.bits 1)) =
      pairEncode (Nat.bits p) (Nat.bits (p ^ j)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlen : (Nat.bits (p ^ j * p)).length ≤ (Nat.bits (p ^ j) ++ Nat.bits p).length := by
      rw [List.length_append, Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_eq_bits_len,
        Nat.size_le, pow_add]
      exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)
    rw [Function.iterate_succ_apply', ih, powStep_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      BinArith.mul_pairEncode, PrefixByLength.take_def, pairFstD_pairEncode, pairSndD_pairEncode,
      List.take_of_length_le hlen, pow_succ]

/-- **The dealer's parameter word machine** on `⟨1^κ, π⟩`: `p^{k−1}` by the counted loop
`powStep` (host H16) over `1^{k−1}`, written as a numeral of width `b(κ) + 1`
(`Encoding.BinaryArith.fromLEPoly`). Its output is the bucket sampler's parameter word
`Cryptography.CoinSampling.modulusWord b κ (p^{k−1})`. -/
def dealerWord (b : PolyExpr) (z : List Bool) : List Bool :=
  Cryptography.Encoding.BinaryArith.fromLEPoly (b.add (.const 1)) (pairEncode (pairFstD z)
    (pairSndD (pairSndD (BinArith.forLoop powStep (pairEncode
      ((pairFstD (pairSndD (pairSndD z))).drop 1)
      (pairEncode (pairFstD (pairSndD z)) [true]))))))

/-- The defining equation of `dealerWord`. -/
theorem dealerWord_eq (b : PolyExpr) (z : List Bool) :
    dealerWord b z = Cryptography.Encoding.BinaryArith.fromLEPoly (b.add (.const 1))
      (pairEncode (pairFstD z) (pairSndD (pairSndD (BinArith.forLoop powStep (pairEncode
        ((pairFstD (pairSndD (pairSndD z))).drop 1)
        (pairEncode (pairFstD (pairSndD z)) [true])))))) := rfl

/-- **The dealer's parameter word machine is polynomial-time**.

**Proof sketch.** `powStep` is a pairing of projections with `BinArith.mul` cut to a length
(`polyTimeComputable_takePrefixByLength`); it keeps `p` and grows by at most `|p| + 2` per round,
so the counted loop is polynomial-time (`BinArith.polyTimeComputable_forLoop`,
`BinArith.forLoop_bound_of_ctx`); the counter is a projection and a `drop`, and the result is
written at width `b(κ) + 1` by `Encoding.BinaryArith.polyTimeComputable_fromLEPoly`. -/
theorem polyTimeComputable_dealerWord (b : PolyExpr) : PolyTimeComputable (dealerWord b) := by
  have hstep : PolyTimeComputable powStep :=
    (polyTimeComputable_pairFstD.pairEncode (PolyTimeComputable.takeTo
      (polyTimeComputable_pairSndD.append polyTimeComputable_pairFstD)
      (BinArith.polyTimeComputable_mul.comp' (polyTimeComputable_pairSndD.pairEncode
        polyTimeComputable_pairFstD)))).congr fun d => (powStep_eq d).symm
  have hlen : ∀ d, (powStep d).length ≤ d.length + 2 * ((pairFstD d).length + 1) := by
    intro d
    have h1 := length_pair_components_le d
    have h2 := length_take_pairEncode_le (pairSndD d ++ pairFstD d)
      (BinArith.mul (pairEncode (pairSndD d) (pairFstD d)))
    rw [List.length_append] at h2
    rw [powStep_eq, length_pairEncode]; omega
  have hloop := BinArith.polyTimeComputable_forLoop hstep _ _
    (BinArith.forLoop_bound_of_ctx 2 (fun d => by rw [powStep_eq, pairFstD_pairEncode]) hlen)
  exact ((Cryptography.Encoding.BinaryArith.polyTimeComputable_fromLEPoly _).comp'
    (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' (hloop.comp'
      ((polyTimeComputable_tail.comp' (BinArith.polyTimeComputable_slot2.comp'
        polyTimeComputable_pairSndD)).pairEncode (BinArith.polyTimeComputable_slot2.pairEncode
          (polyTimeComputable_const _)))))))).congr fun z => (dealerWord_eq b z).symm

/-- **Admissible parameters at `κ`**: the coin space `p^{k−1}` fits in `b(κ)` bits, so that the
bucket sampler with `b(κ) + κ` coins fails with probability at most `2^{-κ}`. -/
def shamirAdm (b : PolyExpr) (κ : ℕ) (π : ShamirParams) : Prop := π.p ^ (π.k - 1) ≤ 2 ^ b.eval κ

/-- `shamirAdm b κ π ↔ p^{k−1} ≤ 2^{b(κ)}`. -/
theorem shamirAdm_iff (b : PolyExpr) (κ : ℕ) (π : ShamirParams) :
    shamirAdm b κ π ↔ π.p ^ (π.k - 1) ≤ 2 ^ b.eval κ := Iff.rfl

/-- The coin space of admissible parameters as a bounded modulus. Glue. -/
def coinModulus (b : PolyExpr) (κ : ℕ) (π : {π // shamirAdm b κ π}) :
    Cryptography.CoinSampling.BoundedModulus b κ :=
  ⟨⟨π.1.p ^ (π.1.k - 1), pow_pos π.1.prime.pos _⟩, π.2⟩

/-- `coinModulus b κ π = p^{k−1}`. -/
theorem coe_coinModulus (b : PolyExpr) (κ : ℕ) (π : {π // shamirAdm b κ π}) :
    ((coinModulus b κ π).1 : ℕ) = π.1.p ^ (π.1.k - 1) := rfl

/-- **The dealer's coins are sampled efficiently**: one uniform residue `r < p^{k−1}`, written
`Nat.bits r`, drawn by the bucket sampler (`CoinSampling.samplesEfficiently_residue`, reindexed by
`samplesEfficiently_comap`, read through `ZMod.finEquiv` and re-encoded by
`Encoding.BinaryArith.toLE`), with the parameter word `p^{k−1}` computed by `dealerWord b`.
[PS10, Def 152.1] (`Share` is probabilistic polynomial-time)

**Proof sketch.** The parameter word: the power loop gives `p^{k−1}` (`iterate_powStep`), written
at width `b(κ) + 1`, which is `modulusWord b κ (p^{k−1})`. The draw: the residue sampler at the
modulus `p^{k−1}` (admissible: at most `2^{b(κ)}`) outputs `residueEnc`, the numeral of
`(finEquiv q).symm a` at width `b(κ) + 1`; `toLE` turns it into `Nat.bits` of the same value
(`toLE_eq_natBits`, `listToNat_natToList`), which is `Nat.bits` of the `Fin` coin; transporting
the draw from `ZMod q` to `Fin q` along `(finEquiv q).symm` leaves the identity core. -/
theorem dealerSamples_shamir (b : PolyExpr) :
    DealerSamples (fun π : ShamirParams => Fin (π.p ^ (π.k - 1))) (shamirAdm b)
      ShamirParams.encode fun _ r => Nat.bits r := by
  set ε : ∀ κ (π : {π // shamirAdm b κ π}), ZMod ((coinModulus b κ π).1 : ℕ) ≃
      Fin (π.1.p ^ (π.1.k - 1)) := fun κ π => (ZMod.finEquiv _).symm.toEquiv with hε
  have h1 := samplesEfficiently_comap (Cryptography.CoinSampling.samplesEfficiently_residue b)
    (coinModulus b)
  have h2 := h1.map_output (encOut' := fun κ (π : {π // shamirAdm b κ π}) (r : Fin
      (π.1.p ^ (π.1.k - 1))) => Nat.bits r) (fun κ π a => ε κ π a)
    Cryptography.Encoding.BinaryArith.polyTimeComputable_toLE fun κ π a => by
      have hlt : (((ZMod.finEquiv _).symm a : Fin _) : ℕ) < 2 ^ (b.eval κ + 1) :=
        lt_of_lt_of_le ((ZMod.finEquiv _).symm a).2 ((coinModulus b κ π).2.trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)))
      rw [Cryptography.CoinSampling.residueEnc_eq,
        Cryptography.Encoding.BinaryArith.toLE_eq_natBits,
        Cryptography.Candidates.listToNat_natToList hlt]
      rfl
  have h3 := h2.congr (encDraw' := fun κ π r => Cryptography.CoinSampling.residueEnc b κ
    (coinModulus b κ π) ((ε κ π).symm r)) ε fun κ π d => by
      show Cryptography.CoinSampling.residueEnc b κ _ ((ε κ π).symm (ε κ π d)) = _
      rw [Equiv.symm_apply_apply]
  have hid : (fun κ (π : {π // shamirAdm b κ π}) (d : Fin (π.1.p ^ (π.1.k - 1))) =>
      ε κ π ((ε κ π).symm d)) = fun _ _ r => r := by
    funext κ π d; exact Equiv.apply_symm_apply _ _
  rw [hid] at h3
  refine (dealerSamples_iff _ _ _ _).2 ⟨_, _, ⟨dealerWord b, polyTimeComputable_dealerWord b,
    fun κ π => ?_⟩, h3⟩
  rw [NUPPT.advInput_eq, dealerWord_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, ShamirParams.pairFstD_encode,
    ShamirParams.pairFstD_pairSndD_encode]
  rw [List.drop_one, List.tail_replicate, ← Nat.one_bits, BinArith.forLoop_pairEncode,
    List.length_replicate, iterate_powStep, pairSndD_pairEncode, pairSndD_pairEncode,
    Cryptography.Encoding.BinaryArith.fromLEPoly_pairEncode, bitsVal_bits,
    Cryptography.CoinSampling.modulusWord_eq, List.length_replicate, PolyExpr.eval_add,
    PolyExpr.eval_const,
    coe_coinModulus]

/-! ### The instance -/

/-- **Shamir's scheme over `ℤ_p` as an efficient secret-sharing scheme** [PS10, Def 152.1,
Prot 154.4], at the coin bound `b`: public parameters `ShamirParams` (word `ShamirParams.encode`),
parties `Fin n` (party `i` is `i + 1`), secrets and shares in `ZMod p`, coins `Fin (p^{k−1})`
(one residue, decoded into the `k − 1` random coefficients by `coinEquiv`), the typed scheme
`shamirScheme π`, the threshold access structure, admissible parameters `shamirAdm b`, residues and
parties as `Nat.bits` numerals; share map `shareRaw`, reconstruction `recombineRaw` after
projecting `p` out of the parameter word, dealer `dealerSamples_shamir b`. -/
noncomputable def shamirEfficient (b : PolyExpr) : EfficientScheme where
  Pub := ShamirParams
  Party π := Fin π.n
  Secret π := ZMod π.p
  Share π := ZMod π.p
  Rand π := Fin (π.p ^ (π.k - 1))
  scheme := shamirScheme
  access π := AccessStructure.threshold π.k
  Adm := shamirAdm b
  encPub := ShamirParams.encode
  encParty π i := resWord (label (partyEmb π i))
  encSecret _ := resWord
  encShare _ := resWord
  encRand _ r := Nat.bits r
  share_poly := ⟨shareRaw, polyTimeComputable_shareRaw, fun π sec r i => by
    rw [shareRaw_spec, shamirScheme_share, scheme_share]⟩
  reconstruct_poly := ⟨fun z => recombineRaw (pairEncode (pairFstD (pairFstD z)) (pairSndD z)),
    polyTimeComputable_recombineRaw.comp' ((polyTimeComputable_pairFstD.comp'
      polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD),
    fun π A l sh hl hA => by
      classical
      let g : Party (ZMod π.p) → ZMod π.p := Function.extend (partyEmb π) sh fun _ => 0
      have hg : ∀ i, g (partyEmb π i) = sh i := fun i => (partyEmb π).injective.extend_apply _ _ _
      have hmap : (l.map fun i => pairEncode (resWord (label (partyEmb π i))) (resWord (sh i))) =
          (l.map (partyEmb π)).map fun a => pairEncode (resWord (label a)) (resWord (g a)) := by
        rw [List.map_map]; exact List.map_congr_left fun i _ => by rw [Function.comp_apply, hg]
      have hset : (l.map (partyEmb π)).toFinset = A.map (partyEmb π) := by
        ext a; simp [hA]
      dsimp only
      rw [pairFstD_pairEncode, pairSndD_pairEncode, ShamirParams.pairFstD_encode, hmap,
        recombineRaw_spec _ (hl.map (partyEmb π).injective), hset,
        shamirScheme_reconstruct π A sh g fun i _ => hg i]⟩
  dealer_efficient := dealerSamples_shamir b

/-- The typed scheme of `shamirEfficient b` at `π` is `shamirScheme π`. -/
theorem shamirEfficient_scheme (b : PolyExpr) (π : ShamirParams) :
    (shamirEfficient b).scheme π = shamirScheme π := rfl

/-- The access structure of `shamirEfficient b` at `π` is `threshold k`. -/
theorem shamirEfficient_access (b : PolyExpr) (π : ShamirParams) :
    (shamirEfficient b).access π = AccessStructure.threshold π.k := rfl

/-- **Correctness of efficient Shamir**: at every `π`, any `k` listed parties reconstruct
(`shamirScheme_correct`, transferred from `Shamir.correct`). [PS10, Prop 154.5] -/
theorem shamirEfficient_correct (b : PolyExpr) : (shamirEfficient b).Correct :=
  ((shamirEfficient b).correct_iff).2 fun π => shamirScheme_correct π

/-- **Local reconstruction of efficient Shamir** (`shamirScheme_localReconstruct`). -/
theorem shamirEfficient_localReconstruct (b : PolyExpr) : (shamirEfficient b).LocalReconstruct :=
  ((shamirEfficient b).localReconstruct_iff).2 fun π => shamirScheme_localReconstruct π

/-- **Perfect privacy of efficient Shamir**: at every `π`, at most `k − 1` listed parties learn
nothing (`shamirScheme_perfectPrivacy`, transferred from `Shamir.perfectPrivacy`).
[PS10, Prop 154.5] -/
theorem shamirEfficient_perfectPrivacy (b : PolyExpr) : (shamirEfficient b).PerfectPrivacy :=
  ((shamirEfficient b).perfectPrivacy_iff).2 fun π => shamirScheme_perfectPrivacy π


/-! Rule-10 paired control (evidence only, not delivered). -/
example (π : ShamirParams) (sec : ZMod π.p) (q : degreeLT (ZMod π.p) (π.k - 1))
    (a : Party (ZMod π.p)) : (scheme π.k (ZMod π.p)).share sec q a = (poly sec q).eval (label a) :=
  rfl  -- CONTROL-FOREIGN
example (π : ShamirParams) (sec : ZMod π.p) (q : degreeLT (ZMod π.p) (π.k - 1))
    (a : Party (ZMod π.p)) : (scheme π.k (ZMod π.p)).share sec q a = (poly sec q).eval (label a) :=
  scheme_share sec q a  -- CONTROL-READER

end TCSlib.Shamir
