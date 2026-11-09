/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.NumberTheory.QuadraticResidues
import TCSlib.Cryptography.Asymptotic.Ensembles
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Decisional Diffie–Hellman for safe primes

The experiments use the order-`q` subgroup of `Z_p^*` for a safe prime
`p = 2q + 1` [PS10, Assumption 105.1 and p. 106]. The seed is the instance
generator's coin string together with two or three independent
`n · n`-bit blocks. Rejection sampling reads the exponent from each block.
The real and random experiments therefore have the same instance law.
Their tuple encoding has length `15n + 14` at a well-formed instance.

## Main definitions

* `TCSlib.Cryptography.Candidates.ddhTuple` encodes the instance and three powers.
* `TCSlib.Cryptography.Candidates.ddhExpo` reads an exponent from a block of coins.
* `TCSlib.Cryptography.Candidates.ddhReal` and `ddhRandom` give the real and random
  ensembles. `TCSlib.Cryptography.Candidates.DDHAssumption` asserts their
  computational indistinguishability.

## Main results

* `TCSlib.Cryptography.Candidates.card_QR_safe` and `zpowers_eq_QR` give the
  order and generators of the subgroup of squares.
* `TCSlib.Cryptography.Candidates.statClose_sq_generator` bounds the difference
  between sampling a square and sampling a generator.
* `TCSlib.Cryptography.Candidates.ddhExpo_statClose` bounds the distance from
  the exponent sampler to the uniform law.
* `ddhReal_σ`, `ddhRandom_σ`, `ddhReal_X` and `ddhRandom_X` expose the seed
  types and sample formulas.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.11: Assumption 105.1, the remarks on p. 106, Algorithm 106.2, Theorem 107.3;
  §3.10: Definitions 102.1 and 102.2; §3.1: Definition 69.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage) and
  Lemma 3.2 (closure under post-processing).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## The group `G_q` of a safe prime (NT-105.a, [PS10, p. 106]) -/

section SafePrime

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- A safe prime `p = 2q + 1` is odd. -/
theorem safe_ne_two (hpq : p = 2 * q + 1) : p ≠ 2 := by
  have := hq.out.two_le
  omega

/-- `5 ≤ p` for a safe prime `p = 2q + 1`. -/
theorem five_le_safe (hpq : p = 2 * q + 1) : 5 ≤ p := by
  have := hq.out.two_le
  omega

/-- `(p − 1)/2 = q` and `p/2 = q` for `p = 2q + 1`. -/
theorem safe_half (hpq : p = 2 * q + 1) : (p - 1) / 2 = q ∧ p / 2 = q := by omega

/-- **`|G_q| = q`** [PS10, p. 106, "`G` has a subgroup `G_q` of order `q`"]: the subgroup of
squares of `Z_p^*` has `(p − 1)/2 = q` elements (`NumberTheory.card_QR_prime`). -/
theorem card_QR_safe (hpq : p = 2 * q + 1) : Nat.card (QR p) = q := by
  rw [card_QR_prime (safe_ne_two hpq), (safe_half hpq).1]

/-- **`x ∈ G_q ↔ x^q = 1`** [PS10, p. 106, "the subgroup `G_q` consists of all of the squares
modulo `p`"]: Euler's criterion with `p/2 = q`. -/
theorem mem_QR_iff_pow_eq_one (hpq : p = 2 * q + 1) (x : (ZMod p)ˣ) : x ∈ QR p ↔ x ^ q = 1 := by
  rw [mem_QR_iff, ZMod.euler_criterion_units, (safe_half hpq).2]

/-- **Every element `≠ 1` of `G_q` has order `q`** [PS10, p. 106, "since `q` is prime, `G_q`
will be a cyclic group … every element is a generator"]. -/
theorem orderOf_eq_of_mem_QR (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) (hx1 : x ≠ 1) :
    orderOf x = q :=
  orderOf_eq_prime ((mem_QR_iff_pow_eq_one hpq x).1 hx) hx1

/-- **Every element `≠ 1` of `G_q` generates `G_q`** [PS10, p. 106]. -/
theorem zpowers_eq_QR (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = QR p := by
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx)
  rw [Nat.card_zpowers, orderOf_eq_of_mem_QR hpq hx hx1, card_QR_safe hpq]

/-- **`G_q` is the unique subgroup of order `q`** of `Z_p^*` [PS10, p. 106]: a subgroup of
order `q` consists of `q`-th roots of unity, hence lies in `G_q`, and has its size. -/
theorem eq_QR_of_card (hpq : p = 2 * q + 1) (K : Subgroup (ZMod p)ˣ) (hK : Nat.card K = q) :
    K = QR p := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [mem_QR_iff_pow_eq_one hpq]
    have h1 := pow_card_eq_one' (G := K) (x := ⟨x, hx⟩)
    rw [hK] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · rw [hK, card_QR_safe hpq]

/-- **Squaring is `2`-to-`1` onto `G_q`** [PS10, p. 106, "choosing a generator involves simply
picking a random element `a ∈ G` and computing `a²`"]: every square has exactly two roots. -/
theorem card_sqrt_safe (hpq : p = 2 * q + 1) {x : (ZMod p)ˣ} (hx : x ∈ QR p) :
    (univ.filter fun y : (ZMod p)ˣ => y ^ 2 = x).card = 2 :=
  card_sqrt_eq_two (safe_ne_two hpq) hx

/-- **The square of a uniform unit is a uniform element of `G_q`** (Claim-107.a, first part; inventory lemma
C5 of chapter 2). -/
theorem pushesUniform_sqTo_safe (hpq : p = 2 * q + 1) : HardcoreBit.PushesUniform (sqTo p) := by
  refine pushesUniform_of_card_fiber (sqTo p) (c := 2) (by norm_num) fun y => ?_
  rw [← card_sqrt_safe hpq y.2]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  rw [Subtype.ext_iff, coe_sqTo]

/-- **`g² = 1` with probability `1/q`** for a uniform unit `g` (Claim-107.a): the two roots
`±1` among the `p − 1 = 2q` units. -/
theorem uprob_sq_eq_one (hpq : p = 2 * q + 1) :
    uprob (fun g : (ZMod p)ˣ => g ^ 2 = 1) = 1 / (q : ℝ) := by
  rw [uprob_eq_card_filter, card_sqrt_safe hpq (one_mem _), ZMod.card_units]
  have h : p - 1 = 2 * q := by omega
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  rw [h]
  push_cast
  field_simp

end SafePrime

/-- **Two samplers on the same seeds are statistically close within the probability that they
differ**: `|Pr[T(X)] − Pr[T(Y)]| ≤ Pr[X ≠ Y]` (the device for the `1/q` term of
Theorem 107.3: the scheme's `h = g²` and the derived generator's `h` differ only on `g² = 1`). -/
theorem statClose_of_uprob_ne {σ γ : Type*} [Fintype σ] (X Y : σ → γ) :
    StatClose X Y (uprob fun s => X s ≠ Y s) := by
  rw [statClose_iff]
  intro T
  have key : ∀ (X Y : σ → γ), uprob (fun s => T (X s)) ≤
      uprob (fun s => T (Y s)) + uprob (fun s => X s ≠ Y s) := by
    intro X Y
    refine (uprob_mono fun s h => ?_).trans (uprob_or_le (fun s => T (Y s)) (fun s => X s ≠ Y s))
    by_cases hxy : X s = Y s
    · exact Or.inl (hxy ▸ h)
    · exact Or.inr hxy
  have h1 := key X Y
  have h2 := key Y X
  have hsymm : uprob (fun s => Y s ≠ X s) = uprob (fun s => X s ≠ Y s) :=
    OneWay.uprob_congr fun s => ne_comm
  rw [hsymm] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **Removing one point moves every probability by at most `1/|α|`** (the counting step of
`statClose_sq_generator`): the uniform element of `α` and the uniform element of `α ∖ {a}` give
an event probabilities `t/N` and `s/(N − 1)` with `s ≤ t ≤ s + 1` and `s ≤ N − 1`.

**Proof sketch.** Count (`uprob_eq_card_filter`, `Fintype.card_subtype_compl`): `s` is the number of
points of `T ∖ {a}` (`Equiv.subtypeSubtypeEquivSubtypeInter`), so `s ≤ t ≤ s + 1` (`card_insert_le`)
and `s ≤ N − 1`. For `N = 1` the punctured side is `0` and `t ≤ 1`. Otherwise `t/N ≤ (s + 1)/N ≤
s/(N − 1) + 1/N` and `s/(N − 1) ≤ (s + 1)/N ≤ t/N + 1/N`, the step `s/(N − 1) ≤ (s + 1)/N` being `s
≤ N − 1`. -/
private theorem dlc_abs_uprob_sub_uprob_ne_le {α : Type*} [Fintype α] [DecidableEq α] (a : α)
    (T : α → Prop) :
    |uprob T - uprob (fun y : {y : α // y ≠ a} => T y)| ≤ 1 / (Fintype.card α : ℝ) := by
  classical
  have hcs : Fintype.card {y : α // y ≠ a} = Fintype.card α - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [uprob_eq_card_filter, uprob_eq_card_filter, hcs]
  set N := Fintype.card α with hN
  set t := (univ.filter T).card with ht
  set s := (univ.filter fun y : {y : α // y ≠ a} => T y).card with hs
  -- `s` counts `T ∖ {a}`
  have hs' : s = (univ.filter fun y : α => T y ∧ y ≠ a).card := by
    rw [hs, ← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun y => y ≠ a) T |>.trans
      (Equiv.subtypeEquivRight fun y => and_comm))
  have hst : s ≤ t := by
    rw [hs']
    exact card_le_card fun y hy => by simp only [mem_filter] at hy ⊢; exact ⟨hy.1, hy.2.1⟩
  have hts : t ≤ s + 1 := by
    rw [hs']
    have hsub : univ.filter T ⊆ insert a (univ.filter fun y : α => T y ∧ y ≠ a) := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and, mem_insert] at hy ⊢
      by_cases h : y = a
      · exact Or.inl h
      · exact Or.inr ⟨hy, h⟩
    exact (card_le_card hsub).trans (card_insert_le _ _)
  have hN1 : 1 ≤ N := Fintype.card_pos_iff.2 ⟨a⟩
  have hsN : s ≤ N - 1 := by
    rw [hs, ← hcs]
    exact card_le_univ _
  rcases Nat.lt_or_ge N 2 with h2 | h2
  · -- `N = 1`: the punctured type is empty
    have h1 : N = 1 := by omega
    rw [h1, Nat.sub_self, Nat.cast_zero, div_zero, sub_zero, Nat.cast_one, div_one, div_one,
      abs_of_nonneg (Nat.cast_nonneg _)]
    have : t ≤ 1 := by
      rw [ht]
      exact (card_le_univ _).trans h1.le
    exact_mod_cast this
  · have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1r : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - 1 by omega)
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN1, Nat.cast_one]
    have hstr : (s : ℝ) ≤ t := by exact_mod_cast hst
    have htsr : (t : ℝ) ≤ s + 1 := by exact_mod_cast hts
    have hsNr : (s : ℝ) ≤ (N : ℝ) - 1 := by rw [← hcast]; exact_mod_cast hsN
    rw [abs_sub_le_iff]
    constructor
    · -- `t/N ≤ (s+1)/N ≤ s/(N−1) + 1/N`
      have h1 : (t : ℝ) / N ≤ (s + 1) / N := div_le_div_of_nonneg_right htsr hNr.le
      have h2 : (s : ℝ) / N ≤ s / ((N - 1 : ℕ) : ℝ) := by
        rw [hcast] at hN1r ⊢
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hN1r (by linarith)
      rw [add_div] at h1
      linarith
    · -- `s/(N−1) ≤ (s+1)/N ≤ t/N + 1/N`
      have h1 : (s : ℝ) / ((N - 1 : ℕ) : ℝ) ≤ (s + 1) / N := by
        rw [hcast] at hN1r ⊢
        rw [div_le_div_iff₀ hN1r hNr]
        nlinarith
      have h2 : ((s : ℝ) + 1) / N ≤ t / N + 1 / N := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hNr.le
      linarith

/-- **The square of a uniform unit is within `1/q` of a uniform generator of `G_q`**
(Claim-107.a, missing in the text): the uniform element of `G_q` (`pushesUniform_sqTo_safe`)
and the uniform element of `G_q ∖ {1}` (the text's "`y ← Gen_q`") are within statistical
distance `1/q`.

**Proof sketch.** For a test set `S ⊆ G_q`, the two probabilities are `|S|/q` and
`|S ∖ {1}|/(q − 1)`; both lie between `|S ∖ {1}|/q` and `|S ∖ {1}|/q + 1/q`
(`uprob_eq_card_filter`, `card_QR_safe`, `Fintype.card_subtype_compl`); transport the first
along `pushesUniform_sqTo_safe` (`PushesUniform.uprob_eq`). -/
theorem statClose_sq_generator {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p = 2 * q + 1) :
    StatClose (sqTo p) (fun y : {y : QR p // y ≠ 1} => (y : QR p)) (1 / (q : ℝ)) := by
  rw [statClose_iff]
  intro T
  rw [(pushesUniform_sqTo_safe hpq).uprob_eq T]
  have h := dlc_abs_uprob_sub_uprob_ne_le (1 : QR p) T
  rwa [← Nat.card_eq_fintype_card, card_QR_safe hpq] at h

/-! ## The DDH assumption [PS10, Assumption 105.1] -/

/-- The DDH tuple `⟨⟨p, ⟨q, y⟩⟩, ⟨y^a, ⟨y^b, y^c⟩⟩⟩` at the instance `i` with exponents
`a, b, c ∈ Z_q` (the text's `(p, y, y^a, y^b, y^c)`), with `n`-bit numerals. -/
noncomputable def ddhTuple (i : List Bool) (a b c : ZMod (expOrd i)) : List Bool :=
  pairEncode i (pairEncode (expF i a) (pairEncode (expF i b) (expF i c)))

/-- The length `15n + 14` of a DDH tuple of `n`-bit numerals. -/
def ddhLen : PolyExpr := .add (.mul (.const 15) .var) (.const 14)

/-- `ddhLen.eval n = 15n + 14`. -/
@[simp] theorem eval_ddhLen (n : ℕ) : ddhLen.eval n = 15 * n + 14 := rfl

/-- A DDH tuple at a well-formed index has length exactly `15n + 14` (the padding of the
ensembles is lossless). -/
theorem length_ddhTuple {n : ℕ} {i : List Bool} (h : WellFormedIndex n i) (a b c : ZMod (expOrd i)) :
    (ddhTuple i a b c).length = 15 * n + 14 := by
  have hw := h.dlW_eq
  simp only [ddhTuple, expF_eq, length_pairEncode, length_natToList, h.length_eq, hw]
  ring

/-- **An exponent of `Z_{expOrd i}` from a block of `n · n` coins** by rejection: `n` trials of
`n`-bit blocks, each reading the bit length of `expOrd i` bits (`sampleBelowL`), with the
fallback `0` — the exponent sampler of El Gamal's `Gen` and `Enc` (`egGenParts`, `egEncParts`:
`sampleBelowL (dlM i) (Nat.size (dlM i)) n n` on an `n · n`-bit coin segment, the same numbers
at a valid index by `expOrd_of_valid`) on typed coins. Its law is within `(1/2)^n` of uniform
at a valid well-formed index (`ddhExpo_statClose`, D10).

Repair (run-3 audit P8-1): the exponents of the DDH ensembles are read from fixed-length coin
blocks instead of being ideal coordinates of a dependent-sum seed (module docstring). -/
noncomputable def ddhExpo (n : ℕ) (i : List Bool) (b : Fin (n * n) → Bool) : ZMod (expOrd i) :=
  (((sampleBelowL (expOrd i) (Nat.size (expOrd i)) n n (List.ofFn b)).getD 0 : ℕ) : ZMod (expOrd i))

/-- `((x : ℕ) : ZMod m) = x` for `x : ZMod m` read through `ZMod.finEquiv` (the identification
of the uniform `Fin m` with the uniform `ZMod m` used by `ddhExpo_statClose`). -/
private theorem natCast_val_finEquiv_symm {m : ℕ} [NeZero m] (t : ZMod m) :
    ((((ZMod.finEquiv m).symm t : Fin m) : ℕ) : ZMod m) = t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  exact ZMod.natCast_zmod_val t

/-- **The DDH exponents are close to uniform**: at a valid index of `n`-bit numerals,
`ddhExpo n i` is within statistical distance `(1/2)^n` of the uniform element of
`Z_{expOrd i}` (D10).

**Proof sketch.** `0 < expOrd i = dlM i < dlP i < 2^n` (`expOrd_of_valid`, `dlP_lt_two_pow`,
`WellFormedIndex.dlW_eq`), so `statClose_sampleBelowL` applies; map both samplers by
`Nat.cast : ℕ → ZMod (expOrd i)` (`StatClose.map`) and identify the image of the uniform
`Fin (expOrd i)` with the uniform `ZMod (expOrd i)` along `ZMod.finEquiv`
(`StatClose.comp_equiv_right`, `natCast_val_finEquiv_symm`). -/
theorem ddhExpo_statClose {n : ℕ} {i : List Bool} (hv : ExpValid i) (hw : WellFormedIndex n i) :
    StatClose (ddhExpo n i) (id : ZMod (expOrd i) → ZMod (expOrd i)) ((1 / 2 : ℝ) ^ n) := by
  have hm : 0 < expOrd i := NeZero.pos _
  have hmn : expOrd i < 2 ^ n := by
    rw [expOrd_of_valid hv, ← hw.dlW_eq]
    exact ((expValid_iff i).1 hv).2.2.1.trans (dlP_lt_two_pow i)
  have h := ((statClose_sampleBelowL hm hmn).map fun v : ℕ => (v : ZMod (expOrd i))).comp_equiv_right
    (ZMod.finEquiv (expOrd i)).symm.toEquiv
  have hY : (fun t : ZMod (expOrd i) =>
      ((((ZMod.finEquiv (expOrd i)).symm.toEquiv t : Fin (expOrd i)) : ℕ) : ZMod (expOrd i))) = id :=
    funext fun t => natCast_val_finEquiv_symm t
  rw [hY] at h
  exact h

/-- **The DDH ensemble** `{p ← Π̃_n; y ← Gen_q; a, b ← Z_q : (p, y, y^a, y^b, y^{ab})}` of
[PS10, Assumption 105.1]: a seed is the generator's coin string together with two blocks of
`n · n` coins from which the exponents `a, b ∈ Z_q` of the generated instance are read by
rejection (`ddhExpo`); the sample is the DDH tuple padded to `15n + 14` bits (exactly its
length from `n₀` on, `length_ddhTuple`). The seed type is a product of coin types, so the
uniform seed gives the generator uniform coins (D6) and is nonempty (`Ensemble.nonempty`,
run-3 audit P2-2, by instance resolution).

Repair (run-3 audit P8-1): the run-2 seed type `Σ r : G.gen.Coins n, Z_{q_r} × Z_{q_r}` gave
the coin string `r` probability `q_r² / Σ_r q_r²` under the uniform seed, so the instance law
depended on the fibre sizes and differed from `ddhRandom`'s (cubes), which could make
`DDHAssumption` false for reasons unrelated to DDH (DESIGN §5 item 20). -/
noncomputable def ddhReal (G : SafePrimeGen) : Ensemble ddhLen where
  σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))
  X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1) (ddhExpo n (G.gen.runAt n [] z.1) z.2.2)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1 * ddhExpo n (G.gen.runAt n [] z.1) z.2.2))

/-- **The random ensemble** `{p ← Π̃_n; y ← Gen_q; a, b, z ← Z_q : (p, y, y^a, y^b, y^z)}` of
[PS10, Assumption 105.1]: the generator's coins and three blocks of `n · n` coins for the
exponents `a, b, z` (`ddhExpo`); seeds nonempty by instance resolution (run-3 audit P2-2).

Repair (run-3 audit P8-1): product seeds instead of the dependent sum (see `ddhReal`). -/
noncomputable def ddhRandom (G : SafePrimeGen) : Ensemble ddhLen where
  σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool) × (Fin (n * n) → Bool))
  X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.1) (ddhExpo n (G.gen.runAt n [] z.1) z.2.2.1)
    (ddhExpo n (G.gen.runAt n [] z.1) z.2.2.2))

/-- **The decisional Diffie–Hellman assumption** [PS10, Assumption 105.1] relative to a
safe-prime instance generator `G`: the ensembles `{(p, y, y^a, y^b, y^{ab})}` and
`{(p, y, y^a, y^b, y^z)}` are computationally indistinguishable (`Ensemble.Indist`,
[PS10, Definition 69.4]).

**Deviation:** the instance law is the generator's (the text's ideal `p ← Π̃_n; y ← Gen_q`);
the exponents are read from `n · n`-bit seed blocks by rejection, within `2^{-n}` of uniform
in `Z_q` (`ddhExpo`, D10; run-3 audit P8-1 — equivalent to the ideal-exponent form up to a
negligible statistical term); the tuple is a bit string of `15n + 14` bits; the
distinguisher receives `1^n` (D5). -/
def DDHAssumption (G : SafePrimeGen) : Prop := (ddhReal G).Indist (ddhRandom G)

/-- Unfolding: the DDH assumption is the indistinguishability of `ddhReal G` and
`ddhRandom G`. -/
theorem ddhAssumption_iff (G : SafePrimeGen) :
    DDHAssumption G ↔ (ddhReal G).Indist (ddhRandom G) := Iff.rfl

/-- The DDH tuple is the instance paired with the three encoded powers. -/
theorem ddhTuple_eq (i : List Bool) (a b c : ZMod (expOrd i)) :
    ddhTuple i a b c = pairEncode i (pairEncode (expF i a) (pairEncode (expF i b) (expF i c))) := rfl

/-- The DDH exponent is the rejection sampler's result, with fallback zero, cast to the
exponent group. -/
theorem ddhExpo_eq (n : ℕ) (i : List Bool) (b : Fin (n * n) → Bool) :
    ddhExpo n i b =
      (((sampleBelowL (expOrd i) (Nat.size (expOrd i)) n n (List.ofFn b)).getD 0 : ℕ) :
        ZMod (expOrd i)) := rfl

/-- The real experiment uses the generator's coins and two independent exponent blocks. -/
theorem ddhReal_σ (G : SafePrimeGen) (n : ℕ) :
    (ddhReal G).σ n = (G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))) := rfl

/-- The random experiment uses the generator's coins and three independent exponent blocks. -/
theorem ddhRandom_σ (G : SafePrimeGen) (n : ℕ) :
    (ddhRandom G).σ n =
      (G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool) × (Fin (n * n) → Bool))) := rfl

/-- The real sample uses the product of the two sampled exponents in its third power. -/
theorem ddhReal_X (G : SafePrimeGen) (n : ℕ)
    (z : G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))) :
    (ddhReal G).X n (cast (ddhReal_σ G n).symm z) =
      padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
        (ddhExpo n (G.gen.runAt n [] z.1) z.2.1) (ddhExpo n (G.gen.runAt n [] z.1) z.2.2)
        (ddhExpo n (G.gen.runAt n [] z.1) z.2.1 * ddhExpo n (G.gen.runAt n [] z.1) z.2.2)) := rfl

/-- The random sample uses an independent third sampled exponent. -/
theorem ddhRandom_X (G : SafePrimeGen) (n : ℕ)
    (z : G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool) × (Fin (n * n) → Bool))) :
    (ddhRandom G).X n (cast (ddhRandom_σ G n).symm z) =
      padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
        (ddhExpo n (G.gen.runAt n [] z.1) z.2.1) (ddhExpo n (G.gen.runAt n [] z.1) z.2.2.1)
        (ddhExpo n (G.gen.runAt n [] z.1) z.2.2.2)) := rfl

end TCSlib.Cryptography.Candidates
