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
# The DDH assumption and El Gamal encryption

[PS10, §3.11]: the *decisional Diffie–Hellman assumption* in the order-`q` subgroup `G_q` of
`Z_p^*` for a safe prime `p = 2q + 1` [PS10, Assumption 105.1], the group facts behind it
(p. 106: `G_q` is the subgroup of squares, cyclic of prime order, every element `≠ 1`
generates, squaring is `2`-to-`1` onto it), the El Gamal public-key encryption scheme
[PS10, Algorithm 106.2] and its security under DDH [PS10, Theorem 107.3, "we leave the formal
proof as an exercise"].

**Instances and the two generators.** Safe primes come from a safe-prime instance generator
`G : SafePrimeGen` (`TCSlib.Cryptography.Candidates.DiscreteLog`; the text's "pick a safe
prime `p = 2q + 1` of length `n`"); El Gamal's `Gen` follows the text and draws its own
`h = g²` for a uniform unit `g` (the generator component of `G`'s output is ignored). The DDH
assumption is stated for the *derived* generator `egGroupGen H G`, which outputs the same
`(p, q)` and `h = g²`, replaced by the fixed generator `4 = 2²` on the event `g² = 1`
(probability `1/q`, Claim-107.a): the law of its `h` is the "`y ← Gen_q`" of
Assumption 105.1 up to this term, which is where the `1/q` of Theorem 107.3 comes from.

**Message space.** With arbitrary `m ∈ Z_p^*` the scheme is insecure under DDH on `G_q` (the
Legendre symbol of `c₂` reveals the coset of `m`, source error 28), so the message space is
`G_q`: `Enc` canonicalises its message (`egCanon`: a numeral not reading as an element of
`G_q` is encrypted as `1`). Since the message space depends on the key, security is stated
in the chosen-message form `GroupPKScheme.Secure`: the two messages are produced by a
non-uniform PPT *selector* `M(1^n, pk)`; the constant selectors (messages hard-wired as
advice) recover the quantifier form of [PS10, Definition 102.2] (`GroupPKScheme.Secure.const`).

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the DDH ensembles draw `(p, q, y)` from the instance
generator (the text's ideal `p ← Π̃_n; y ← Gen_q`) and the exponents `a, b, z ∈ Z_q` by
rejection from blocks of `n · n` seed coins, within `2^{-n}` of uniform at the generated
instance (`ddhExpo`, D10 — the inventory's recommendation for Assumption 105.1; equivalent to
the ideal-exponent form up to a negligible statistical term), encoded as
`⟨⟨p, ⟨q, y⟩⟩, ⟨y^a, ⟨y^b, y^c⟩⟩⟩` of `n`-bit numerals, length `15n + 14`; El Gamal's `Gen`
draws `g ← Z_p^*` by rejection (the text's `g ∈ Z_p` may be `0, ±1`, source error 28) and
`a, b ← Z_q` by the same rejection sampler (D10); `pk = ⟨⟨p, ⟨q, h⟩⟩, h^a⟩` carries `q`; `Dec`
is a deterministic string function; messages are canonicalised into `G_q`; security is the
chosen-message form; the safe prime has full length `n` except on a negligible set of the
generator's coins (`ExpGroupGen.FullLengthExcept`).

**Run-3 audit repairs.** P8-1: the run-2 DDH ensembles had dependent-sum seeds
`Σ r, Z_{q_r} × Z_{q_r}` (resp. three factors), on which the uniform seed gives the coin string
`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — so the two ensembles
could have different instance laws, and when `q` varies non-negligibly with the coins (two
orders `q`, `3q/2` on half the coins each give the laws `(4/13, 9/13)` and `(8/35, 27/35)`) a
threshold test `[q ≥ θ_n]` distinguished them, making `DDHAssumption` false for reasons
unrelated to DDH. The seeds are now product types (uniform coins for the generator, D6)
with the exponents read by `ddhExpo`. P8-2: `elGamal_secure`'s hypothesis `G.FullLength`
(full length on every coin string) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.

## Main definitions

* `TCSlib.Cryptography.Candidates.ddhTuple`, `ddhLen`, `ddhExpo`, `ddhReal`, `ddhRandom`,
  `TCSlib.Cryptography.Candidates.DDHAssumption` — [PS10, Assumption 105.1].
* `TCSlib.Cryptography.Candidates.GroupPKScheme`, `GroupPKScheme.challenge`,
  `GroupPKScheme.Secure`, `constSelector` — public-key schemes with a key-dependent message
  space and their security (the form of [PS10, Definition 102.2] for `G_q`).
* `TCSlib.Cryptography.Candidates.egUnit`, `egCanon`, `egGenParts`, `egGen`, `egEncParts`,
  `egEnc`, `egDecStr`, `elGamal` — El Gamal [PS10, Algorithm 106.2].
* `TCSlib.Cryptography.Candidates.egSquareGen`, `egGroupParts`, `egGroupGen` — the derived
  safe-prime instance generator with `h = g²` (fallback `4`).

## Main results

* `TCSlib.Cryptography.Candidates.card_QR_safe`, `mem_QR_iff_pow_eq_one`,
  `orderOf_eq_of_mem_QR`, `zpowers_eq_QR`, `eq_QR_of_card`, `card_sqrt_safe`,
  `pushesUniform_sqTo_safe` — the group facts of p. 106 (NT-105.a, proved).
* `TCSlib.Cryptography.Candidates.uprob_sq_eq_one`, `statClose_of_uprob_ne`,
  `statClose_sq_generator` — the generator-versus-square term `1/q` (Claim-107.a).
* `TCSlib.Cryptography.Candidates.ddhExpo_statClose` — the DDH exponents are within `(1/2)^n`
  of uniform at a generated instance (D10).
* `TCSlib.Cryptography.Candidates.egSquareGen_valid` — the derived generator is valid
  (proved); `egGroupGen_runAt`, `egGen_runAt`, `egEnc_runAt`, `egDecStr_apply` — unfolding.
* `TCSlib.Cryptography.Candidates.elGamal_correct` — correctness of [PS10, Algorithm 106.2].
* `TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const` — constant messages.
* `TCSlib.Cryptography.Candidates.elGamal_secure` — [PS10, Theorem 107.3].

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

attribute [local irreducible] Complexity.NUPPT.Uniform Complexity.NUPPT.advInput Complexity.NUPPT.coinLen Complexity.NUPPT.distinguisher Complexity.NUPPT.distinguisherL Complexity.NUPPT.inArg Complexity.NUPPT.inCoins Complexity.NUPPT.inParam Complexity.NUPPT.layout Complexity.NUPPT.ofPolyTimeUniform Complexity.NUPPT.output Complexity.NUPPT.runAt Complexity.NUPPT.runAtL Complexity.PolyTimeComputable Complexity.pairFstD Complexity.pairSndD Complexity.polyTimeComputable_iterateFind.match_1 TCSlib.Cryptography.Candidates.ExpGroupGen.FullLengthExcept TCSlib.Cryptography.Candidates.ExpValid TCSlib.Cryptography.Candidates.SafePrimeValid TCSlib.Cryptography.Candidates.WellFormedIndex TCSlib.Cryptography.Candidates.addStr TCSlib.Cryptography.Candidates.divModStr TCSlib.Cryptography.Candidates.dlG TCSlib.Cryptography.Candidates.dlM TCSlib.Cryptography.Candidates.dlP TCSlib.Cryptography.Candidates.dlW TCSlib.Cryptography.Candidates.expF TCSlib.Cryptography.Candidates.expOrd TCSlib.Cryptography.Candidates.leStr TCSlib.Cryptography.Candidates.modExpStr TCSlib.Cryptography.Candidates.mulStr TCSlib.Cryptography.Candidates.natToBits TCSlib.Cryptography.Candidates.natToList TCSlib.Cryptography.Candidates.rejectBlocksL TCSlib.Cryptography.Candidates.sampleBelowL TCSlib.Cryptography.Candidates.sizeStr TCSlib.Cryptography.Candidates.subStr TCSlib.Cryptography.Candidates.xgcdStr TCSlib.Cryptography.Ensemble.Indist TCSlib.Cryptography.HardcoreBit.PushesUniform TCSlib.Cryptography.Negligible TCSlib.Cryptography.NumberTheory.QR TCSlib.Cryptography.NumberTheory.instDecidablePredUnitsZModMemSubgroupQROfNeZeroNat TCSlib.Cryptography.NumberTheory.listToNat TCSlib.Cryptography.NumberTheory.sqTo TCSlib.Cryptography.StatClose TCSlib.Cryptography.acceptProb TCSlib.Cryptography.decodeFin TCSlib.Cryptography.distAdv TCSlib.Cryptography.padFin TCSlib.Cryptography.splitCoins TCSlib.Cryptography.uexp TCSlib.Cryptography.uprob Turing.pairEncode

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
an event probabilities `t/N` and `s/(N − 1)` with `s ≤ t ≤ s + 1` and `s ≤ N − 1`. -/
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

/-! ## Public-key schemes with a key-dependent message space -/

/-- A **public-key encryption scheme with a key-dependent message space** (the shape of
[PS10, Definition 102.1] for El Gamal, whose messages are elements of the group `G_q`
determined by the public key): a PPT key generator `Gen(1^n) = ⟨pk, sk⟩`, a PPT encryptor
`Enc_pk(m)` activated on `⟨pk, m⟩`, and a deterministic polynomial-time decryptor on
`⟨sk, c⟩`. Correctness is stated per scheme (`elGamal_correct`), since it only holds for the
messages of the key's group.

**Deviation:** `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the
canonical message — here the message space is key-dependent and correctness is stated as a
separate theorem. -/
structure GroupPKScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(m)`, activated on `⟨pk, m⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec

namespace GroupPKScheme

/-- The challenge distribution `{(pk, sk) ← Gen(1^n); ⟨m₀, m₁⟩ ← M(1^n, pk) : ⟨pk, Enc_pk(m_b)⟩}`
for a message selector `M` and the bit `b` (the sampler over the coins of `Gen`, `M` and `Enc`). -/
def challenge (S : GroupPKScheme) (n : ℕ) (M : NUPPT) (b : Bool) :
    S.gen.Coins n × (M.Coins n × S.enc.Coins n) → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1))
      (if b then pairSndD (M.runAt n (pairFstD (S.gen.runAt n [] r.1)) r.2.1)
        else pairFstD (M.runAt n (pairFstD (S.gen.runAt n [] r.1)) r.2.1))) r.2.2)

/-- **Security with a key-dependent message space** (the form of [PS10, Definition 102.2]
used for El Gamal): for every non-uniform PPT message selector `M` and distinguisher `D` there
is a negligible `ε` with, for all `n`, advantage at most `ε(n)` between `⟨pk, Enc_pk(m₀)⟩` and
`⟨pk, Enc_pk(m₁)⟩` for `⟨m₀, m₁⟩ ← M(1^n, pk)`.

**Deviation:** the text's "for all `m₀, m₁ ∈ {0,1}^n`" becomes "for all selectors `M`"
(the messages must lie in the group of the key, so they are functions of `pk`; constant
messages are the selectors returning their advice, `Secure.const`); `D` receives `1^n`. -/
def Secure (S : GroupPKScheme) : Prop :=
  ∀ M D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    distAdv (S.challenge n M false) (S.challenge n M true) (D.distinguisherL n) ≤ ε n

end GroupPKScheme

/-- **The constant message selector**: the non-uniform PPT with no coins returning its advice
`⟨m₀(n), m₁(n)⟩` (length bounded by the syntactic polynomial `b`), whatever the public key. -/
noncomputable def constSelector (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) : NUPPT :=
  NUPPT.ofPolyTime NUPPT.polyTimeComputable_inAdvice (.const 0) b (fun n => pairEncode (m₀ n) (m₁ n)) hb

/-- The constant selector outputs `⟨m₀(n), m₁(n)⟩` on every input. -/
theorem constSelector_runAt (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (n : ℕ) (pk : List Bool)
    (r : (constSelector m₀ m₁ b hb).Coins n) :
    (constSelector m₀ m₁ b hb).runAt n pk r = pairEncode (m₀ n) (m₁ n) := by
  rw [NUPPT.runAt_eq]
  unfold constSelector
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.inAdvice_eq]

/-- The coins of the constant selector form a one-element type. -/
instance constSelector_unique (m₀ m₁ : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (n : ℕ) :
    Unique ((constSelector m₀ m₁ b hb).Coins n) :=
  haveI : IsEmpty (Fin ((constSelector m₀ m₁ b hb).coinLen n)) :=
    ⟨fun i => absurd i.2 (by simp [constSelector, NUPPT.coinLen_eq])⟩
  Pi.uniqueOfIsEmpty _

/-- **Constant messages** (the quantifier form of [PS10, Definition 102.2]): a secure scheme
has, for every pair of message families `m₀, m₁` of polynomially bounded length and every
distinguisher `D`, a negligible `ε` with advantage at most `ε(n)` between `⟨pk, Enc_pk(m₀(n))⟩`
and `⟨pk, Enc_pk(m₁(n))⟩`.

**Proof sketch.** Apply `h` to `constSelector m₀ m₁ b hb` and `D`; by `constSelector_runAt`
the challenge samplers are the constant-message samplers composed with the projection that
forgets the selector's (unique) coin, so `acceptProb_comp_equiv` with
`Equiv.prodCongr (Equiv.refl _) (Equiv.uniqueProd _ _).symm` identifies the advantages. -/
theorem GroupPKScheme.Secure.const {S : GroupPKScheme} (h : S.Secure) (m₀ m₁ : ℕ → List Bool)
    (b : PolyExpr) (hb : ∀ n, (pairEncode (m₀ n) (m₁ n)).length ≤ b.eval n) (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      distAdv (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
          (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₀ n)) r.2))
        (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
          (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₁ n)) r.2))
        (D.distinguisherL n) ≤ ε n := by
  obtain ⟨ε, hε, hle⟩ := h (constSelector m₀ m₁ b hb) D
  refine ⟨ε, hε, fun n => le_of_eq_of_le ?_ (hle n)⟩
  let e : S.gen.Coins n × S.enc.Coins n ≃
      S.gen.Coins n × ((constSelector m₀ m₁ b hb).Coins n × S.enc.Coins n) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.uniqueProd _ _).symm
  rw [distAdv_def, distAdv_def,
    ← acceptProb_comp_equiv e (S.challenge n (constSelector m₀ m₁ b hb) false),
    ← acceptProb_comp_equiv e (S.challenge n (constSelector m₀ m₁ b hb) true)]
  have h0 : (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
        (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₀ n)) r.2)) =
      fun s => S.challenge n (constSelector m₀ m₁ b hb) false (e s) := by
    funext r; simp [e, GroupPKScheme.challenge, constSelector_runAt]
  have h1 : (fun r : S.gen.Coins n × S.enc.Coins n => pairEncode (pairFstD (S.gen.runAt n [] r.1))
        (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (m₁ n)) r.2)) =
      fun s => S.challenge n (constSelector m₀ m₁ b hb) true (e s) := by
    funext r; simp [e, GroupPKScheme.challenge, constSelector_runAt]
  rw [h0, h1]

/-! ## El Gamal [PS10, Algorithm 106.2] -/

/-- A uniform unit `g ∈ Z_p^*` by rejection: `1 + v` for `v` sampled below `p − 1`
(`sampleBelowL`, `n` trials of `n`-bit blocks); the fallback `g = 1` on failure.

**Deviation:** the text draws "a random element `g ∈ Z_p`" (possibly `0, ±1`, source
error 28). -/
def egUnit (n p : ℕ) (r : List Bool) : ℕ :=
  (sampleBelowL (p - 1) (Nat.size (p - 1)) n n r).getD 0 + 1

/-- `0 < egUnit n p r`. -/
theorem egUnit_pos (n p : ℕ) (r : List Bool) : 0 < egUnit n p r := Nat.succ_pos _

/-- `egUnit n p r < p` for `p ≥ 2`. -/
theorem egUnit_lt {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (r : List Bool) : egUnit n p r < p := by
  unfold egUnit
  match h : sampleBelowL (p - 1) (Nat.size (p - 1)) n n r with
  | some v => have := sampleBelowL_lt h; simp only [Option.getD_some]; omega
  | none => simp only [Option.getD_none]; omega

/-- **Canonicalisation of a message into `G_q`**: `m` itself when `0 < m < p` and `m^q ≡ 1
(mod p)` (i.e. `m ∈ G_q`, `mem_QR_iff_pow_eq_one`), and `1` otherwise.

**Deviation:** the message space is `G_q` (source error 28); a numeral outside it is
encrypted as the identity. -/
def egCanon (p q m : ℕ) : ℕ := if 0 < m ∧ m < p ∧ m ^ q % p = 1 then m else 1

/-- **The key material of El Gamal's `Gen`** [PS10, Algorithm 106.2] from the numerals `a, b`
of `p, q` and two coin segments: `g ← Z_p^*` (`egUnit`), `h = g² mod p`, `x ← Z_q`
(`sampleBelowL`), `pk = ⟨⟨p, ⟨q, h⟩⟩, h^x mod p⟩`, `sk = ⟨⟨p, ⟨q, h⟩⟩, x⟩`.

**Deviation:** `pk` carries `q` and `sk` carries `q` (the text's `(p, h, a)`); the exponent
is sampled by rejection with the fallback `0`. -/
def egGenParts (n : ℕ) (a b r₁ r₂ : List Bool) : List Bool × List Bool :=
  (pairEncode (pairEncode a (pairEncode b (natToList n (egUnit n (listToNat a) r₁ ^ 2 % listToNat a))))
      (natToList n ((egUnit n (listToNat a) r₁ ^ 2 % listToNat a) ^
        (sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂).getD 0 % listToNat a)),
    pairEncode (pairEncode a (pairEncode b (natToList n (egUnit n (listToNat a) r₁ ^ 2 % listToNat a))))
      (natToList n ((sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂).getD 0)))

/-- The coins of El Gamal's `Gen`: the instance generator's coins, then `n · n` coins for `g`
and `n · n` coins for `a`. -/
def egGenCoins (G : SafePrimeGen) : PolyExpr := .add G.gen.coins (.add (.mul .var .var) (.mul .var .var))

/-- The string function of El Gamal's `Gen` on the raw layout `⟨⟨⟨1^n, []⟩, α⟩, r⟩`: run the
safe-prime generator on the first coin segment to get `⟨p, ⟨q, _⟩⟩`, then `egGenParts` on the
next two segments; output `⟨pk, sk⟩`. -/
def egGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
  pairEncode
    (egGenParts (NUPPT.inParam z).length
      (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
      (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
      (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
        ((NUPPT.inParam z).length * (NUPPT.inParam z).length))
      ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length +
        (NUPPT.inParam z).length * (NUPPT.inParam z).length))).1
    (egGenParts (NUPPT.inParam z).length
      (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
      (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
      (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
        ((NUPPT.inParam z).length * (NUPPT.inParam z).length))
      ((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length +
        (NUPPT.inParam z).length * (NUPPT.inParam z).length))).2

/-! ### Helpers of the polynomial-time targets (unit dl-c)

A numeral calculus on top of the arithmetic bundle: `dlc_NumPoly F` says that the number `F z`
is the value of a polynomial-time string function of `z`. It is closed under the bundle's
operations (lossless at the widths used here), under a polynomial-time `if`, and contains the
rejection sampler `sampleBelowL` (a trial loop, `Complexity.polyTimeComputable_iterateFind`);
`dlc_poly_natToList` writes such a number as a numeral of a given width. -/

/-- The empty numeral reads as `0`. -/
private theorem dlc_listToNat_nil : listToNat [] = 0 := by
  rw [listToNat_eq]
  rfl

/-- The number read from `a ++ b` is `⟦a⟧ · 2^{|b|} + ⟦b⟧` (most significant bit first). -/
private theorem dlc_listToNat_append (a b : List Bool) :
    listToNat (a ++ b) = listToNat a * 2 ^ b.length + listToNat b := by
  have key : ∀ (l : List Bool) (acc : ℕ),
      l.foldl (fun a c => 2 * a + if c = true then 1 else 0) acc =
        acc * 2 ^ l.length + l.foldl (fun a c => 2 * a + if c = true then 1 else 0) 0 := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons c l ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih, ih (2 * 0 + _), List.length_cons, pow_succ]
      ring
  rw [listToNat_eq, listToNat_eq, listToNat_eq, List.foldl_append, key]

/-- The one-bit numeral `1` reads as `1`. -/
private theorem dlc_listToNat_true : listToNat [true] = 1 := by
  rw [listToNat_eq]
  rfl

/-- The `k`-bit numeral keeps the `k` low-order bits: `⟦N mod 2^k⟧_k = ⟦N⟧_k`. -/
private theorem dlc_natToList_mod (k N : ℕ) : natToList k (N % 2 ^ k) = natToList k N := by
  have h := natToList_length_listToNat (natToList k N)
  rw [length_natToList, listToNat_natToList_eq_mod] at h
  exact h

/-- Leading zeros do not change the number read. -/
private theorem dlc_listToNat_zeros_append (k : ℕ) (b : List Bool) :
    listToNat (natToList k 0 ++ b) = listToNat b := by
  rw [dlc_listToNat_append, listToNat_natToList (Nat.two_pow_pos k), zero_mul, zero_add]

/-- **Width normalization**: `(⟦0⟧_W ++ b).drop |b| = ⟦⟦b⟧⟧_W`. -/
private theorem dlc_drop_natToList_zero_append (W : ℕ) (b : List Bool) :
    (natToList W 0 ++ b).drop b.length = natToList W (listToNat b) := by
  set w := natToList W 0 ++ b with hw
  have hlen : (w.drop b.length).length = W := by
    rw [List.length_drop, hw, List.length_append, length_natToList]
    omega
  have hsplit : listToNat w = listToNat (w.take b.length) * 2 ^ W + listToNat (w.drop b.length) := by
    conv_lhs => rw [← List.take_append_drop b.length w]
    rw [dlc_listToNat_append, hlen]
  have hlt := listToNat_lt_two_pow (w.drop b.length)
  rw [hlen] at hlt
  have hmod : listToNat b % 2 ^ W = listToNat (w.drop b.length) := by
    rw [← dlc_listToNat_zeros_append W b, ← hw, hsplit, Nat.mul_add_mod_of_lt hlt]
  rw [← dlc_natToList_mod, hmod, ← hlen, natToList_length_listToNat]

/-- The zero numeral of the width of `w`: `subStr ⟨w, w⟩ = ⟦0⟧_{|w|}`. -/
private theorem dlc_subStr_self (w : List Bool) : subStr (pairEncode w w) = natToList w.length 0 := by
  rw [subStr_pairEncode, Nat.sub_self]

/-- `F z` is the number read from a polynomial-time string function of `z`. -/
private def dlc_NumPoly (F : List Bool → ℕ) : Prop :=
  ∃ g : List Bool → List Bool, PolyTimeComputable g ∧ ∀ z, listToNat (g z) = F z

/-- The number read from a polynomial-time string function. -/
private theorem dlc_numPoly_of_poly {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    dlc_NumPoly fun z => listToNat (f z) :=
  ⟨f, hf, fun _ => rfl⟩

/-- Pointwise equal numbers. -/
private theorem dlc_numPoly_congr {F G : List Bool → ℕ} (hF : dlc_NumPoly F) (h : ∀ z, F z = G z) :
    dlc_NumPoly G := by
  obtain ⟨f, hf, hfF⟩ := hF
  exact ⟨f, hf, fun z => (hfF z).trans (h z)⟩

/-- Constants. -/
private theorem dlc_numPoly_const (k : ℕ) : dlc_NumPoly fun _ => k :=
  ⟨fun _ => natToList (Nat.size k) k, polyTimeComputable_const _,
    fun _ => listToNat_natToList (Nat.lt_size_self k)⟩

/-- Sums (`H.add`, lossless). -/
private theorem dlc_numPoly_add (H : ArithmeticFP) {F G : List Bool → ℕ} (hF : dlc_NumPoly F)
    (hG : dlc_NumPoly G) : dlc_NumPoly fun z => F z + G z := by
  obtain ⟨f, hf, hfF⟩ := hF
  obtain ⟨g, hg, hgG⟩ := hG
  refine ⟨fun z => addStr (pairEncode (f z) (g z)), H.add.comp (hf.pairEncode hg), fun z => ?_⟩
  rw [listToNat_addStr, hfF, hgG]

/-- Truncated differences (`H.sub`, lossless). -/
private theorem dlc_numPoly_sub (H : ArithmeticFP) {F G : List Bool → ℕ} (hF : dlc_NumPoly F)
    (hG : dlc_NumPoly G) : dlc_NumPoly fun z => F z - G z := by
  obtain ⟨f, hf, hfF⟩ := hF
  obtain ⟨g, hg, hgG⟩ := hG
  refine ⟨fun z => subStr (pairEncode (f z) (g z)), H.sub.comp (hf.pairEncode hg), fun z => ?_⟩
  rw [listToNat_subStr, hfF, hgG]

/-- Products (`H.mul`, lossless at width `|a| + |b|`). -/
private theorem dlc_numPoly_mul (H : ArithmeticFP) {F G : List Bool → ℕ} (hF : dlc_NumPoly F)
    (hG : dlc_NumPoly G) : dlc_NumPoly fun z => F z * G z := by
  obtain ⟨f, hf, hfF⟩ := hF
  obtain ⟨g, hg, hgG⟩ := hG
  refine ⟨fun z => mulStr (pairEncode (f z) (g z)), H.mul.comp (hf.pairEncode hg), fun z => ?_⟩
  simp only
  rw [mulStr_pairEncode, listToNat_natToList, hfF, hgG]
  rw [pow_add]
  exact Nat.mul_lt_mul'' (listToNat_lt_two_pow _) (listToNat_lt_two_pow _)

/-- Remainders (`H.divMod` on the modulus padded by `|a|` leading zeros, so that the
remainder is lossless also for the modulus `0`). -/
private theorem dlc_numPoly_mod (H : ArithmeticFP) {F G : List Bool → ℕ} (hF : dlc_NumPoly F)
    (hG : dlc_NumPoly G) : dlc_NumPoly fun z => F z % G z := by
  obtain ⟨f, hf, hfF⟩ := hF
  obtain ⟨g, hg, hgG⟩ := hG
  refine ⟨fun z => pairSndD (divModStr (pairEncode (f z) (subStr (pairEncode (f z) (f z)) ++ g z))),
    polyTimeComputable_pairSndD.comp (H.divMod.comp (hf.pairEncode ((H.sub.comp (hf.pairEncode hf)).append hg))),
    fun z => ?_⟩
  simp only
  rw [divModStr_pairEncode, pairSndD_pairEncode, dlc_subStr_self, dlc_listToNat_zeros_append,
    listToNat_natToList, hfF, hgG]
  rw [List.length_append, length_natToList, pow_add]
  calc listToNat (f z) % listToNat (g z) ≤ listToNat (f z) := Nat.mod_le _ _
    _ < 2 ^ (f z).length := listToNat_lt_two_pow _
    _ ≤ 2 ^ (f z).length * 2 ^ (g z).length := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

/-- Modular powers for a positive modulus (`H.modExp`, lossless below the modulus). -/
private theorem dlc_numPoly_powMod (H : ArithmeticFP) {A X M : List Bool → ℕ} (hA : dlc_NumPoly A)
    (hX : dlc_NumPoly X) (hM : dlc_NumPoly M) (hpos : ∀ z, 0 < M z) :
    dlc_NumPoly fun z => A z ^ X z % M z := by
  obtain ⟨a, ha, haA⟩ := hA
  obtain ⟨x, hx, hxX⟩ := hX
  obtain ⟨m, hm, hmM⟩ := hM
  refine ⟨fun z => modExpStr (pairEncode (a z) (pairEncode (x z) (m z))),
    H.modExp.comp (ha.pairEncode (hx.pairEncode hm)), fun z => ?_⟩
  simp only
  rw [modExpStr_pairEncode, listToNat_natToList, haA, hxX, hmM]
  calc listToNat (a z) ^ listToNat (x z) % listToNat (m z) < listToNat (m z) :=
        Nat.mod_lt _ (by rw [hmM]; exact hpos z)
    _ < 2 ^ (m z).length := listToNat_lt_two_pow _

/-- The powers of two `2^{|u|}` (`1` followed by the zero numeral of the width of `u`). -/
private theorem dlc_numPoly_two_pow (H : ArithmeticFP) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) : dlc_NumPoly fun z => 2 ^ (u z).length := by
  refine ⟨fun z => [true] ++ subStr (pairEncode (u z) (u z)),
    (polyTimeComputable_prepend [true]).comp (H.sub.comp (hu.pairEncode hu)), fun z => ?_⟩
  simp only
  rw [dlc_subStr_self, dlc_listToNat_append, dlc_listToNat_true, length_natToList,
    listToNat_natToList (Nat.two_pow_pos _), one_mul, add_zero]

/-- Comparisons are polynomial-time tests (`H.le`). -/
private theorem dlc_poly_le (H : ArithmeticFP) {F G : List Bool → ℕ} (hF : dlc_NumPoly F)
    (hG : dlc_NumPoly G) : PolyTimeComputable fun z => [decide (F z ≤ G z)] := by
  obtain ⟨f, hf, hfF⟩ := hF
  obtain ⟨g, hg, hgG⟩ := hG
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp (H.le.comp (hf.pairEncode hg))
  rw [Function.comp_apply, leStr_pairEncode, hfF, hgG]

/-- Equality tests (two comparisons). -/
private theorem dlc_poly_eq (H : ArithmeticFP) {F G : List Bool → ℕ} (hF : dlc_NumPoly F)
    (hG : dlc_NumPoly G) : PolyTimeComputable fun z => [decide (F z = G z)] := by
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp
    (polyTimeComputable_and (dlc_poly_le H hF hG) (dlc_poly_le H hG hF))
  by_cases h : F z = G z
  · simp [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · simp [h, h'.not_ge]
    · simp [h, h'.not_ge]

/-- A polynomial-time choice between two numbers. -/
private theorem dlc_numPoly_ite {c : List Bool → Bool} (hc : PolyTimeComputable fun z => [c z])
    {F G : List Bool → ℕ} (hF : dlc_NumPoly F) (hG : dlc_NumPoly G) :
    dlc_NumPoly fun z => if c z then F z else G z := by
  obtain ⟨f, hf, hfF⟩ := hF
  obtain ⟨g, hg, hgG⟩ := hG
  refine ⟨fun z => if c z then f z else g z, polyTimeComputable_ite hc hf hg, fun z => ?_⟩
  show listToNat (if c z then f z else g z) = if c z then F z else G z
  cases c z
  · exact hgG z
  · exact hfF z

/-- **Numerals of a given width**: `⟦F z⟧_{|u z|}` (width normalization: the last `|b|` bits of
`⟦0⟧_{|u|} ++ b` for a string `b` reading `F z`). -/
private theorem dlc_poly_natToList (H : ArithmeticFP) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) {F : List Bool → ℕ} (hF : dlc_NumPoly F) :
    PolyTimeComputable fun z => natToList (u z).length (F z) := by
  obtain ⟨b, hb, hbF⟩ := hF
  have hq := (polyTimeComputable_pairDropPoly .var).comp
    (hb.pairEncode ((H.sub.comp (hu.pairEncode hu)).append hb))
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hq
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  rw [dlc_subStr_self, dlc_drop_natToList_zero_append, hbF]

/-- The safe modulus: `M`, or `2^n` in place of the modulus `0`. -/
private def dlc_safeMod (n M : ℕ) : ℕ := if M = 0 then 2 ^ n else M

/-- The safe modulus is positive. -/
private theorem dlc_safeMod_pos (n M : ℕ) : 0 < dlc_safeMod n M := by
  unfold dlc_safeMod
  split_ifs with h
  · exact Nat.two_pow_pos n
  · exact Nat.pos_of_ne_zero h

/-- **Reduction modulo the safe modulus** does not change an `n`-bit numeral of a remainder:
`⟦V mod M⟧_n = ⟦V mod M'⟧_n` (for `M = 0` both are the `n` low-order bits of `V`). -/
private theorem dlc_natToList_mod_safeMod (n V M : ℕ) :
    natToList n (V % M) = natToList n (V % dlc_safeMod n M) := by
  unfold dlc_safeMod
  split_ifs with h
  · rw [h, Nat.mod_zero, dlc_natToList_mod]
  · rfl

/-- The safe modulus of a polynomial-time number at the width of `u`. -/
private theorem dlc_numPoly_safeMod (H : ArithmeticFP) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) {M : List Bool → ℕ} (hM : dlc_NumPoly M) :
    dlc_NumPoly fun z => dlc_safeMod (u z).length (M z) := by
  refine dlc_numPoly_congr (dlc_numPoly_ite (dlc_poly_eq H hM (dlc_numPoly_const 0))
    (dlc_numPoly_two_pow H hu) hM) fun z => ?_
  unfold dlc_safeMod
  by_cases h : M z = 0 <;> simp [h]

/-! #### The rejection sampler as a trial loop -/

/-- One trial step on `⟨⟨u, ⟨1^k, m⟩⟩, ⟨counter, coins⟩⟩`: keep the header, decrement the
counter, drop one block of `|u|` coins. -/
private def dlc_ssStep (x : List Bool) : List Bool :=
  pairEncode (pairFstD x)
    (pairEncode ((pairFstD (pairSndD x)).drop 1) ((pairSndD (pairSndD x)).drop (pairFstD (pairFstD x)).length))

/-- The current trial value: the first `k` bits of the remaining coins. -/
private def dlc_ssBlock (x : List Bool) : List Bool :=
  (pairSndD (pairSndD x)).take (pairFstD (pairSndD (pairFstD x))).length

/-- The acceptance test: the counter is nonzero and the trial value is below `m`. -/
private def dlc_ssAcc (x : List Bool) : Bool :=
  !(decide (pairFstD (pairSndD x) = [])) &&
    !(decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (dlc_ssBlock x)))

/-- The payload: a `true` marker, then the accepted block. -/
private def dlc_ssOut (x : List Bool) : List Bool := [true] ++ dlc_ssBlock x

/-- The trial loop: the payload at the first accepted state among the first `|x| + 1`. -/
private def dlc_ssLoop (x : List Bool) : List Bool :=
  match (List.range (x.length + 1)).find? (fun i => dlc_ssAcc (dlc_ssStep^[i] x)) with
  | some i => dlc_ssOut (dlc_ssStep^[i] x)
  | none => []

private theorem dlc_ssStep_poly : PolyTimeComputable dlc_ssStep := by
  have h := polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
      ((polyTimeComputable_pairDropPoly .var).comp
        ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))))
  refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp h
  simp only [dlc_ssStep, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

private theorem dlc_ssBlock_poly : PolyTimeComputable dlc_ssBlock := by
  have h := (polyTimeComputable_pairTakePoly .var).comp
    ((polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp h
  simp only [dlc_ssBlock, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

private theorem dlc_ssAcc_poly (H : ArithmeticFP) : PolyTimeComputable fun x => [dlc_ssAcc x] := by
  have hle := dlc_poly_le H
    (dlc_numPoly_of_poly (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)))
    (dlc_numPoly_of_poly dlc_ssBlock_poly)
  have h1 := polyTimeComputable_not
    (polyTimeComputable_isNil.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  exact polyTimeComputable_and h1 (polyTimeComputable_not hle)

private theorem dlc_ssOut_poly : PolyTimeComputable dlc_ssOut :=
  (polyTimeComputable_prepend [true]).comp dlc_ssBlock_poly

/-- The orbit: after `i` trials the state is `⟨h, ⟨c.drop i, s.drop (i · |fst h|)⟩⟩`. -/
private theorem dlc_ssStep_iterate (h c s : List Bool) (i : ℕ) :
    dlc_ssStep^[i] (pairEncode h (pairEncode c s)) =
      pairEncode h (pairEncode (c.drop i) (s.drop (i * (pairFstD h).length))) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [dlc_ssStep, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
    rw [Nat.succ_mul]

private theorem dlc_length_ssStep_le (x : List Bool) : (dlc_ssStep x).length ≤ 2 * x.length + 4 := by
  have h1 := StateLoop.length_pairFstD_add_pairSndD_le x
  have h2 := StateLoop.length_pairFstD_add_pairSndD_le (pairSndD x)
  simp only [dlc_ssStep, length_pairEncode, List.length_drop]
  omega

private theorem dlc_length_ssStep_ssStep_le (x : List Bool) :
    (dlc_ssStep (dlc_ssStep x)).length ≤ (dlc_ssStep x).length := by
  simp only [dlc_ssStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
    List.length_drop]
  omega

private theorem dlc_length_ssStep_iterate_le (x : List Bool) (i : ℕ) :
    (dlc_ssStep^[i] x).length ≤ 2 * x.length + 4 := by
  cases i with
  | zero => simp only [Function.iterate_zero, id]; omega
  | succ i =>
    induction i with
    | zero => exact dlc_length_ssStep_le x
    | succ i ih =>
      rw [Function.iterate_succ_apply'] at ih ⊢
      rw [Function.iterate_succ_apply']
      exact (dlc_length_ssStep_ssStep_le _).trans ih

/-- The trial loop is polynomial-time (the repetition lemma with `R = var`). -/
private theorem dlc_ssLoop_poly (H : ArithmeticFP) : PolyTimeComputable dlc_ssLoop := by
  refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp
    (polyTimeComputable_iterateFind dlc_ssStep_poly (dlc_ssAcc_poly H) dlc_ssOut_poly
      PolyExpr.var (PolyExpr.add (.mul (.const 2) .var) (.const 4)) (fun x i _ => by
        simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
        exact dlc_length_ssStep_iterate_le x i))
  rw [PolyExpr.eval_var]
  unfold dlc_ssLoop
  split <;> split <;> simp_all

end TCSlib.Cryptography.Candidates
