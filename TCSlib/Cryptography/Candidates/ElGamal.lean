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
private theorem dlc_ssLoop_poly (H : ArithmeticFP) : PolyTimeComputable dlc_ssLoop :=
  polyTimeComputable_iterateFind dlc_ssStep_poly (dlc_ssAcc_poly H) dlc_ssOut_poly
    PolyExpr.var (PolyExpr.add (.mul (.const 2) .var) (.const 4)) (fun x i _ => by
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      exact dlc_length_ssStep_iterate_le x i)

/-- `List.findSome?` of a filter-and-map is `List.find?` followed by the map. -/
private theorem dlc_findSome?_ite {α β : Type*} (p : α → Prop) [DecidablePred p] (h : α → β)
    (l : List α) :
    l.findSome? (fun t => if p t then some (h t) else none) = (l.find? fun t => decide (p t)).map h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.find?_cons]
    by_cases ha : p a
    · rw [if_pos ha, decide_eq_true ha]
      rfl
    · rw [if_neg ha, decide_eq_false ha, ih]

/-- A search over `[0, L)` whose test also demands `i < N` is the search over `[0, N)`. -/
private theorem dlc_find?_range_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
  have hcongr : ∀ l : List ℕ, (∀ i ∈ l, i < N) →
      l.find? (fun i => decide (i < N) && p i) = l.find? p := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      rw [List.find?_cons, List.find?_cons, ih (fun i hi => hl i (List.mem_cons_of_mem a hi)),
        decide_eq_true (hl a List.mem_cons_self), Bool.true_and]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
  rw [List.range_add, List.find?_append, hcongr _ (fun i hi => List.mem_range.1 hi)]
  have hnone : (List.map (fun x => N + x) (List.range d)).find?
      (fun i => decide (i < N) && p i) = none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    simp
  rw [hnone, Option.or_none]

/-- **The trial loop computes the rejection sampler**: from `⟨⟨u, ⟨1^k, m⟩⟩, ⟨u, c⟩⟩` with
`k = Nat.size ⟦m⟧`, the number read from the payload (marker dropped) is
`sampleBelowL ⟦m⟧ k |u| |u| c` with the fallback `0` (read through
`sampleBelowL_eq_rejectBlocksL` and `rejectBlocksL_eq`). -/
private theorem dlc_ssLoop_eq (u ks ms c : List Bool) (hk : ks.length = Nat.size (listToNat ms)) :
    listToNat ((dlc_ssLoop (pairEncode (pairEncode u (pairEncode ks ms)) (pairEncode u c))).drop 1) =
      (sampleBelowL (listToNat ms) (Nat.size (listToNat ms)) u.length u.length c).getD 0 := by
  set x0 := pairEncode (pairEncode u (pairEncode ks ms)) (pairEncode u c) with hx0
  let val : ℕ → ℕ := fun i => listToNat ((c.drop (i * u.length)).take (Nat.size (listToNat ms)))
  have hblock : ∀ i, dlc_ssBlock (dlc_ssStep^[i] x0) =
      (c.drop (i * u.length)).take (Nat.size (listToNat ms)) := by
    intro i
    rw [hx0, dlc_ssStep_iterate]
    simp only [dlc_ssBlock, pairFstD_pairEncode, pairSndD_pairEncode, hk]
  have hacc : ∀ i, dlc_ssAcc (dlc_ssStep^[i] x0) =
      (decide (i < u.length) && decide (val i < listToNat ms)) := by
    intro i
    have hb := hblock i
    rw [dlc_ssAcc, hb, hx0, dlc_ssStep_iterate]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.drop_eq_nil_iff]
    by_cases h1 : i < u.length <;> by_cases h2 : val i < listToNat ms
    · simp [h1, h2, val]
    · simp [h1, h2, val, not_lt.1 h2]
    · simp [h1, h2, val]
    · simp [h1, h2, val]
  have hrange : u.length ≤ x0.length + 1 := by
    rw [hx0, length_pairEncode, length_pairEncode]
    omega
  have hfind : (List.range (x0.length + 1)).find? (fun i => dlc_ssAcc (dlc_ssStep^[i] x0)) =
      (List.range u.length).find? (fun i => decide (val i < listToNat ms)) := by
    rw [show (fun i => dlc_ssAcc (dlc_ssStep^[i] x0)) =
      fun i => decide (i < u.length) && decide (val i < listToNat ms) from funext hacc]
    exact dlc_find?_range_lt _ hrange
  have hsample : sampleBelowL (listToNat ms) (Nat.size (listToNat ms)) u.length u.length c =
      ((List.range u.length).find? (fun i => decide (val i < listToNat ms))).map val := by
    rw [sampleBelowL_eq_rejectBlocksL, rejectBlocksL_eq]
    exact dlc_findSome?_ite (fun i => val i < listToNat ms) val _
  rw [hsample]
  unfold dlc_ssLoop
  rw [hfind]
  rcases hf : (List.range u.length).find? (fun i => decide (val i < listToNat ms)) with _ | i
  · exact dlc_listToNat_nil
  · show listToNat ((dlc_ssOut (dlc_ssStep^[i] x0)).drop 1) = val i
    rw [dlc_ssOut, List.singleton_append, List.drop_one, List.tail_cons, hblock]

/-- **The rejection sampler is a polynomial-time number**: `(sampleBelowL M (Nat.size M) |u| |u| c).getD 0`
for polynomial-time `u`, `c` and `M`. -/
private theorem dlc_numPoly_sample (H : ArithmeticFP) {u c : List Bool → List Bool}
    (hu : PolyTimeComputable u) (hc : PolyTimeComputable c) {M : List Bool → ℕ} (hM : dlc_NumPoly M) :
    dlc_NumPoly fun z => (sampleBelowL (M z) (Nat.size (M z)) (u z).length (u z).length (c z)).getD 0 := by
  obtain ⟨m, hm, hmM⟩ := hM
  have hstart : PolyTimeComputable fun z =>
      pairEncode (pairEncode (u z) (pairEncode (sizeStr (m z)) (m z))) (pairEncode (u z) (c z)) :=
    (hu.pairEncode ((H.size.comp hm).pairEncode hm)).pairEncode (hu.pairEncode hc)
  refine ⟨fun z => (dlc_ssLoop (pairEncode (pairEncode (u z) (pairEncode (sizeStr (m z)) (m z)))
      (pairEncode (u z) (c z)))).drop 1, polyTimeComputable_tail.comp ((dlc_ssLoop_poly H).comp hstart),
    fun z => ?_⟩
  simp only
  rw [dlc_ssLoop_eq _ _ _ _ (length_sizeStr _), hmM]

/-- Cutting a polynomial-length prefix of `c` at the length of `u` (`polyTimeComputable_pairTakePoly`). -/
private theorem dlc_poly_take (p : PolyExpr) {u c : List Bool → List Bool} (hu : PolyTimeComputable u)
    (hc : PolyTimeComputable c) : PolyTimeComputable fun z => (c z).take (p.eval (u z).length) := by
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp
    ((polyTimeComputable_pairTakePoly p).comp (hu.pairEncode hc))
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- Dropping a polynomial-length prefix of `c` at the length of `u` (`polyTimeComputable_pairDropPoly`). -/
private theorem dlc_poly_drop (p : PolyExpr) {u c : List Bool → List Bool} (hu : PolyTimeComputable u)
    (hc : PolyTimeComputable c) : PolyTimeComputable fun z => (c z).drop (p.eval (u z).length) := by
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp
    ((polyTimeComputable_pairDropPoly p).comp (hu.pairEncode hc))
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- `egUnit` of polynomial-time data is a polynomial-time number. -/
private theorem dlc_numPoly_egUnit (H : ArithmeticFP) {u a r : List Bool → List Bool}
    (hu : PolyTimeComputable u) (ha : PolyTimeComputable a) (hr : PolyTimeComputable r) :
    dlc_NumPoly fun z => egUnit (u z).length (listToNat (a z)) (r z) :=
  dlc_numPoly_add H (dlc_numPoly_sample H hu hr (dlc_numPoly_sub H (dlc_numPoly_of_poly ha)
    (dlc_numPoly_const 1))) (dlc_numPoly_const 1)

/-- `g² mod p` for `g = egUnit …` is a polynomial-time number. -/
private theorem dlc_numPoly_egUnit_sq (H : ArithmeticFP) {u a r : List Bool → List Bool}
    (hu : PolyTimeComputable u) (ha : PolyTimeComputable a) (hr : PolyTimeComputable r) :
    dlc_NumPoly fun z => egUnit (u z).length (listToNat (a z)) (r z) ^ 2 % listToNat (a z) :=
  dlc_numPoly_congr (dlc_numPoly_mod H (dlc_numPoly_mul H (dlc_numPoly_egUnit H hu ha hr)
    (dlc_numPoly_egUnit H hu ha hr)) (dlc_numPoly_of_poly ha)) fun z => by rw [sq]

/-- `⟦A^X mod M⟧_{|u|}` for polynomial-time numbers (through the safe modulus). -/
private theorem dlc_poly_natToList_powMod (H : ArithmeticFP) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) {A X M : List Bool → ℕ} (hA : dlc_NumPoly A) (hX : dlc_NumPoly X)
    (hM : dlc_NumPoly M) :
    PolyTimeComputable fun z => natToList (u z).length (A z ^ X z % M z) := by
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp (dlc_poly_natToList H hu
    (dlc_numPoly_powMod H hA hX (dlc_numPoly_safeMod H hu hM) fun z => dlc_safeMod_pos _ _))
  exact (dlc_natToList_mod_safeMod _ _ _).symm

/-- `⟦A^X · C mod M⟧_{|u|}` for polynomial-time numbers (through the safe modulus). -/
private theorem dlc_poly_natToList_powMulMod (H : ArithmeticFP) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) {A X C M : List Bool → ℕ} (hA : dlc_NumPoly A) (hX : dlc_NumPoly X)
    (hC : dlc_NumPoly C) (hM : dlc_NumPoly M) :
    PolyTimeComputable fun z => natToList (u z).length (A z ^ X z * C z % M z) := by
  have hS := dlc_numPoly_safeMod H hu hM
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp (dlc_poly_natToList H hu
    (dlc_numPoly_mod H (dlc_numPoly_mul H (dlc_numPoly_powMod H hA hX hS fun z => dlc_safeMod_pos _ _)
      hC) hS))
  rw [Nat.mod_mul_mod]
  exact (dlc_natToList_mod_safeMod _ _ _).symm

/-- The key material `egGenParts` of polynomial-time data is polynomial-time. -/
private theorem dlc_poly_egGenParts (H : ArithmeticFP) {u a b r₁ r₂ : List Bool → List Bool}
    (hu : PolyTimeComputable u) (ha : PolyTimeComputable a) (hb : PolyTimeComputable b)
    (hr₁ : PolyTimeComputable r₁) (hr₂ : PolyTimeComputable r₂) :
    PolyTimeComputable fun z => pairEncode (egGenParts (u z).length (a z) (b z) (r₁ z) (r₂ z)).1
      (egGenParts (u z).length (a z) (b z) (r₁ z) (r₂ z)).2 := by
  have hh := dlc_numPoly_egUnit_sq H hu ha hr₁
  have hx := dlc_numPoly_sample H hu hr₂ (dlc_numPoly_of_poly hb)
  have hpk := ha.pairEncode (hb.pairEncode (dlc_poly_natToList H hu hh))
  exact (hpk.pairEncode (dlc_poly_natToList_powMod H hu hh hx (dlc_numPoly_of_poly ha))).pairEncode
    (hpk.pairEncode (dlc_poly_natToList H hu hx))

/-- The output of `G.gen` on the first coin segment, as a function of the raw layout. -/
private theorem dlc_poly_genOut (G : SafePrimeGen) :
    PolyTimeComputable fun z => G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))) :=
  G.gen.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
    (polyTimeComputable_const []) (polyTimeComputable_const [])
    (dlc_poly_take G.gen.coins NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inCoins))

/-- **El Gamal's `Gen` is polynomial-time** given the arithmetic bundle.

**Proof sketch.** Cut the coins at the unary lengths `1^{coins(n)}` and `1^{n·n}`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly` on `⟨1^n, r⟩`); run `G.gen.output` on the
layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`); the two
rejection loops are `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the
test `H.le` (the decrement `p − 1` and the bit length `Nat.size`: `H.sub`, `H.size`);
`h = g² mod p` and `h^x mod p` by `H.modExp`; the numerals are padded to width `n`
(`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
theorem polyTimeComputable_egGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
    PolyTimeComputable (egGenRaw G) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hc := NUPPT.polyTimeComputable_inCoins
  have hO := dlc_poly_genOut G
  have h := dlc_poly_egGenParts H hu (polyTimeComputable_pairFstD.comp hO)
    (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hO))
    (dlc_poly_take (.mul .var .var) hu (dlc_poly_drop G.gen.coins hu hc))
    (dlc_poly_drop (.add G.gen.coins (.mul .var .var)) hu hc)
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [Function.comp_apply, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var]
  rfl


/-- **El Gamal's key generator** `Gen(1^n) = ⟨pk, sk⟩` as a uniform `NUPPT`. -/
noncomputable def egGen (H : ArithmeticFP) (G : SafePrimeGen) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egGenRaw H G) (egGenCoins G)

/-- The activation of `Gen`: `⟨pk, sk⟩ = egGenParts` on the safe-prime generator's output and
the coin segments. -/
theorem egGen_runAt (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : (egGen H G).Coins n) :
    (egGen H G).runAt n [] r =
      pairEncode
        (egGenParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
          (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
          (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
          ((List.ofFn r).drop (G.gen.coinLen n + n * n))).1
        (egGenParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
          (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
          (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
          ((List.ofFn r).drop (G.gen.coinLen n + n * n))).2 := by
  rw [NUPPT.runAt_eq]
  unfold egGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [egGenRaw, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, NUPPT.layout_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.Uniform.runAtL_eq G.gen_uniform, NUPPT.coinLen_eq]

/-- **The ciphertext of El Gamal's `Enc`** [PS10, Algorithm 106.2] on the public key
`pk = ⟨⟨p, ⟨q, h⟩⟩, A⟩` (`A = h^a`), the message numeral `m` and coins `r`: `b ← Z_q`
(`sampleBelowL`), output `⟨h^b mod p, A^b · m' mod p⟩` with `m' = egCanon p q m`. -/
def egEncParts (n : ℕ) (pk m r : List Bool) : List Bool :=
  pairEncode
    (natToList n (dlG (pairFstD pk) ^
      (sampleBelowL (dlM (pairFstD pk)) (Nat.size (dlM (pairFstD pk))) n n r).getD 0 % dlP (pairFstD pk)))
    (natToList n (listToNat (pairSndD pk) ^
      (sampleBelowL (dlM (pairFstD pk)) (Nat.size (dlM (pairFstD pk))) n n r).getD 0 *
        egCanon (dlP (pairFstD pk)) (dlM (pairFstD pk)) (listToNat m) % dlP (pairFstD pk)))

/-- The string function of `Enc` on the raw layout `⟨⟨⟨1^n, ⟨pk, m⟩⟩, α⟩, r⟩`. -/
def egEncRaw (z : List Bool) : List Bool :=
  egEncParts (NUPPT.inParam z).length (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z)) (NUPPT.inCoins z)

/-- The canonicalised message `egCanon p q m` of polynomial-time numbers is a polynomial-time
number (the test `m^q mod p = 1` through the safe modulus: it is only read when `m < p`). -/
private theorem dlc_numPoly_egCanon (H : ArithmeticFP) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) {P Q M : List Bool → ℕ} (hP : dlc_NumPoly P) (hQ : dlc_NumPoly Q)
    (hM : dlc_NumPoly M) : dlc_NumPoly fun z => egCanon (P z) (Q z) (M z) := by
  have hS := dlc_numPoly_safeMod H hu hP
  have t1 := dlc_poly_le H (dlc_numPoly_const 1) hM
  have t2 := dlc_poly_le H (dlc_numPoly_add H hM (dlc_numPoly_const 1)) hP
  have t3 := dlc_poly_eq H (dlc_numPoly_powMod H hM hQ hS fun z => dlc_safeMod_pos _ _)
    (dlc_numPoly_const 1)
  refine dlc_numPoly_congr (dlc_numPoly_ite (polyTimeComputable_and t1 (polyTimeComputable_and t2 t3))
    hM (dlc_numPoly_const 1)) fun z => ?_
  unfold egCanon
  by_cases h1 : 0 < M z
  · by_cases h2 : M z < P z
    · have hS' : dlc_safeMod (u z).length (P z) = P z := if_neg (by omega)
      by_cases h3 : M z ^ Q z % P z = 1
      · have e1 : decide (1 ≤ M z) = true := decide_eq_true (by omega)
        have e2 : decide (M z + 1 ≤ P z) = true := decide_eq_true (by omega)
        have e3 : decide (M z ^ Q z % dlc_safeMod (u z).length (P z) = 1) = true :=
          decide_eq_true (by rw [hS']; exact h3)
        simp [e1, e2, e3, h1, h2, h3]
      · have e3 : decide (M z ^ Q z % dlc_safeMod (u z).length (P z) = 1) = false :=
          decide_eq_false (by rw [hS']; exact h3)
        simp [e3, h3]
    · have e2 : decide (M z + 1 ≤ P z) = false := decide_eq_false (by omega)
      simp [e2, h2]
  · have e1 : decide (1 ≤ M z) = false := decide_eq_false (by omega)
    simp [e1, h1]

/-- The ciphertext `egEncParts` of polynomial-time data is polynomial-time (the index read
through `dlP_eq`, `dlM_eq`, `dlG_eq`). -/
private theorem dlc_poly_egEncParts (H : ArithmeticFP) {u pk m r : List Bool → List Bool}
    (hu : PolyTimeComputable u) (hpk : PolyTimeComputable pk) (hm : PolyTimeComputable m)
    (hr : PolyTimeComputable r) :
    PolyTimeComputable fun z => egEncParts (u z).length (pk z) (m z) (r z) := by
  have hi := polyTimeComputable_pairFstD.comp hpk
  have hP : dlc_NumPoly fun z => dlP (pairFstD (pk z)) :=
    dlc_numPoly_congr (dlc_numPoly_of_poly (polyTimeComputable_pairFstD.comp hi))
      fun z => (dlP_eq _).symm
  have hQ : dlc_NumPoly fun z => dlM (pairFstD (pk z)) :=
    dlc_numPoly_congr (dlc_numPoly_of_poly
      (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hi)))
      fun z => (dlM_eq _).symm
  have hG : dlc_NumPoly fun z => dlG (pairFstD (pk z)) :=
    dlc_numPoly_congr (dlc_numPoly_of_poly
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hi)))
      fun z => (dlG_eq _).symm
  have hb := dlc_numPoly_sample H hu hr hQ
  have hA := dlc_numPoly_of_poly (polyTimeComputable_pairSndD.comp hpk)
  have hC := dlc_numPoly_egCanon H hu hP hQ (dlc_numPoly_of_poly hm)
  exact (dlc_poly_natToList_powMod H hu hG hb hP).pairEncode
    (dlc_poly_natToList_powMulMod H hu hA hb hC hP)

/-- **El Gamal's `Enc` is polynomial-time** given the arithmetic bundle.

**Proof sketch.** The exponent `b` by the rejection loop (`polyTimeComputable_iterateFind`,
`H.le`); `h^b`, `A^b`, the membership test `m^q mod p = 1` (`H.modExp`, `polyTimeComputable_pairEq`,
`H.le` for `0 < m < p`, `polyTimeComputable_ite` for the canonicalisation); the product by
`H.mul` and the reduction modulo `p` by `H.divMod`; width-`n` padding by
`polyTimeComputable_unaryPoly`/`_blockMap`; pair. -/
theorem polyTimeComputable_egEncRaw (H : ArithmeticFP) : PolyTimeComputable egEncRaw :=
  dlc_poly_egEncParts H NUPPT.polyTimeComputable_inParam
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)
    (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg) NUPPT.polyTimeComputable_inCoins


/-- **El Gamal's encryptor** as a uniform `NUPPT` with `n · n` coins. -/
noncomputable def egEnc (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egEncRaw H) (.mul .var .var)

/-- The activation of `Enc` on `⟨pk, m⟩`. -/
theorem egEnc_runAt (H : ArithmeticFP) (n : ℕ) (pk m : List Bool) (r : (egEnc H).Coins n) :
    (egEnc H).runAt n (pairEncode pk m) r = egEncParts n pk m (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold egEnc
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [egEncRaw, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- **El Gamal's `Dec`** [PS10, Algorithm 106.2, `Dec_sk(c₁, c₂) = c₂ / c₁^a mod p`] as a
composition of the bundle's string functions on `⟨⟨⟨p, ⟨q, h⟩⟩, a⟩, ⟨c₁, c₂⟩⟩`:
`c₁^a mod p` (`modExpStr`), its inverse modulo `p` (`xgcdStr`, second component), the product
with `c₂` (`mulStr`) reduced modulo `p` (`divModStr`, second component). -/
def egDecStr (z : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode
    (mulStr (pairEncode (pairSndD (pairSndD z))
      (pairSndD (xgcdStr (pairEncode
        (modExpStr (pairEncode (pairFstD (pairSndD z))
          (pairEncode (pairSndD (pairFstD z)) (pairFstD (pairFstD (pairFstD z))))))
        (pairFstD (pairFstD (pairFstD z))))))))
    (pairFstD (pairFstD (pairFstD z)))))

/-- Transport of polynomial-time computability along a pointwise equation (used to avoid
the unifier unfolding the arithmetic string functions when matching a composition chain
against a definition; integration note, run 2). -/
private theorem polyTimeComputable_of_forall_eq {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (h : ∀ x, f x = g x) : PolyTimeComputable g :=
  (funext h : f = g) ▸ hf

/-- **`Dec` is polynomial-time** given the arithmetic bundle (a composition of its functions).

The chain is assembled in composition form and transported to `egDecStr` pointwise
(`polyTimeComputable_of_forall_eq` with `Function.comp_apply`): matching the composition
directly against the unfolded definition makes the unifier unfold `xgcdStr`/`modExpStr`
and does not terminate in practice. -/
theorem polyTimeComputable_egDecStr (H : ArithmeticFP) : PolyTimeComputable egDecStr := by
  have hp := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have ha := polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hc₁ := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hc₂ := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hexp := H.modExp.comp (hc₁.pairEncode (ha.pairEncode hp))
  have hinv := polyTimeComputable_pairSndD.comp (H.xgcd.comp (hexp.pairEncode hp))
  have hmul := H.mul.comp (hc₂.pairEncode hinv)
  refine polyTimeComputable_of_forall_eq
    (polyTimeComputable_pairSndD.comp (H.divMod.comp (hmul.pairEncode hp))) (fun z => ?_)
  simp only [Function.comp_apply, egDecStr]

/-- **Unfolding `Dec`**: on `⟨⟨⟨p, t⟩, a⟩, ⟨c₁, c₂⟩⟩` with `0 < p` it returns the numeral of
`c₂ · (c₁^a mod p)⁻¹ mod p` of the width of `p`'s numeral, the inverse being that of `Z_p`
(`ZMod.inv`).

**Proof sketch.** `modExpStr_pairEncode` gives the numeral `v` of `c₁^a mod p < p < 2^{|p|}`
(`listToNat_natToList`); `xgcdStr` returns the numeral of `(v : Z_p)⁻¹.val < p`; `mulStr_pairEncode`
gives the lossless product (`mul_lt_two_pow_add`); `divModStr`'s second component reduces it
modulo `p`. -/
theorem egDecStr_apply (pstr t a c₁ c₂ : List Bool) (hp : 0 < listToNat pstr) :
    egDecStr (pairEncode (pairEncode (pairEncode pstr t) a) (pairEncode c₁ c₂)) =
      natToList pstr.length (listToNat c₂ *
        (((listToNat c₁ ^ listToNat a % listToNat pstr : ℕ) : ZMod (listToNat pstr))⁻¹).val %
          listToNat pstr) := by
  sorry

/-- **El Gamal** [PS10, Algorithm 106.2] from a safe-prime instance generator `G` (used for
`(p, q)` only) and the arithmetic bundle: `Gen(1^n) = ⟨⟨⟨p, ⟨q, h⟩⟩, h^a⟩, ⟨⟨p, ⟨q, h⟩⟩, a⟩⟩` with
`h = g²` for `g ← Z_p^*` and `a ← Z_q`; `Enc_pk(m) = ⟨h^b, (h^a)^b · m⟩` for `b ← Z_q`;
`Dec_sk(c₁, c₂) = c₂ / c₁^a`.

**Deviation:** module docstring (rejection-sampled `g`, `a`, `b`; `q` in the keys;
canonicalised messages; the generator component of `G` is ignored). -/
noncomputable def elGamal (H : ArithmeticFP) (G : SafePrimeGen) : GroupPKScheme where
  gen := egGen H G
  enc := egEnc H
  dec := egDecStr
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := polyTimeComputable_egDecStr H

/-- **Correctness of El Gamal** [PS10, Algorithm 106.2, "`Dec_sk(c) = c₂ / c₁^a mod p`"]: for
`n ≥ n₀`, every key pair and every message `m` of the key's group `G_q` (`egCanon p q m = m`),
`Dec_sk(Enc_pk(m))` decodes to the `n`-bit numeral of `m`.

**Proof sketch.** By `egGen_runAt` (the first coin segment has length `coinLen n`, so it is
`List.ofFn r'` for a typed `r'` and `G.valid`/`G.wellFormed` apply: `p = 2q + 1` prime,
`n`-bit numerals) the keys are `pk = ⟨⟨p, ⟨q, h⟩⟩, h^a⟩`, `sk = ⟨⟨p, ⟨q, h⟩⟩, a⟩` with
`h = g² mod p`, `0 < h < p` (`egUnit_pos`, `egUnit_lt`, `Nat.Prime.dvd_of_dvd_pow`); by
`egEnc_runAt` the ciphertext is `⟨h^b mod p, (h^a mod p)^b · m mod p⟩` (`dlP`, `dlM`, `dlG`
read back by `listToNat_natToList`), and by `egDecStr_apply` the decryption is
`c₂ · ((h^b mod p)^a mod p)⁻¹ mod p`. In `Z_p` (units `h_u`, `m_u`):
`(h^a)^b · m · ((h^b)^a)⁻¹ = m` (`pow_mul`, `mul_comm`, `Units.mul_inv_cancel_right`,
`ZMod.natCast_mod`), so the result is the numeral of `m < p < 2^n` (`natToList n m`), decoded
by `decodeFin_ofFn`. -/
theorem elGamal_correct (H : ArithmeticFP) (G : SafePrimeGen) {n : ℕ} (hn : G.n₀ ≤ n)
    (rg : (egGen H G).Coins n) (re : (egEnc H).Coins n) (m : ℕ)
    (hm : egCanon (dlP (pairFstD (pairFstD ((egGen H G).runAt n [] rg))))
      (dlM (pairFstD (pairFstD ((egGen H G).runAt n [] rg)))) m = m) :
    decodeFin n (egDecStr (pairEncode (pairSndD ((egGen H G).runAt n [] rg))
      ((egEnc H).runAt n (pairEncode (pairFstD ((egGen H G).runAt n [] rg)) (natToList n m)) re))) =
      some (natToBits n m) := by
  sorry

/-! ## The derived instance generator and Theorem 107.3 -/

/-- The generator `h` of `G_q` derived from a unit `g`: `g² mod p`, replaced by `4 = 2²` when
`g² ≡ 1` (the text's `h = g²` with the degenerate case `h = 1` removed; Claim-107.a). -/
def egSquareGen (p g : ℕ) : ℕ := if g ^ 2 % p = 1 then 4 else g ^ 2 % p

/-- **The derived generator is a generator of `G_q`** (NT-105.a and Claim-107.a): for a safe
prime `p = 2q + 1` and `0 < g < p`, `h = egSquareGen p g` satisfies `0 < h < p` and
`orderOf (h : Z_p) = q`.

**Proof sketch.** Let `u` be the unit `g mod p`. If `g² mod p ≠ 1`, then `h = g² mod p` is the
value of `u² ∈ G_q` (`ZMod.natCast_mod`, `ZMod.coe_unitOfCoprime`), nonzero since `p ∤ g²`
(`Nat.Prime.dvd_of_dvd_pow`), different from `1` (`ZMod.val_natCast_of_lt`), of order `q`
(`orderOf_eq_of_mem_QR`, `sq_mem_QR`, `orderOf_units`). Otherwise `h = 4 = 2²` with `5 ≤ p`
(`five_le_safe`), the value of the square of the unit `2`, different from `1`, of order `q`
likewise. -/
theorem egSquareGen_valid {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p = 2 * q + 1)
    {g : ℕ} (hg0 : 0 < g) (hgp : g < p) :
    0 < egSquareGen p g ∧ egSquareGen p g < p ∧ orderOf ((egSquareGen p g : ℕ) : ZMod p) = q := by
  have h5 := five_le_safe hpq
  -- the order of the square of a unit `u` with `u² ≠ 1`
  have key : ∀ (u : (ZMod p)ˣ) (h : ℕ), ((h : ℕ) : ZMod p) = (u : ZMod p) ^ 2 → h < p → h ≠ 1 →
      orderOf ((h : ℕ) : ZMod p) = q := by
    intro u h hu hhp hh1
    have hne : u ^ 2 ≠ 1 := by
      intro h1
      apply hh1
      have h2 : ((h : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        rw [hu, ← Units.val_pow_eq_pow_val, h1, Units.val_one, Nat.cast_one]
      have h3 := congrArg ZMod.val h2
      rwa [ZMod.val_natCast_of_lt hhp, ZMod.val_natCast_of_lt (by omega)] at h3
    rw [hu, ← Units.val_pow_eq_pow_val, orderOf_units]
    exact orderOf_eq_of_mem_QR hpq (sq_mem_QR u) hne
  have hcop : Nat.Coprime g p :=
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt hg0 hgp)).symm
  by_cases h1 : g ^ 2 % p = 1
  · have hval : egSquareGen p g = 4 := if_pos h1
    refine ⟨by rw [hval]; norm_num, by rw [hval]; omega, ?_⟩
    have hcop2 : Nat.Coprime 2 p :=
      (Nat.coprime_primes Nat.prime_two hp.out).2 (by omega)
    rw [hval]
    refine key (ZMod.unitOfCoprime 2 hcop2) 4 ?_ (by omega) (by norm_num)
    rw [ZMod.coe_unitOfCoprime]
    norm_num
  · have hval : egSquareGen p g = g ^ 2 % p := if_neg h1
    have hlt : g ^ 2 % p < p := Nat.mod_lt _ hp.out.pos
    refine ⟨?_, by rw [hval]; exact hlt, ?_⟩
    · rw [hval]
      apply Nat.pos_of_ne_zero
      intro h0
      have hdvd : p ∣ g := hp.out.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0)
      exact absurd (Nat.le_of_dvd hg0 hdvd) (not_le.2 hgp)
    · rw [hval]
      refine key (ZMod.unitOfCoprime g hcop) (g ^ 2 % p) ?_ hlt h1
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_mod, Nat.cast_pow]

/-- The index `⟨p, ⟨q, h⟩⟩` of the derived generator from the numerals `a, b` of `p, q` and
the coin segment of `g`. -/
def egGroupParts (n : ℕ) (a b r₁ : List Bool) : List Bool :=
  pairEncode a (pairEncode b (natToList n (egSquareGen (listToNat a) (egUnit n (listToNat a) r₁))))

/-- The string function of the derived generator on `⟨⟨⟨1^n, []⟩, α⟩, r⟩`: the safe-prime
generator on the first coin segment, then `egGroupParts` on the next `n · n` coins. -/
def egGroupGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
  egGroupParts (NUPPT.inParam z).length
    (pairFstD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length)))))
    (pairFstD (pairSndD (G.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      ((NUPPT.inCoins z).take (G.gen.coins.eval (NUPPT.inParam z).length))))))
    (((NUPPT.inCoins z).drop (G.gen.coins.eval (NUPPT.inParam z).length)).take
      ((NUPPT.inParam z).length * (NUPPT.inParam z).length))

/-- `egGroupParts` of polynomial-time data is polynomial-time (the test `g² mod p = 1`, the
constant `4`). -/
private theorem dlc_poly_egGroupParts (H : ArithmeticFP) {u a b r₁ : List Bool → List Bool}
    (hu : PolyTimeComputable u) (ha : PolyTimeComputable a) (hb : PolyTimeComputable b)
    (hr₁ : PolyTimeComputable r₁) :
    PolyTimeComputable fun z => egGroupParts (u z).length (a z) (b z) (r₁ z) := by
  have hh := dlc_numPoly_egUnit_sq H hu ha hr₁
  have hs : dlc_NumPoly fun z =>
      egSquareGen (listToNat (a z)) (egUnit (u z).length (listToNat (a z)) (r₁ z)) :=
    dlc_numPoly_congr (dlc_numPoly_ite (dlc_poly_eq H hh (dlc_numPoly_const 1)) (dlc_numPoly_const 4) hh)
      fun z => by
        unfold egSquareGen
        by_cases h : egUnit (u z).length (listToNat (a z)) (r₁ z) ^ 2 % listToNat (a z) = 1 <;> simp [h]
  exact ha.pairEncode (hb.pairEncode (dlc_poly_natToList H hu hs))

/-- **The derived generator is polynomial-time** given the arithmetic bundle (the first two
steps of `polyTimeComputable_egGenRaw`, plus the test `g² mod p = 1` by `H.modExp` and
`polyTimeComputable_pairEq` with the constant numeral of `4` on `polyTimeComputable_ite`). -/
theorem polyTimeComputable_egGroupGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
    PolyTimeComputable (egGroupGenRaw G) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hc := NUPPT.polyTimeComputable_inCoins
  have hO := dlc_poly_genOut G
  have h := dlc_poly_egGroupParts H hu (polyTimeComputable_pairFstD.comp hO)
    (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hO))
    (dlc_poly_take (.mul .var .var) hu (dlc_poly_drop G.gen.coins hu hc))
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [Function.comp_apply, PolyExpr.eval_mul, PolyExpr.eval_var]
  rfl

/-- The machine of the derived generator: a uniform `NUPPT` with `G`'s coins plus `n · n`. -/
noncomputable def egGroupGenMachine (H : ArithmeticFP) (G : SafePrimeGen) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_egGroupGenRaw H G) (.add G.gen.coins (.mul .var .var))

/-- The activation of the derived generator's machine. -/
theorem egGroupGenMachine_runAt (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) :
    (egGroupGenMachine H G).runAt n [] r =
      egGroupParts n (pairFstD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n))))
        (pairFstD (pairSndD (G.gen.runAtL n [] ((List.ofFn r).take (G.gen.coinLen n)))))
        (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n)) := by
  rw [NUPPT.runAt_eq]
  unfold egGroupGenMachine
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [egGroupGenRaw, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, NUPPT.layout_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    NUPPT.Uniform.runAtL_eq G.gen_uniform, NUPPT.coinLen_eq]

/-- A string of the right length is the encoding of a typed coin string. -/
private theorem exists_ofFn_eq {ℓ : ℕ} (w : List Bool) (h : w.length = ℓ) :
    ∃ x : Fin ℓ → Bool, List.ofFn x = w := by
  subst h
  exact ⟨fun j => w.get j, List.ofFn_get w⟩

/-- The first coin segment of the derived generator is a coin string of `G.gen`. -/
private theorem exists_take_coins (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) :
    ∃ r' : G.gen.Coins n, List.ofFn r' = (List.ofFn r).take (G.gen.coinLen n) := by
  apply exists_ofFn_eq
  rw [List.length_take, List.length_ofFn]
  simp only [NUPPT.coinLen_eq, egGroupGenMachine, NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_add]
  omega

/-- **The derived generator outputs safe-prime instances** from `G.n₀` on: the index
`⟨p, ⟨q, egSquareGen p g⟩⟩` is valid.

**Proof sketch.** The first coin segment is a typed coin string of `G.gen` (`exists_take_coins`),
so `G.valid` and `G.wellFormed` give `⟨a, ⟨b, c⟩⟩` with `p = 2q + 1` prime; reading the output
back (`pairFstD_pairEncode`, `listToNat_natToList`) reduces the claim to `egSquareGen_valid`
with `0 < g < p` from `egUnit_pos`, `egUnit_lt`. -/
theorem egGroupGen_valid (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) (hn : G.n₀ ≤ n) :
    SafePrimeValid ((egGroupGenMachine H G).runAt n [] r) := by
  obtain ⟨r', hr'⟩ := exists_take_coins H G n r
  rw [egGroupGenMachine_runAt, ← hr', ← NUPPT.runAt_eq]
  have hv := G.valid n r' hn
  obtain ⟨a, b, c, ho, ha, hb, -⟩ := (wellFormedIndex_iff n _).1 (G.wellFormed n r' hn)
  rw [ho] at hv ⊢
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, egGroupParts]
  simp only [safePrimeValid_iff, expValid_iff, dlP_eq, dlM_eq, dlG_eq, pairFstD_pairEncode,
    pairSndD_pairEncode] at hv ⊢
  -- the occurrence of `p` inside the type `ZMod (dlP …)` is not reached by `simp`; `rw` abstracts it
  rw [pairFstD_pairEncode]
  haveI : Fact (listToNat a).Prime := ⟨hv.1.1⟩
  haveI : Fact (listToNat b).Prime := ⟨hv.2.1⟩
  have hpq := hv.2.2
  have hg0 := egUnit_pos n (listToNat a) (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
  have hgp := egUnit_lt hv.1.1.two_le n (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))
  obtain ⟨hh0, hhp, hord⟩ := egSquareGen_valid hpq hg0 hgp
  have hlt : egSquareGen (listToNat a) (egUnit n (listToNat a) (((List.ofFn r).drop (G.gen.coinLen n)).take (n * n))) <
      2 ^ n := by
    have h2 : listToNat a < 2 ^ n := by
      rw [← ha]
      exact listToNat_lt_two_pow a
    exact hhp.trans h2
  rw [listToNat_natToList hlt]
  exact ⟨⟨hv.1.1, hv.1.2.1, hv.1.2.2.1, hh0, hhp, hord⟩, hv.2.1, hpq⟩

/-- **The derived generator outputs well-formed indices** from `G.n₀` on. -/
theorem egGroupGen_wellFormed (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ)
    (r : (egGroupGenMachine H G).Coins n) (hn : G.n₀ ≤ n) :
    WellFormedIndex n ((egGroupGenMachine H G).runAt n [] r) := by
  obtain ⟨r', hr'⟩ := exists_take_coins H G n r
  rw [egGroupGenMachine_runAt, ← hr', ← NUPPT.runAt_eq]
  obtain ⟨a, b, c, ho, ha, hb, -⟩ := (wellFormedIndex_iff n _).1 (G.wellFormed n r' hn)
  rw [ho]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, egGroupParts]
  exact (wellFormedIndex_iff n _).2 ⟨a, b, _, rfl, ha, hb, length_natToList _ _⟩

/-- **The derived safe-prime instance generator** of El Gamal: the same `(p, q)` as `G`,
`h = g²` for `g ← Z_p^*` with the fallback `4` on `g² = 1`. The DDH assumption of
Theorem 107.3 is relative to this generator; its `h` is the text's "`y ← Gen_q`" up to the
`1/q` term of Claim-107.a. -/
noncomputable def egGroupGen (H : ArithmeticFP) (G : SafePrimeGen) : SafePrimeGen where
  gen := egGroupGenMachine H G
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  n₀ := G.n₀
  valid := egGroupGen_valid H G
  wellFormed := egGroupGen_wellFormed H G

/-- **Theorem 107.3** [PS10, Theorem 107.3]: if the DDH assumption holds (for the derived
generator) then El Gamal with message space `G_q` is secure, for safe primes of full length
except on a negligible set of the generator's coins (and under the arithmetic hypotheses).

**Deviation:** message space `G_q` and the chosen-message form of security (the text's
`m ∈ Z_p` is insecure, source error 28); the DDH assumption is relative to `egGroupGen H G`
and samples its exponents by rejection (`ddhExpo`, D10); `hbig` (`ExpGroupGen.FullLengthExcept`)
is used to make the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of
probability `δ n` (a convenience: if `E[1/q]` were not negligible, a DDH distinguisher finding
`a` by exhaustive search when `q ≤ 2n^c` would contradict the DDH assumption, so `hbig` could be
dropped; gate 03f1 review, M1; ruling R-03f1-1 (A) keeps it); the text leaves the proof as
an exercise and omits the generator-versus-square term.

Repair (run-3 audit P8-1, P8-2): the DDH ensembles' seeds became products (so hybrid 1 below
is exact up to the event `g² = 1`), and `hbig : G.FullLength` became
`∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.

**Proof sketch.** Fix `M, D`. For each bit `b` build the DDH distinguisher `D_b` (advice
`⟨M.advice n, ⟨D.advice n, [b]⟩⟩`, coins `M.coins + D.coins`): on a tuple `t`
(parsed by `pairFstD`/`pairSndD`, the last numeral cut to `n` bits by
`polyTimeComputable_pairTakePoly var`) with `t = ⟨i, ⟨A, ⟨B, Z⟩⟩⟩`, set `pk := ⟨i, A⟩`, run
`M(1^n, pk)` (`NUPPT.exists_seq`), take the `b`-th message, canonicalise it (`H.modExp`,
`H.le`, `polyTimeComputable_ite`), and output `D(1^n, ⟨pk, ⟨B, Z · m' mod p⟩⟩)` (`H.mul`,
`H.divMod`, `NUPPT.exists_comp`). *Hybrid 1* (the square-versus-generator event): the coins of
`challenge n M b` — `G`'s coins, the `n · n`-bit segments of `g` and `a` (`egGen_runAt`), `M`'s
coins and the `n · n` coins of `Enc` for `b'` (`egEnc_runAt`) — are in bijection with the seeds
`(r', (e₁, e₂))` of `ddhReal (egGroupGen H G)` together with `D_b`'s coins
(`acceptProb_comp_equiv`), `r'` being `G`'s coins followed by the segment of `g`
(`egGroupGenMachine_runAt`). Under this bijection the two experiments run `D` on the *same*
string unless `g² ≡ 1 (mod p)`: `ddhExpo` is the very sampler `sampleBelowL q (Nat.size q) n n`
of `egGenParts`/`egEncParts` (`expOrd_of_valid` at the valid index), `h^{(ab' mod q)} = h^{ab'}`
since `h` has order `q` (`egSquareGen_valid`), and `egSquareGen p g = g² mod p` unless
`g² ≡ 1`. Hence `|Pr[D(challenge b)] − Pr[D_b(ddhReal)]| ≤ Pr[g² ≡ 1]` (`uprob_mono`,
`statClose_of_uprob_ne`); `egUnit` is within `(1/2)^n` of the uniform unit
(`statClose_sampleBelowL` with `m = p − 1`, `StatClose.map`), so `Pr[g² ≡ 1] ≤ 1/q + (1/2)^n`
(`uprob_sq_eq_one`, `card_sqrt_safe`), and `hbig` gives, for `n ≥ n₀`, a set of `G`'s coins of
probability `≤ δ n` outside which `2^{n−1} ≤ p = 2q + 1` and `1/q ≤ 8 (1/2)^n`; altogether the
hybrid-1 gap is at most `9 (1/2)^n + δ n =: η n`. *Hybrid 2* (DDH): `hDDH D_b` through
`Ensemble.indist_iff_exists_negligible` gives `ε_b` with
`|Pr[D_b(ddhReal)] − Pr[D_b(ddhRandom)]| ≤ ε_b n`. *Hybrid 3* (the two random worlds coincide
up to the exponent sampler): in `ddhRandom`, `Z = h^z` with `z = ddhExpo n i e₃` independent
of the rest; replacing `z` by an ideal uniform `z ∈ Z_q` costs `(1/2)^n` (`ddhExpo_statClose`,
`StatClose.abs_uprob_sub_le_prod`) in each world, and for ideal `z` and a fixed rest,
`z ↦ h^z · m'_b` is a bijection of `G_q` for `m'_b ∈ G_q` (`expF_injective`, `card_QR_safe`,
`Equiv.mulRight`, or `HardcoreBit.pushesUniform_add_right` on the exponent `z + dlog m'_b`), so
`uprob_prod` and `uprob_comp_equiv` give `|Pr[D_0(ddhRandom)] − Pr[D_1(ddhRandom)]| ≤ 2 (1/2)^n`.
Hence the advantage is at most `2 η n + ε_0 n + ε_1 n + 2 (1/2)^n` for `n ≥ n₀` (and `≤ 1`
below), negligible by `negligible_two_pow_neg`, `Negligible.const_mul`, `Negligible.add`,
`Negligible.mono`. -/
theorem elGamal_secure (H : ArithmeticFP) (G : SafePrimeGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ)
    (hDDH : DDHAssumption (egGroupGen H G)) : (elGamal H G).Secure := by
  sorry

end TCSlib.Cryptography.Candidates
