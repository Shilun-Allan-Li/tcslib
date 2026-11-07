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
rejection sampler `sampleBelowL` (the block-rejection host `polyTimeComputable_rejectBlocksL`);
`dlc_poly_natToList` writes such a number as a numeral of a given width. -/

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
  rw [listToNat_mulStr, hfF, hgG]

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
  rw [divModStr_pairEncode, pairSndD_pairEncode, subStr_self, listToNat_natToList_zero_append,
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
  rw [subStr_self, listToNat_append, listToNat_singleton_true, length_natToList,
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
  rw [subStr_self, natToList_zero_append_drop, hbF]

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
  · rw [h, Nat.mod_zero, natToList_mod_two_pow]
  · rfl

/-- The safe modulus of a polynomial-time number at the width of `u`. -/
private theorem dlc_numPoly_safeMod (H : ArithmeticFP) {u : List Bool → List Bool}
    (hu : PolyTimeComputable u) {M : List Bool → ℕ} (hM : dlc_NumPoly M) :
    dlc_NumPoly fun z => dlc_safeMod (u z).length (M z) := by
  refine dlc_numPoly_congr (dlc_numPoly_ite (dlc_poly_eq H hM (dlc_numPoly_const 0))
    (dlc_numPoly_two_pow H hu) hM) fun z => ?_
  unfold dlc_safeMod
  by_cases h : M z = 0 <;> simp [h]

/-! #### The rejection sampler through the block-rejection host -/

/-- The comparison test on a pair `⟨w, b⟩`: not `⟦w⟧ ≤ ⟦b⟧`, i.e. the trial value is below `⟦w⟧`. -/
private def dlc_belowAcc (x : List Bool) : Bool :=
  !decide (listToNat (pairFstD x) ≤ listToNat (pairSndD x))

/-- The comparison test decides `⟦b⟧ < ⟦w⟧` on `⟨w, b⟩`. -/
private theorem dlc_belowAcc_spec (w b : List Bool) :
    dlc_belowAcc (pairEncode w b) = decide (listToNat b < listToNat w) := by
  rw [dlc_belowAcc, pairFstD_pairEncode, pairSndD_pairEncode, ← decide_not, decide_eq_decide,
    Nat.not_le]

/-- **The rejection sampler is a polynomial-time number**: `(sampleBelowL M (Nat.size M) |u| |u| c).getD 0`
for polynomial-time `u`, `c` and `M`.

**Proof sketch.** Host H15 (`polyTimeComputable_rejectBlocksL`) with the test `v < ⟦m⟧` (`H.le`,
negated), the parameter word `m` with `⟦m⟧ = M`, the width word `sizeStr m` (`H.size`), and `u`
for both the block length and the trial count (`sampleBelowL_eq_rejectBlocksL`); the number is
the payload's tail (`polyTimeComputable_tail`, `List.drop_one`), which reads `0` on failure. -/
private theorem dlc_numPoly_sample (H : ArithmeticFP) {u c : List Bool → List Bool}
    (hu : PolyTimeComputable u) (hc : PolyTimeComputable c) {M : List Bool → ℕ} (hM : dlc_NumPoly M) :
    dlc_NumPoly fun z => (sampleBelowL (M z) (Nat.size (M z)) (u z).length (u z).length (c z)).getD 0 := by
  obtain ⟨m, hm, hmM⟩ := hM
  obtain ⟨g, hg, hs⟩ := polyTimeComputable_rejectBlocksL (fun a v => v < a)
    (polyTimeComputable_not (H.le_poly polyTimeComputable_pairFstD polyTimeComputable_pairSndD))
    dlc_belowAcc_spec hm (H.size.comp hm) hu hu hc
  refine ⟨fun z => (g z).tail,
    (PolyTimeComputable.comp' polyTimeComputable_tail hg).congr fun z => List.drop_one, fun z => ?_⟩
  show listToNat (g z).tail =
    (sampleBelowL (M z) (Nat.size (M z)) (u z).length (u z).length (c z)).getD 0
  rw [← hmM, ← length_sizeStr, sampleBelowL_eq_rejectBlocksL,
    show rejectBlocksL (· < listToNat (m z)) (sizeStr (m z)).length (u z).length (u z).length
        (c z) = if g z = [] then none else some (listToNat (g z).tail) from (hs z).2]
  split_ifs with he
  · rw [he, List.tail_nil, listToNat_nil]
    rfl
  · rfl

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

/-! ### El Gamal's algorithms -/

/-- **El Gamal's `Gen` is polynomial-time** given the arithmetic bundle.

**Proof sketch.** Cut the coins at the lengths `coins(n)` and `n · n`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly` against `1^n`); run `G.gen.output` on the
layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`). The numbers are
read through a numeral calculus over the bundle (`H.add`, `H.sub`, `H.mul`, `H.divMod`,
`H.modExp`, `H.le`, `H.size`, `polyTimeComputable_ite`). The two rejection samplers are
instances of the block-rejection host H15 (`polyTimeComputable_rejectBlocksL`) over `n`-bit blocks
and `n` trials, read through `sampleBelowL_eq_rejectBlocksL`, with the test "`v` below the
parameter" by `H.le` (the parameter `p − 1` by `H.sub`, resp. `q`; the width word by `H.size`);
the sampled number is the tail of H15's output, which reads `0` when every trial is rejected.
`h = g² mod p` is `H.mul` then `H.divMod`, `h^x mod p` is `H.modExp`; every reduction uses the
modulus `2^n` where `p` reads as `0` (the `n`-bit numerals agree), so `H.modExp` stays
polynomial, and the remainder of `H.divMod` is taken against the modulus padded with leading
zeros, which keeps it lossless. Width-`n` numerals are the last `|b|` bits of `⟦0⟧_n ++ b`
(`⟦0⟧_n` by `H.sub`, `polyTimeComputable_pairDropPoly`); pair. -/
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
number (the test `m^q mod p = 1` through the safe modulus: it is only read when `m < p`).

**Proof sketch.** `egCanon` is an `if` on `0 < m ∧ m < p ∧ m^q mod p = 1`. The first two tests are
`H.le` comparisons (`dlc_poly_le`: `1 ≤ m`, `m + 1 ≤ p`), the third an equality test (`dlc_poly_eq`)
of `m^q mod p'` with `1` for the safe modulus `p'` (`dlc_numPoly_safeMod`, `dlc_numPoly_powMod`),
and the choice is `dlc_numPoly_ite`. The test with `p'` agrees with the test with `p` whenever it is
read: `m < p` forces `p ≠ 0`, so `p' = p`. -/
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
through `dlP_eq`, `dlM_eq`, `dlG_eq`).

**Proof sketch.** Read `p`, `q`, `h` from the index through `dlP_eq`, `dlM_eq`, `dlG_eq`
(`dlc_numPoly_of_poly` on the projections). The exponent is `dlc_numPoly_sample` and the canonical
message `dlc_numPoly_egCanon`; the two `n`-bit components are `dlc_poly_natToList_powMod` (`h^b mod
p`) and `dlc_poly_natToList_powMulMod` (`A^b · m' mod p`), paired. -/
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

**Proof sketch.** The calculus of `polyTimeComputable_egGenRaw`: `p`, `q`, `h` are read from the key
through `dlP_eq`, `dlM_eq`, `dlG_eq`; the exponent `b` by the block-rejection host H15
(`polyTimeComputable_rejectBlocksL` with the test `H.le`, the tail of its output); `h^b mod p` and
`A^b · m' mod p` by `H.modExp`, `H.mul` and `H.divMod`, with the modulus `2^n` where `p` reads as
`0`; the canonicalisation test `0 < m < p ∧ m^q mod p = 1` by `H.le` comparisons, the equality with
`1` as two comparisons rather than `polyTimeComputable_pairEq` (numerals of different widths can
read as the same number), and the choice by `polyTimeComputable_ite`; width-`n` numerals as the last
bits of `⟦0⟧_n ++ b`; pair. -/
theorem polyTimeComputable_egEncRaw (H : ArithmeticFP) : PolyTimeComputable egEncRaw := by
  exact dlc_poly_egEncParts H NUPPT.polyTimeComputable_inParam
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

/-- **`Dec` is polynomial-time** given the arithmetic bundle (a composition of its functions).

The chain is assembled in composition form and transported to `egDecStr` pointwise
(`PolyTimeComputable.congr` with `Function.comp_apply`): matching the composition
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
  refine PolyTimeComputable.congr
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
  have hp2 : listToNat pstr < 2 ^ pstr.length := listToNat_lt_two_pow pstr
  haveI : NeZero (listToNat pstr) := ⟨hp.ne'⟩
  have he : listToNat (natToList pstr.length (listToNat c₁ ^ listToNat a % listToNat pstr)) =
      listToNat c₁ ^ listToNat a % listToNat pstr :=
    listToNat_natToList ((Nat.mod_lt _ hp).trans hp2)
  have hi : listToNat (natToList pstr.length
      ((((listToNat c₁ ^ listToNat a % listToNat pstr : ℕ) : ZMod (listToNat pstr))⁻¹).val)) =
      (((listToNat c₁ ^ listToNat a % listToNat pstr : ℕ) : ZMod (listToNat pstr))⁻¹).val :=
    listToNat_natToList ((ZMod.val_lt _).trans hp2)
  unfold egDecStr
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [modExpStr_pairEncode, xgcdStr_pairEncode, pairSndD_pairEncode, he, mulStr_pairEncode, hi,
    divModStr_pairEncode, pairSndD_pairEncode, length_natToList]
  rw [listToNat_natToList]
  rw [pow_add]
  exact Nat.mul_lt_mul'' (listToNat_lt_two_pow c₂) ((ZMod.val_lt _).trans hp2)

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
  -- the first coin segment is a coin string of the safe-prime generator
  have hlen : ((List.ofFn rg).take (G.gen.coinLen n)).length = G.gen.coinLen n := by
    rw [List.length_take, List.length_ofFn]
    simp only [NUPPT.coinLen_eq, egGen, NUPPT.coins_ofPolyTimeUniform, egGenCoins, PolyExpr.eval_add]
    omega
  obtain ⟨r', hr'⟩ : ∃ r' : G.gen.Coins n, List.ofFn r' = (List.ofFn rg).take (G.gen.coinLen n) :=
    ⟨fun j => ((List.ofFn rg).take (G.gen.coinLen n)).get (Fin.cast hlen.symm j),
      List.ext_get (by rw [List.length_ofFn, hlen]) (fun k h1 h2 => by simp)⟩
  have hv := G.valid n r' hn
  obtain ⟨a, b, c, ho, ha, hb, -⟩ := (wellFormedIndex_iff n _).1 (G.wellFormed n r' hn)
  rw [ho] at hv
  simp only [safePrimeValid_iff, expValid_iff, dlP_eq, dlM_eq, pairFstD_pairEncode,
    pairSndD_pairEncode] at hv
  have hpp : (listToNat a).Prime := hv.1.1
  have hqp : (listToNat b).Prime := hv.2.1
  have hpq : listToNat a = 2 * listToNat b + 1 := hv.2.2
  haveI : Fact (listToNat a).Prime := ⟨hpp⟩
  have hp2n : listToNat a < 2 ^ n := ha ▸ listToNat_lt_two_pow a
  have hp0 : 0 < listToNat a := hpp.pos
  -- the keys
  rw [egGen_runAt, ← hr', ← NUPPT.runAt_eq, ho] at hm ⊢
  simp only [egGenParts, pairFstD_pairEncode, pairSndD_pairEncode, dlP_eq, dlM_eq] at hm ⊢
  generalize hr₁ : ((List.ofFn rg).drop (G.gen.coinLen n)).take (n * n) = r₁ at hm ⊢
  generalize hr₂ : (List.ofFn rg).drop (G.gen.coinLen n + n * n) = r₂ at hm ⊢
  have hg0 := egUnit_pos n (listToNat a) r₁
  have hgp := egUnit_lt hpp.two_le n r₁
  generalize hg : egUnit n (listToNat a) r₁ = g at hm ⊢ hg0 hgp
  have hx : (sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂).getD 0 < listToNat a := by
    rcases hs : sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂ with _ | v
    · exact hp0
    · have := sampleBelowL_lt hs
      rw [Option.getD_some]
      omega
  generalize (sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n r₂).getD 0 = x at hm ⊢ hx
  -- the message lies below `p`
  have hmp : m < listToNat a := by
    unfold egCanon at hm
    split_ifs at hm with hc
    · exact hc.2.1
    · rw [← hm]
      exact hpp.one_lt
  -- the ciphertext
  rw [egEnc_runAt]
  unfold egEncParts
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, dlP_eq, dlM_eq, dlG_eq]
  have hh : g ^ 2 % listToNat a < listToNat a := Nat.mod_lt _ hp0
  rw [listToNat_natToList (hh.trans hp2n), listToNat_natToList ((Nat.mod_lt _ hp0).trans hp2n),
    listToNat_natToList (hmp.trans hp2n), hm]
  generalize ((sampleBelowL (listToNat b) (Nat.size (listToNat b)) n n (List.ofFn re)).getD 0) = y
  -- the decryption
  rw [egDecStr_apply _ _ _ _ _ hp0, listToNat_natToList ((Nat.mod_lt _ hp0).trans hp2n),
    listToNat_natToList ((Nat.mod_lt _ hp0).trans hp2n), listToNat_natToList (hx.trans hp2n), ha]
  -- in `Z_p`: `(h^x)^y · m · ((h^y)^x)⁻¹ = m`
  have hgz : ((g : ℕ) : ZMod (listToNat a)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hg0 hgp
  have key : (((g ^ 2 % listToNat a) ^ x % listToNat a) ^ y * m % listToNat a *
      ((((g ^ 2 % listToNat a) ^ y % listToNat a) ^ x % listToNat a : ℕ) :
        ZMod (listToNat a))⁻¹.val % listToNat a : ℕ) = ((m : ℕ) : ZMod (listToNat a)) := by
    push_cast [ZMod.natCast_mod, ZMod.natCast_zmod_val]
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm x y, mul_comm _ (m : ZMod (listToNat a)),
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hgz), mul_one]
  have hval := congrArg ZMod.val key
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ hp0),
    Nat.mod_eq_of_lt hmp] at hval
  rw [hval, natToList_eq, decodeFin_ofFn]

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
steps of `polyTimeComputable_egGenRaw`, plus the test `g² mod p = 1`, with `g · g` by `H.mul`,
the remainder by `H.divMod` and the equality with `1` as two `H.le` comparisons, choosing the
constant numeral of `4` on `polyTimeComputable_ite`). -/
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

/-! ### Helpers of `elGamal_secure` (unit dl-c) -/

/-- Splitting a coin string `Fin L → Bool` with `L = a + b` into its two segments: the length
cast, then `TCSlib.Cryptography.splitCoins`. -/
private def dlc_splitEquiv {L a b : ℕ} (h : L = a + b) :
    (Fin L → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans (splitCoins a b)

/-- The coin string of two joined segments is the concatenation of their coin strings
(`ofFn_splitCoins_symm`). -/
private theorem dlc_splitEquiv_symm_ofFn {L a b : ℕ} (h : L = a + b) (u : Fin a → Bool)
    (v : Fin b → Bool) : List.ofFn ((dlc_splitEquiv h).symm (u, v)) = List.ofFn u ++ List.ofFn v := by
  subst h
  exact ofFn_splitCoins_symm a b u v

/-- Padding a string of the right length is lossless: `List.ofFn (padFin ℓ w) = w` for `|w| = ℓ`
(`Collection.ofFn_padFin_of_le`). -/
private theorem dlc_ofFn_padFin {ℓ : ℕ} {w : List Bool} (h : w.length = ℓ) :
    List.ofFn (padFin ℓ w) = w := by
  rw [Collection.ofFn_padFin_of_le h.le, h, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- The public key `⟨i, X⟩` read from a DDH tuple `⟨i, ⟨X, ⟨Y, Z⟩⟩⟩`. -/
private def dlc_tuplePk (t : List Bool) : List Bool := pairEncode (pairFstD t) (pairFstD (pairSndD t))

/-- The input of `D` built by the DDH distinguisher `D_b` from the tuple `t = ⟨i, ⟨X, ⟨Y, Z⟩⟩⟩`
and the selector's output `mm = ⟨m₀, m₁⟩`: `⟨⟨i, X⟩, ⟨Y, ⟦Z · m'_b mod p⟧_n⟩⟩` with
`m'_b = egCanon p q m_b`. -/
private def dlc_ddhInput (n : ℕ) (b : Bool) (t mm : List Bool) : List Bool :=
  pairEncode (dlc_tuplePk t) (pairEncode (pairFstD (pairSndD (pairSndD t)))
    (natToList n (listToNat (pairSndD (pairSndD (pairSndD t))) *
      egCanon (dlP (pairFstD t)) (dlM (pairFstD t)) (listToNat (if b then pairSndD mm else pairFstD mm)) %
        dlP (pairFstD t))))

/-- The pre-processing of `D_b` is polynomial-time on `⟨1^n, ⟨t, mm⟩⟩`.

**Proof sketch.** The projections of `⟨1^n, ⟨t, mm⟩⟩` give `⟨i, X⟩` and `Y`; `p` and `q` are read
from `i` (`dlP_eq`, `dlM_eq`), `m_b` is a fixed projection of `mm` (case on `b`), `m'_b` is
`dlc_numPoly_egCanon`, and `⟦Z · m'_b mod p⟧_n` is `dlc_poly_natToList_powMulMod` with the exponent
`1` (`pow_one`); pair, and match the definition pointwise. -/
private theorem dlc_poly_ddhInput (H : ArithmeticFP) (b : Bool) :
    PolyTimeComputable fun z =>
      dlc_ddhInput (pairFstD z).length b (pairFstD (pairSndD z)) (pairSndD (pairSndD z)) := by
  have ht := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hmm := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hi := polyTimeComputable_pairFstD.comp ht
  have hpk := hi.pairEncode (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp ht))
  have hY := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp ht))
  have hZ := dlc_numPoly_of_poly (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp ht)))
  have hP : dlc_NumPoly fun z => dlP (pairFstD (pairFstD (pairSndD z))) :=
    dlc_numPoly_congr (dlc_numPoly_of_poly (polyTimeComputable_pairFstD.comp hi))
      fun z => (dlP_eq _).symm
  have hQ : dlc_NumPoly fun z => dlM (pairFstD (pairFstD (pairSndD z))) :=
    dlc_numPoly_congr (dlc_numPoly_of_poly
      (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hi)))
      fun z => (dlM_eq _).symm
  have hm : PolyTimeComputable fun z =>
      if b then pairSndD (pairSndD (pairSndD z)) else pairFstD (pairSndD (pairSndD z)) := by
    cases b
    · exact polyTimeComputable_pairFstD.comp hmm
    · exact polyTimeComputable_pairSndD.comp hmm
  have hC := dlc_numPoly_egCanon H polyTimeComputable_pairFstD hP hQ (dlc_numPoly_of_poly hm)
  have hW := dlc_poly_natToList_powMulMod H polyTimeComputable_pairFstD hZ (dlc_numPoly_const 1) hC hP
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp (hpk.pairEncode (hY.pairEncode hW))
  simp only [Function.comp_apply, pow_one]
  rfl

/-- **The DDH distinguisher `D_b`** of Theorem 107.3: on a tuple `t`, run the selector `M` on
`pk = ⟨i, X⟩` and then `D` on `dlc_ddhInput n b t ⟨m₀, m₁⟩`; its coins are `M`'s followed by
`D`'s (`NUPPT.exists_comp`, `exists_compParam`, `exists_seq`). -/
private theorem dlc_exists_ddhDist (H : ArithmeticFP) (M D : NUPPT) (b : Bool) :
    ∃ Db : NUPPT, ∀ n, ∃ e : M.Coins n × D.Coins n ≃ Db.Coins n,
      ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
        Db.runAt n w (e (rM, rD)) = D.runAt n (dlc_ddhInput n b w (M.runAt n (dlc_tuplePk w) rM)) rD := by
  have hpk : PolyTimeComputable dlc_tuplePk :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  obtain ⟨M', hM'c, -, -, hM'⟩ := NUPPT.exists_comp M hpk polyTimeComputable_id
  obtain ⟨D', hD'c, -, -, hD'⟩ := NUPPT.exists_compParam D (dlc_poly_ddhInput H b)
    polyTimeComputable_pairSndD
  obtain ⟨C, hCc, -, hC⟩ := NUPPT.exists_seq M' D'
  refine ⟨C, fun n => ?_⟩
  have hlen : C.coinLen n = M.coinLen n + D.coinLen n := by
    rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, NUPPT.coinLen_eq, hCc, hM'c, hD'c, PolyExpr.eval_add]
  have hM'len : M'.coinLen n = M.coinLen n := by rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, hM'c]
  refine ⟨(dlc_splitEquiv hlen).symm, fun w rM rD => ?_⟩
  rw [NUPPT.runAt_eq, dlc_splitEquiv_symm_ofFn, hC, hM'len, List.take_left' (List.length_ofFn),
    List.drop_left' (List.length_ofFn), hM', hD', NUPPT.runAt_eq, NUPPT.runAt_eq]
  simp only [id, pairSndD_pairEncode, NUPPT.advInput_eq, pairFstD_pairEncode, List.length_replicate]

/-- Two events that agree outside `C` have probabilities within `Pr[C]` (`statClose_of_uprob_ne`
on the indicators). -/
private theorem dlc_abs_uprob_sub_le_of_iff {Ω : Type*} [Fintype Ω] {A B C : Ω → Prop}
    (h : ∀ ω, ¬ C ω → (A ω ↔ B ω)) : |uprob A - uprob B| ≤ uprob C := by
  classical
  have hs := (statClose_of_uprob_ne (fun ω => decide (A ω)) (fun ω => decide (B ω))).abs_uprob_sub_le
    (fun v => v = true)
  simp only [decide_eq_true_eq] at hs
  refine hs.trans (uprob_mono fun ω hne => ?_)
  by_contra hc
  exact hne (decide_eq_decide.2 (h ω hc))

/-- **At most two square roots of `1` among `1, …, p − 1`**: `(x + 1)² ≡ 1 (mod p)` forces
`x = 0` or `x = p − 2` (`p ∣ x (x + 2)`, `Nat.Prime.dvd_mul`).

**Proof sketch.** Map the filter into `ℕ` by `Fin.valEmbedding`. From `(x + 1)² mod p = 1`, `p ∣ (x
+ 1)² − 1 = x (x + 2)` (`Nat.modEq_iff_dvd'`), so `p ∣ x`, hence `x = 0` since `x < p − 1`, or `p ∣
x + 2`, hence `x = p − 2`. The image lies in `{0, p − 2}` (`card_le_card`, `card_insert_le`). -/
private theorem dlc_card_sq_eq_one_le {p : ℕ} (hp : p.Prime) :
    (univ.filter fun x : Fin (p - 1) => ((x : ℕ) + 1) ^ 2 % p = 1).card ≤ 2 := by
  have h2 := hp.two_le
  have hsub : (univ.filter fun x : Fin (p - 1) => ((x : ℕ) + 1) ^ 2 % p = 1).map Fin.valEmbedding ⊆
      ({0, p - 2} : Finset ℕ) := by
    intro v hv
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hxp : (x : ℕ) < p - 1 := x.2
    have hdvd : p ∣ (x : ℕ) * ((x : ℕ) + 2) := by
      have hmod : ((x : ℕ) + 1) ^ 2 % p = 1 % p := by rw [hx, Nat.mod_eq_of_lt hp.one_lt]
      have h := (Nat.modEq_iff_dvd' (by nlinarith)).1 hmod.symm
      have he : ((x : ℕ) + 1) ^ 2 - 1 = (x : ℕ) * ((x : ℕ) + 2) := by
        rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
        ring
      rwa [he] at h
    simp only [mem_insert, mem_singleton]
    rcases hp.dvd_mul.1 hdvd with h | h
    · left
      exact Nat.eq_zero_of_dvd_of_lt h (by omega)
    · right
      have hle := Nat.le_of_dvd (by omega) h
      omega
  have hc := card_le_card hsub
  rw [card_map] at hc
  exact hc.trans (card_insert_le _ _)

/-- **The event `g² ≡ 1 (mod p)` for the sampled unit**: for a prime `p < 2^n`, over uniform
coins, `Pr[egUnit² ≡ 1] ≤ 2/(p − 1) + (1/2)^n` (`statClose_sampleBelowL` with `m = p − 1`, then
`dlc_card_sq_eq_one_le`). -/
private theorem dlc_uprob_egUnit_sq_le {p n : ℕ} (hp : p.Prime) (hpn : p < 2 ^ n) :
    uprob (fun u : Fin (n * n) → Bool => egUnit n p (List.ofFn u) ^ 2 % p = 1) ≤
      2 / ((p - 1 : ℕ) : ℝ) + (1 / 2) ^ n := by
  classical
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have h := (statClose_sampleBelowL hp1 (by omega : p - 1 < 2 ^ n)).uprob_le_add
    (fun v => (v + 1) ^ 2 % p = 1)
  unfold egUnit
  refine h.trans (add_le_add_right ?_ _)
  rw [uprob_eq_card_filter, Fintype.card_fin]
  exact div_le_div_of_nonneg_right (by exact_mod_cast dlc_card_sq_eq_one_le hp) (Nat.cast_nonneg _)

/-- `2/(p − 1) ≤ 8 · (1/2)^n` for a full-length `p` (`2^{n−1} ≤ p`, `2 ≤ p`). -/
private theorem dlc_two_div_le {p n : ℕ} (hp2 : 2 ≤ p) (hpn : p < 2 ^ n) (hfull : 2 ^ (n - 1) ≤ p) :
    2 / ((p - 1 : ℕ) : ℝ) ≤ 8 * (1 / 2) ^ n := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hpn; simp at hpn; omega
    · exact h
  have h2n : 2 ^ n ≤ 4 * (p - 1) := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
    omega
  have hp1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have h2n' : (2 : ℝ) ^ n ≤ 4 * ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h2n
  rw [div_le_iff₀ hp1, one_div_pow]
  have h2pos : (0 : ℝ) < 2 ^ n := by positivity
  rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ h2pos]
  linarith

/-- **The bad event of hybrid 1 is negligible**: for `n ≥ n₀`, over the generator's coins and the
coins of `g`, `Pr[g² ≡ 1 (mod p)] ≤ δ n + 9 · (1/2)^n` (the short-prime coins cost `δ n` by `hbig`;
on the others `2/(p − 1) ≤ 8 · (1/2)^n`).

**Proof sketch.** Average over `G`'s coins (`uprob_prod`). For each coin string `r` (valid and well
formed from `n₀` on: `wellFormedIndex_iff`, `safePrimeValid_iff`) the inner probability is at most
`[p < 2^{n−1}] + 9 · (1/2)^n`: at most `1` for a short prime, and otherwise `2/(p − 1) + (1/2)^n ≤ 9
· (1/2)^n` (`dlc_uprob_egUnit_sq_le`, `dlc_two_div_le`). The average of the indicator is at most `δ
n` (`fullLengthExcept_iff`, `uprob_eq_uexp`, `HardcoreBit.uexp_mono`, `HardcoreBit.uexp_add`,
`HardcoreBit.uexp_const`). -/
private theorem dlc_uprob_bad_le (G : SafePrimeGen) {δ : ℕ → ℝ} (hδ : G.FullLengthExcept δ) {n : ℕ}
    (hn : G.n₀ ≤ n) :
    uprob (fun z : G.gen.Coins n × (Fin (n * n) → Bool) =>
      egUnit n (dlP (G.gen.runAt n [] z.1)) (List.ofFn z.2) ^ 2 % dlP (G.gen.runAt n [] z.1) = 1) ≤
      δ n + 9 * (1 / 2) ^ n := by
  classical
  rw [uprob_prod]
  have hδn := (G.fullLengthExcept_iff δ).1 hδ n hn
  have hpt : ∀ r : G.gen.Coins n,
      uprob (fun u : Fin (n * n) → Bool =>
        egUnit n (dlP (G.gen.runAt n [] r)) (List.ofFn u) ^ 2 % dlP (G.gen.runAt n [] r) = 1) ≤
      (if dlP (G.gen.runAt n [] r) < 2 ^ (n - 1) then (1 : ℝ) else 0) + 9 * (1 / 2) ^ n := by
    intro r
    have hv := G.valid n r hn
    obtain ⟨a, b, c, ho, ha, -, -⟩ := (wellFormedIndex_iff n _).1 (G.wellFormed n r hn)
    rw [ho] at hv ⊢
    simp only [safePrimeValid_iff, expValid_iff, dlP_eq, dlM_eq, pairFstD_pairEncode,
      pairSndD_pairEncode] at hv ⊢
    have hpp : (listToNat a).Prime := hv.1.1
    have hpn : listToNat a < 2 ^ n := ha ▸ listToNat_lt_two_pow a
    have hpos : (0 : ℝ) ≤ 9 * (1 / 2) ^ n := by positivity
    split_ifs with hsmall
    · linarith [uprob_le_one (fun u : Fin (n * n) → Bool =>
        egUnit n (listToNat a) (List.ofFn u) ^ 2 % listToNat a = 1)]
    · push_neg at hsmall
      have h8 := dlc_two_div_le hpp.two_le hpn hsmall
      linarith [dlc_uprob_egUnit_sq_le hpp hpn]
  refine (HardcoreBit.uexp_mono hpt).trans ?_
  rw [HardcoreBit.uexp_add, HardcoreBit.uexp_const, ← uprob_eq_uexp]
  linarith

/-- **Every element of `G_q` is a power of a generator** (NT-105.a; `zpowers_eq_QR`,
`mem_powers_iff_mem_zpowers`): if `h` has order `q` in `Z_p` for a safe prime `p = 2q + 1`, then
every `0 < c < p` with `c^q ≡ 1 (mod p)` is `h^k` for some `k`.

**Proof sketch.** `h` and `c` are nonzero in `Z_p`, hence units `h_u`, `c_u`. `h_u` has order `q`,
so it lies in `G_q` (`mem_QR_iff_pow_eq_one`) and is not `1`; `c_u^q = 1`, so `c_u ∈ G_q`. Since
`G_q` is generated by `h_u` (`zpowers_eq_QR`) and is finite, `c_u = h_u^k` for some `k : ℕ`
(`mem_powers_iff_mem_zpowers`); take values. -/
private theorem dlc_exists_pow_eq {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime] (hpq : p = 2 * q + 1)
    {h c : ℕ} (hord : orderOf ((h : ℕ) : ZMod p) = q) (hc0 : 0 < c) (hcp : c < p)
    (hcq : c ^ q % p = 1) : ∃ k : ℕ, ((h : ℕ) : ZMod p) ^ k = ((c : ℕ) : ZMod p) := by
  have hh0 : ((h : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, orderOf_eq_zero_iff'.2 fun k hk => by rw [zero_pow hk.ne']; exact zero_ne_one] at hord
    exact hq.out.ne_zero hord.symm
  have hc0' : ((c : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hc0 hcp
  set hu := Units.mk0 ((h : ℕ) : ZMod p) hh0
  set cu := Units.mk0 ((c : ℕ) : ZMod p) hc0'
  have hord' : orderOf hu = q := by rw [← orderOf_units, Units.val_mk0, hord]
  have hmem : hu ∈ QR p := (mem_QR_iff_pow_eq_one hpq hu).2 (by rw [← hord']; exact pow_orderOf_eq_one hu)
  have hne : hu ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord'
    exact hq.out.one_lt.ne hord'
  have hcmem : cu ∈ QR p := by
    rw [mem_QR_iff_pow_eq_one hpq]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, ← Nat.cast_pow, ← ZMod.natCast_mod, hcq,
      Nat.cast_one]
  rw [← zpowers_eq_QR hpq hmem hne, ← mem_powers_iff_mem_zpowers] at hcmem
  obtain ⟨k, hk⟩ := hcmem
  refine ⟨k, ?_⟩
  have := congrArg Units.val hk
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0] at this

/-- **The random world forgets the message** (hybrid 3): for `h` of order `q` in `Z_p` and
`c ≡ h^k (mod p)`, the numeral of `h^z · c mod p` for uniform `z ∈ Z_q` has the law of the numeral
of `h^z mod p` (the shift `z ↦ z + k`, `Equiv.addRight`). -/
private theorem dlc_uprob_shift {p q : ℕ} [NeZero q] {h c k : ℕ}
    (hord : orderOf ((h : ℕ) : ZMod p) = q) (hk : ((h : ℕ) : ZMod p) ^ k = ((c : ℕ) : ZMod p)) (n : ℕ)
    (Ψ : List Bool → Prop) :
    uprob (fun z : ZMod q => Ψ (natToList n (h ^ z.val % p * c % p))) =
      uprob (fun z : ZMod q => Ψ (natToList n (h ^ z.val % p))) := by
  rw [← uprob_comp_equiv (Equiv.addRight ((k : ℕ) : ZMod q))
    (fun z : ZMod q => Ψ (natToList n (h ^ z.val % p)))]
  congr 1
  funext z
  have hval : h ^ z.val % p * c % p = h ^ (Equiv.addRight ((k : ℕ) : ZMod q) z).val % p := by
    have hcast : ((h ^ z.val % p * c % p : ℕ) : ZMod p) =
        ((h ^ (Equiv.addRight ((k : ℕ) : ZMod q) z).val % p : ℕ) : ZMod p) := by
      rw [Equiv.coe_addRight, ZMod.val_add, ZMod.val_natCast]
      push_cast [ZMod.natCast_mod]
      generalize z.val = v
      rw [← hk, ← pow_add, ← hord, pow_mod_orderOf, pow_add, pow_add, pow_mod_orderOf]
    have := (ZMod.natCast_eq_natCast_iff' _ _ p).1 hcast
    rwa [Nat.mod_mod, Nat.mod_mod] at this
  rw [hval]

/-- The coin count of El Gamal's `Gen`: `G`'s coins, then `n · n` for `g` and `n · n` for `a`. -/
private theorem dlc_egGen_coinLen (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) :
    (egGen H G).coinLen n = G.gen.coinLen n + (n * n + n * n) := by
  rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq]
  simp only [egGen, NUPPT.coins_ofPolyTimeUniform, egGenCoins, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_var]

/-- The coin count of El Gamal's `Enc`: `n · n`. -/
private theorem dlc_egEnc_coinLen (H : ArithmeticFP) (n : ℕ) : (egEnc H).coinLen n = n * n := by
  rw [NUPPT.coinLen_eq]
  simp only [egEnc, NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_mul, PolyExpr.eval_var]

/-- The coin count of the derived generator: `G`'s coins, then `n · n` for `g`. -/
private theorem dlc_egGroupGen_coinLen (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) :
    (egGroupGenMachine H G).coinLen n = G.gen.coinLen n + n * n := by
  rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq]
  simp only [egGroupGenMachine, NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_var]

/-- The coins of `Gen` from `G`'s coins and the segments of `g` and `a`. -/
private noncomputable def dlc_genEquiv (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) :
    (G.gen.Coins n × (Fin (n * n) → Bool)) × (Fin (n * n) → Bool) ≃ (egGen H G).Coins n :=
  ((dlc_splitEquiv (dlc_egGen_coinLen H G n)).trans
    ((Equiv.prodCongr (Equiv.refl _) (dlc_splitEquiv rfl)).trans (Equiv.prodAssoc _ _ _).symm)).symm

private theorem dlc_genEquiv_ofFn (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : G.gen.Coins n)
    (u₁ u₂ : Fin (n * n) → Bool) :
    List.ofFn (dlc_genEquiv H G n ((r, u₁), u₂)) = List.ofFn r ++ (List.ofFn u₁ ++ List.ofFn u₂) := by
  unfold dlc_genEquiv
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodAssoc_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm, Equiv.refl_apply,
    dlc_splitEquiv_symm_ofFn, dlc_splitEquiv_symm_ofFn]

/-- The coins of `Enc` from one segment of `n · n` coins. -/
private noncomputable def dlc_encEquiv (H : ArithmeticFP) (n : ℕ) : (Fin (n * n) → Bool) ≃ (egEnc H).Coins n :=
  Equiv.arrowCongr (finCongr (dlc_egEnc_coinLen H n).symm) (Equiv.refl Bool)

/-- The coins of the derived generator from `G`'s coins and the segment of `g`. -/
private noncomputable def dlc_grpEquiv (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) :
    G.gen.Coins n × (Fin (n * n) → Bool) ≃ (egGroupGenMachine H G).Coins n :=
  (dlc_splitEquiv (dlc_egGroupGen_coinLen H G n)).symm

/-- The coin string of `Enc` read from its segment. -/
private theorem dlc_encEquiv_ofFn (H : ArithmeticFP) (n : ℕ) (u : Fin (n * n) → Bool) :
    List.ofFn (dlc_encEquiv H n u) = List.ofFn u :=
  (List.ofFn_congr (dlc_egEnc_coinLen H n).symm u).symm

/-- **The challenge on split coins**: the keys are `egGenParts` on `G`'s output and the segments of
`g` and `a`, the ciphertext is `egEncParts` on the segment of `b` (`egGen_runAt`, `egEnc_runAt`).

**Proof sketch.** `dlc_genEquiv_ofFn` writes the coins of `Gen` as `r ++ (u₁ ++ u₂)`, so the cuts of
`egGen_runAt` at `coinLen n` and `n · n` recover `r`, `u₁` and `u₂` (`List.take_left'`,
`List.drop_left'`, `List.drop_drop`), and `NUPPT.runAt_eq` reads `G.gen.runAtL` back as
`G.gen.runAt`. Unfold `challenge`, read the fields of `elGamal`, and rewrite the ciphertext by
`egEnc_runAt` with `dlc_encEquiv_ofFn`. -/
private theorem dlc_challenge_eq (H : ArithmeticFP) (G : SafePrimeGen) (M : NUPPT) (b : Bool) (n : ℕ)
    (r : G.gen.Coins n) (u₁ u₂ u₃ : Fin (n * n) → Bool) (rM : M.Coins n) :
    (elGamal H G).challenge n M b (dlc_genEquiv H G n ((r, u₁), u₂), (rM, dlc_encEquiv H n u₃)) =
      pairEncode (egGenParts n (pairFstD (G.gen.runAt n [] r)) (pairFstD (pairSndD (G.gen.runAt n [] r)))
          (List.ofFn u₁) (List.ofFn u₂)).1
        (egEncParts n (egGenParts n (pairFstD (G.gen.runAt n [] r))
            (pairFstD (pairSndD (G.gen.runAt n [] r))) (List.ofFn u₁) (List.ofFn u₂)).1
          (if b then pairSndD (M.runAt n (egGenParts n (pairFstD (G.gen.runAt n [] r))
              (pairFstD (pairSndD (G.gen.runAt n [] r))) (List.ofFn u₁) (List.ofFn u₂)).1 rM)
            else pairFstD (M.runAt n (egGenParts n (pairFstD (G.gen.runAt n [] r))
              (pairFstD (pairSndD (G.gen.runAt n [] r))) (List.ofFn u₁) (List.ofFn u₂)).1 rM))
          (List.ofFn u₃)) := by
  have hl : (List.ofFn r).length = G.gen.coinLen n := List.length_ofFn
  have hl₁ : (List.ofFn u₁).length = n * n := List.length_ofFn
  have hgen : (egGen H G).runAt n [] (dlc_genEquiv H G n ((r, u₁), u₂)) =
      pairEncode (egGenParts n (pairFstD (G.gen.runAt n [] r)) (pairFstD (pairSndD (G.gen.runAt n [] r)))
          (List.ofFn u₁) (List.ofFn u₂)).1
        (egGenParts n (pairFstD (G.gen.runAt n [] r)) (pairFstD (pairSndD (G.gen.runAt n [] r)))
          (List.ofFn u₁) (List.ofFn u₂)).2 := by
    rw [egGen_runAt, dlc_genEquiv_ofFn, List.take_left' hl, List.drop_left' hl, List.take_left' hl₁,
      ← List.drop_drop, List.drop_left' hl, List.drop_left' hl₁, ← NUPPT.runAt_eq]
  unfold GroupPKScheme.challenge
  dsimp only [elGamal]
  rw [hgen, pairFstD_pairEncode, egEnc_runAt, dlc_encEquiv_ofFn]

/-- **The derived generator on split coins**: `egGroupParts` on `G`'s output and the segment of `g`. -/
private theorem dlc_grp_runAt (H : ArithmeticFP) (G : SafePrimeGen) (n : ℕ) (r : G.gen.Coins n)
    (u₁ : Fin (n * n) → Bool) :
    (egGroupGen H G).gen.runAt n [] (dlc_grpEquiv H G n (r, u₁)) =
      egGroupParts n (pairFstD (G.gen.runAt n [] r)) (pairFstD (pairSndD (G.gen.runAt n [] r)))
        (List.ofFn u₁) := by
  have hl : (List.ofFn r).length = G.gen.coinLen n := List.length_ofFn
  have hl₁ : (List.ofFn u₁).length = n * n := List.length_ofFn
  show (egGroupGenMachine H G).runAt n [] _ = _
  rw [egGroupGenMachine_runAt]
  unfold dlc_grpEquiv
  rw [dlc_splitEquiv_symm_ofFn, List.take_left' hl, List.drop_left' hl,
    List.take_of_length_le hl₁.le, ← NUPPT.runAt_eq]

/-- **Hybrid 1, pointwise**: outside the event `g² ≡ 1 (mod p)`, the challenge with bit `b` and the
DDH distinguisher `D_b` on the real tuple of the derived generator run `D` on the same string with
the same coins (the exponents are the same samplers, `h^{(ab mod q)} = h^{ab}` since `h` has order
`q`, and `egSquareGen p g = g² mod p`).

**Proof sketch.** Both sides are `D` on one string (`NUPPT.distinguisher_eq`,
`NUPPT.distinguisherL_eq`, `he`, `dlc_challenge_eq`). The derived index `i` (`dlc_grp_runAt`) is
valid and well formed, `⟨p, ⟨q, h⟩⟩` with `p`, `q` from `G`'s index (`wellFormedIndex_iff`,
`safePrimeValid_iff`) and `h = egSquareGen p g = g² mod p` off the bad event, of order `q`
(`egSquareGen_valid`). The padding of the tuple is lossless (`dlc_ofFn_padFin`, `length_ddhTuple`),
so `D_b` reads `⟨i, X⟩`, `Y` and `Z` back. The exponent `ddhExpo n i u` has the value of the sampler
`sampleBelowL q (Nat.size q) n n u` of `egGenParts`/`egEncParts` (`expOrd_of_valid`,
`ZMod.val_natCast`, `sampleBelowL_lt`), `expF i z` is the numeral of `h^z mod p` (`expF_eq`,
`WellFormedIndex.dlW_eq`), and `(h^x mod p)^y · c ≡ h^{xy mod q} · c (mod p)` since `h` has order
`q` (`ZMod.val_mul`, `pow_mod_orderOf`, `ZMod.natCast_eq_natCast_iff'`). -/
private theorem dlc_hyb1_point (H : ArithmeticFP) (G : SafePrimeGen) (M D Db : NUPPT) (b : Bool) {n : ℕ}
    (hn : G.n₀ ≤ n) (e : M.Coins n × D.Coins n ≃ Db.Coins n)
    (he : ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
      Db.runAt n w (e (rM, rD)) = D.runAt n (dlc_ddhInput n b w (M.runAt n (dlc_tuplePk w) rM)) rD)
    (r : G.gen.Coins n) (u₁ u₂ u₃ : Fin (n * n) → Bool) (rM : M.Coins n) (rD : D.Coins n)
    (hgood : ¬ egUnit n (dlP (G.gen.runAt n [] r)) (List.ofFn u₁) ^ 2 % dlP (G.gen.runAt n [] r) = 1) :
    D.distinguisherL n
        ((elGamal H G).challenge n M b (dlc_genEquiv H G n ((r, u₁), u₂), (rM, dlc_encEquiv H n u₃))) rD =
      Db.distinguisher n (ddhLen.eval n)
        ((ddhReal (egGroupGen H G)).X n (dlc_grpEquiv H G n (r, u₁), (u₂, u₃))) (e (rM, rD)) := by
  rw [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, he, dlc_challenge_eq]
  dsimp only [ddhReal]
  -- the index of the derived generator: valid and well formed
  have hvi : SafePrimeValid ((egGroupGen H G).gen.runAt n [] (dlc_grpEquiv H G n (r, u₁))) :=
    (egGroupGen H G).valid n _ hn
  have hwi : WellFormedIndex n ((egGroupGen H G).gen.runAt n [] (dlc_grpEquiv H G n (r, u₁))) :=
    (egGroupGen H G).wellFormed n _ hn
  have hi := dlc_grp_runAt H G n r u₁
  generalize (egGroupGen H G).gen.runAt n [] (dlc_grpEquiv H G n (r, u₁)) = i at hvi hwi hi ⊢
  -- the safe-prime instance of `G`
  have hv := G.valid n r hn
  obtain ⟨a, bq, cc, ho, ha, hb, -⟩ := (wellFormedIndex_iff n _).1 (G.wellFormed n r hn)
  rw [ho] at hv hgood hi ⊢
  simp only [safePrimeValid_iff, expValid_iff, dlP_eq, dlM_eq, pairFstD_pairEncode,
    pairSndD_pairEncode] at hv hgood hi ⊢
  haveI : Fact (listToNat a).Prime := ⟨hv.1.1⟩
  haveI : Fact (listToNat bq).Prime := ⟨hv.2.1⟩
  have hpq : listToNat a = 2 * listToNat bq + 1 := hv.2.2
  have hp0 : 0 < listToNat a := hv.1.1.pos
  have hpn : listToNat a < 2 ^ n := ha ▸ listToNat_lt_two_pow a
  have hq0 : 0 < listToNat bq := hv.2.1.pos
  have hg0 := egUnit_pos n (listToNat a) (List.ofFn u₁)
  have hgp := egUnit_lt hv.1.1.two_le n (List.ofFn u₁)
  obtain ⟨-, -, hord⟩ := egSquareGen_valid hpq hg0 hgp
  have hsq : egSquareGen (listToNat a) (egUnit n (listToNat a) (List.ofFn u₁)) =
      egUnit n (listToNat a) (List.ofFn u₁) ^ 2 % listToNat a := if_neg hgood
  rw [hsq] at hord
  simp only [egGroupParts, hsq] at hi
  have hhp : egUnit n (listToNat a) (List.ofFn u₁) ^ 2 % listToNat a < listToNat a := Nat.mod_lt _ hp0
  unfold egGenParts egEncParts
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, dlP_eq, dlM_eq, dlG_eq]
  generalize egUnit n (listToNat a) (List.ofFn u₁) ^ 2 % listToNat a = h at hord hi hhp ⊢
  -- the tuple
  rw [dlc_ofFn_padFin (by rw [length_ddhTuple hwi, eval_ddhLen])]
  unfold dlc_ddhInput dlc_tuplePk ddhTuple
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  have hsamp : ∀ u : Fin (n * n) → Bool,
      (sampleBelowL (listToNat bq) (Nat.size (listToNat bq)) n n (List.ofFn u)).getD 0 < listToNat bq := by
    intro u
    rcases hs : sampleBelowL (listToNat bq) (Nat.size (listToNat bq)) n n (List.ofFn u) with _ | v
    · exact hq0
    · rw [Option.getD_some]
      exact sampleBelowL_lt hs
  have hP : dlP i = listToNat a := by rw [hi, dlP_eq, pairFstD_pairEncode]
  have hM : dlM i = listToNat bq := by rw [hi, dlM_eq, pairSndD_pairEncode, pairFstD_pairEncode]
  have hG : dlG i = h := by
    rw [hi, dlG_eq, pairSndD_pairEncode, pairSndD_pairEncode, listToNat_natToList (hhp.trans hpn)]
  have hW : dlW i = n := hwi.dlW_eq
  have hE : expOrd i = listToNat bq := by rw [expOrd_of_valid hvi.expValid, hM]
  have hexpF : ∀ z, expF i z = natToList n (h ^ z.val % listToNat a) := fun z => by
    rw [expF_eq, hW, hG, hP]
  have hval : ∀ u : Fin (n * n) → Bool, (ddhExpo n i u).val =
      (sampleBelowL (listToNat bq) (Nat.size (listToNat bq)) n n (List.ofFn u)).getD 0 := by
    intro u
    unfold ddhExpo
    rw [ZMod.val_natCast, hE, Nat.mod_eq_of_lt (hsamp u)]
  rw [hexpF, hexpF, hexpF, ZMod.val_mul, hval, hval, hE, hP, hM, hi]
  have key : ∀ x y c : ℕ, (h ^ x % listToNat a) ^ y * c % listToNat a =
      h ^ (x * y % listToNat bq) % listToNat a * c % listToNat a := by
    intro x y c
    have hcast : (((h ^ x % listToNat a) ^ y * c % listToNat a : ℕ) : ZMod (listToNat a)) =
        ((h ^ (x * y % listToNat bq) % listToNat a * c % listToNat a : ℕ) : ZMod (listToNat a)) := by
      push_cast [ZMod.natCast_mod]
      rw [← hord, pow_mod_orderOf, pow_mul]
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hcast
    rwa [Nat.mod_mod, Nat.mod_mod] at this
  rw [listToNat_natToList (hhp.trans hpn), listToNat_natToList ((Nat.mod_lt _ hp0).trans hpn),
    listToNat_natToList ((Nat.mod_lt _ hp0).trans hpn), key]

/-- **Hybrid 1**: for `n ≥ n₀` the challenge with bit `b` and the DDH distinguisher `D_b` on the
real ensemble of the derived generator are accepted with probabilities within
`Pr[g² ≡ 1] ≤ δ n + 9 · (1/2)^n` (the coins identified by `dlc_genEquiv`, `dlc_encEquiv`,
`dlc_grpEquiv` and `e`; `dlc_hyb1_point`, `dlc_uprob_bad_le`).

**Proof sketch.** Relabel both acceptance probabilities over the common coin space `((r, u₁), (u₂,
(u₃, (r_M, r_D))))` (`acceptProb_def`, `uprob_comp_equiv` with `E₁`, built from `dlc_genEquiv` and
`dlc_encEquiv`, and `E₂`, built from `dlc_grpEquiv` and `e`). Off the event `g² ≡ 1 (mod p)` the two
events coincide (`dlc_hyb1_point`), so the gap is at most the probability of the event
(`dlc_abs_uprob_sub_le_of_iff`), which depends on `(r, u₁)` only (`uprob_fst`) and is at most `δ n +
9 · (1/2)^n` (`dlc_uprob_bad_le`). -/
private theorem dlc_hyb1 (H : ArithmeticFP) (G : SafePrimeGen) {δ : ℕ → ℝ} (hδ : G.FullLengthExcept δ)
    (M D Db : NUPPT) (b : Bool) {n : ℕ} (hn : G.n₀ ≤ n) (e : M.Coins n × D.Coins n ≃ Db.Coins n)
    (he : ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
      Db.runAt n w (e (rM, rD)) = D.runAt n (dlc_ddhInput n b w (M.runAt n (dlc_tuplePk w) rM)) rD) :
    |acceptProb ((elGamal H G).challenge n M b) (D.distinguisherL n) -
      acceptProb ((ddhReal (egGroupGen H G)).X n) (Db.distinguisher n (ddhLen.eval n))| ≤
      δ n + 9 * (1 / 2) ^ n := by
  let E₁ : (G.gen.Coins n × (Fin (n * n) → Bool)) × ((Fin (n * n) → Bool) ×
      ((Fin (n * n) → Bool) × (M.Coins n × D.Coins n))) ≃
      ((elGamal H G).gen.Coins n × (M.Coins n × (elGamal H G).enc.Coins n)) × D.Coins n :=
    { toFun := fun ω => ((dlc_genEquiv H G n (ω.1, ω.2.1), (ω.2.2.2.1, dlc_encEquiv H n ω.2.2.1)),
        ω.2.2.2.2)
      invFun := fun s => (((dlc_genEquiv H G n).symm s.1.1).1, (((dlc_genEquiv H G n).symm s.1.1).2,
        ((dlc_encEquiv H n).symm s.1.2.2, (s.1.2.1, s.2))))
      left_inv := fun ω => by simp
      right_inv := fun s => by simp }
  let E₂ : (G.gen.Coins n × (Fin (n * n) → Bool)) × ((Fin (n * n) → Bool) ×
      ((Fin (n * n) → Bool) × (M.Coins n × D.Coins n))) ≃
      (ddhReal (egGroupGen H G)).σ n × Db.Coins n :=
    { toFun := fun ω => ((dlc_grpEquiv H G n ω.1, (ω.2.1, ω.2.2.1)), e ω.2.2.2)
      invFun := fun s => ((dlc_grpEquiv H G n).symm s.1.1, (s.1.2.1, (s.1.2.2, e.symm s.2)))
      left_inv := fun ω => by simp
      right_inv := fun s => by simp }
  rw [acceptProb_def, acceptProb_def, ← uprob_comp_equiv E₁, ← uprob_comp_equiv E₂]
  refine (dlc_abs_uprob_sub_le_of_iff (C := fun ω => egUnit n (dlP (G.gen.runAt n [] ω.1.1))
    (List.ofFn ω.1.2) ^ 2 % dlP (G.gen.runAt n [] ω.1.1) = 1) fun ω hω => ?_).trans ?_
  · obtain ⟨⟨r, u₁⟩, u₂, u₃, rM, rD⟩ := ω
    show D.distinguisherL n ((elGamal H G).challenge n M b
        (dlc_genEquiv H G n ((r, u₁), u₂), (rM, dlc_encEquiv H n u₃))) rD = true ↔
      Db.distinguisher n (ddhLen.eval n)
        ((ddhReal (egGroupGen H G)).X n (dlc_grpEquiv H G n (r, u₁), (u₂, u₃))) (e (rM, rD)) = true
    rw [dlc_hyb1_point H G M D Db b hn e he r u₁ u₂ u₃ rM rD hω]
  · exact (uprob_fst (fun z : G.gen.Coins n × (Fin (n * n) → Bool) =>
      egUnit n (dlP (G.gen.runAt n [] z.1)) (List.ofFn z.2) ^ 2 % dlP (G.gen.runAt n [] z.1) = 1)).le.trans
      (dlc_uprob_bad_le G hδ hn)

/-- The canonicalised message is `1` or an element of `G_q` (`0 < c < p`, `c^q ≡ 1`). -/
private theorem dlc_egCanon_cases (p q m : ℕ) :
    egCanon p q m = 1 ∨ (0 < egCanon p q m ∧ egCanon p q m < p ∧ egCanon p q m ^ q % p = 1) := by
  unfold egCanon
  split_ifs with h
  · exact Or.inr h
  · exact Or.inl rfl

/-- **Hybrid 3, one world**: at a valid well-formed index, replacing the exponent sampler by a
uniform `z ∈ Z_q` costs `(1/2)^n` (`ddhExpo_statClose`), and multiplying `h^z` by an element `c`
of `G_q` does not change the law (`dlc_exists_pow_eq`, `dlc_uprob_shift`).

**Proof sketch.** At the valid index (`safePrimeValid_iff`, `expValid_iff`) `g` has order `q =
expOrd i` (`expOrd_of_valid`), and the canonical message is `1 = g^0` or an element of `G_q`, hence
`g^k` (`dlc_egCanon_cases`, `dlc_exists_pow_eq`). `dlc_uprob_shift` puts the factor on the uniform
side, and the remaining gap is `ddhExpo_statClose` on the test `z ↦ Ψ ⟦g^z · c mod p⟧_n`. -/
private theorem dlc_rand_term {n : ℕ} {i : List Bool} (hvi : SafePrimeValid i) (hwi : WellFormedIndex n i)
    (Ψ : List Bool → Prop) (m : ℕ) :
    |uprob (fun u : Fin (n * n) → Bool => Ψ (natToList n (dlG i ^ (ddhExpo n i u).val % dlP i *
        egCanon (dlP i) (dlM i) m % dlP i))) -
      uprob (fun z : ZMod (expOrd i) => Ψ (natToList n (dlG i ^ z.val % dlP i)))| ≤ (1 / 2) ^ n := by
  obtain ⟨hev, hqp, hpq⟩ := (safePrimeValid_iff i).1 hvi
  have hev' := (expValid_iff i).1 hev
  haveI : Fact (dlP i).Prime := ⟨hev'.1⟩
  haveI : Fact (dlM i).Prime := ⟨hqp⟩
  have hord := hev'.2.2.2.2.2
  have hk : ∃ k : ℕ, ((dlG i : ℕ) : ZMod (dlP i)) ^ k =
      ((egCanon (dlP i) (dlM i) m : ℕ) : ZMod (dlP i)) := by
    rcases dlc_egCanon_cases (dlP i) (dlM i) m with h1 | ⟨h0, hlt, hq⟩
    · exact ⟨0, by rw [h1, pow_zero, Nat.cast_one]⟩
    · exact dlc_exists_pow_eq hpq hord h0 hlt hq
  obtain ⟨k, hk⟩ := hk
  have hord' : orderOf ((dlG i : ℕ) : ZMod (dlP i)) = expOrd i := by
    rw [hord, expOrd_of_valid hev]
  rw [← dlc_uprob_shift hord' hk n Ψ]
  exact (ddhExpo_statClose hev hwi).abs_uprob_sub_le
    (fun z => Ψ (natToList n (dlG i ^ z.val % dlP i * egCanon (dlP i) (dlM i) m % dlP i)))

/-- **The random world's acceptance event**: `D_b` on the random tuple of the derived generator
runs `D` on `⟨⟨i, g^a⟩, ⟨g^b, ⟦g^z · m'_b mod p⟧_n⟩⟩` with `z = ddhExpo n i u₃`.

**Proof sketch.** Unfold `D_b` on the random tuple (`NUPPT.distinguisher_eq`,
`NUPPT.distinguisherL_eq`, `he`, `ddhRandom`). The padding is lossless (`dlc_ofFn_padFin`,
`length_ddhTuple`), so the projections of `dlc_ddhInput` and `dlc_tuplePk` read the components of
the tuple back, and the numeral `Z = expF i z` reads as `g^z mod p` (`expF_eq`,
`listToNat_natToList` below `dlP_lt_two_pow`). -/
private theorem dlc_rand_accept (H : ArithmeticFP) (G : SafePrimeGen) (M D Db : NUPPT) (b : Bool) {n : ℕ}
    (hn : G.n₀ ≤ n) (e : M.Coins n × D.Coins n ≃ Db.Coins n)
    (he : ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
      Db.runAt n w (e (rM, rD)) = D.runAt n (dlc_ddhInput n b w (M.runAt n (dlc_tuplePk w) rM)) rD)
    (r : (egGroupGen H G).gen.Coins n) (u₁ u₂ u₃ : Fin (n * n) → Bool) (rM : M.Coins n) (rD : D.Coins n) :
    (Db.distinguisher n (ddhLen.eval n) ((ddhRandom (egGroupGen H G)).X n (r, (u₁, (u₂, u₃))))
        (e (rM, rD)) = true) ↔
      (fun W => D.runAt n (pairEncode (pairEncode ((egGroupGen H G).gen.runAt n [] r)
          (expF ((egGroupGen H G).gen.runAt n [] r) (ddhExpo n ((egGroupGen H G).gen.runAt n [] r) u₁)))
          (pairEncode (expF ((egGroupGen H G).gen.runAt n [] r)
            (ddhExpo n ((egGroupGen H G).gen.runAt n [] r) u₂)) W)) rD = [true])
        (natToList n (dlG ((egGroupGen H G).gen.runAt n [] r) ^
            (ddhExpo n ((egGroupGen H G).gen.runAt n [] r) u₃).val % dlP ((egGroupGen H G).gen.runAt n [] r) *
          egCanon (dlP ((egGroupGen H G).gen.runAt n [] r)) (dlM ((egGroupGen H G).gen.runAt n [] r))
            (listToNat (if b then pairSndD (M.runAt n (pairEncode ((egGroupGen H G).gen.runAt n [] r)
                (expF ((egGroupGen H G).gen.runAt n [] r)
                  (ddhExpo n ((egGroupGen H G).gen.runAt n [] r) u₁))) rM)
              else pairFstD (M.runAt n (pairEncode ((egGroupGen H G).gen.runAt n [] r)
                (expF ((egGroupGen H G).gen.runAt n [] r)
                  (ddhExpo n ((egGroupGen H G).gen.runAt n [] r) u₁))) rM))) %
          dlP ((egGroupGen H G).gen.runAt n [] r))) := by
  have hvi : SafePrimeValid ((egGroupGen H G).gen.runAt n [] r) := (egGroupGen H G).valid n r hn
  have hwi : WellFormedIndex n ((egGroupGen H G).gen.runAt n [] r) := (egGroupGen H G).wellFormed n r hn
  rw [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, he, decide_eq_true_iff]
  dsimp only [ddhRandom]
  generalize (egGroupGen H G).gen.runAt n [] r = i at hvi hwi ⊢
  have hp0 : 0 < dlP i := ((expValid_iff i).1 hvi.expValid).1.pos
  rw [dlc_ofFn_padFin (by rw [length_ddhTuple hwi, eval_ddhLen])]
  unfold dlc_ddhInput dlc_tuplePk ddhTuple
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [expF_eq i (ddhExpo n i u₃), listToNat_natToList ((Nat.mod_lt _ hp0).trans (dlP_lt_two_pow i))]

/-- **Hybrid 3, pointwise**: with everything but the coins of `z` fixed, the random worlds of
`D_0` and `D_1` are accepted with probabilities within `2 · (1/2)^n` (both are within `(1/2)^n`
of the same ideal probability, `dlc_rand_term`).

**Proof sketch.** Rewrite each event by `dlc_rand_accept` (`OneWay.uprob_congr`). With the index,
`u₁`, `u₂`, `r_M` and `r_D` fixed, the two events differ only in the message `m₀` or `m₁` given to
`dlc_rand_term`, which puts each within `(1/2)^n` of the same probability over a uniform `z ∈ Z_q`;
the triangle inequality gives `2 · (1/2)^n`. -/
private theorem dlc_hyb3_point (H : ArithmeticFP) (G : SafePrimeGen) (M D Db₀ Db₁ : NUPPT) {n : ℕ}
    (hn : G.n₀ ≤ n) (e₀ : M.Coins n × D.Coins n ≃ Db₀.Coins n)
    (he₀ : ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
      Db₀.runAt n w (e₀ (rM, rD)) = D.runAt n (dlc_ddhInput n false w (M.runAt n (dlc_tuplePk w) rM)) rD)
    (e₁ : M.Coins n × D.Coins n ≃ Db₁.Coins n)
    (he₁ : ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
      Db₁.runAt n w (e₁ (rM, rD)) = D.runAt n (dlc_ddhInput n true w (M.runAt n (dlc_tuplePk w) rM)) rD)
    (r : (egGroupGen H G).gen.Coins n) (u₁ u₂ : Fin (n * n) → Bool) (rM : M.Coins n) (rD : D.Coins n) :
    |uprob (fun u₃ : Fin (n * n) → Bool => Db₀.distinguisher n (ddhLen.eval n)
        ((ddhRandom (egGroupGen H G)).X n (r, (u₁, (u₂, u₃)))) (e₀ (rM, rD)) = true) -
      uprob (fun u₃ : Fin (n * n) → Bool => Db₁.distinguisher n (ddhLen.eval n)
        ((ddhRandom (egGroupGen H G)).X n (r, (u₁, (u₂, u₃)))) (e₁ (rM, rD)) = true)| ≤
      2 * (1 / 2) ^ n := by
  rw [OneWay.uprob_congr fun u₃ => dlc_rand_accept H G M D Db₀ false hn e₀ he₀ r u₁ u₂ u₃ rM rD,
    OneWay.uprob_congr fun u₃ => dlc_rand_accept H G M D Db₁ true hn e₁ he₁ r u₁ u₂ u₃ rM rD]
  have hvi : SafePrimeValid ((egGroupGen H G).gen.runAt n [] r) := (egGroupGen H G).valid n r hn
  have hwi : WellFormedIndex n ((egGroupGen H G).gen.runAt n [] r) := (egGroupGen H G).wellFormed n r hn
  generalize (egGroupGen H G).gen.runAt n [] r = i at hvi hwi ⊢
  have t₀ := dlc_rand_term hvi hwi (fun W => D.runAt n (pairEncode (pairEncode i (expF i (ddhExpo n i u₁)))
    (pairEncode (expF i (ddhExpo n i u₂)) W)) rD = [true])
    (listToNat (pairFstD (M.runAt n (pairEncode i (expF i (ddhExpo n i u₁))) rM)))
  have t₁ := dlc_rand_term hvi hwi (fun W => D.runAt n (pairEncode (pairEncode i (expF i (ddhExpo n i u₁)))
    (pairEncode (expF i (ddhExpo n i u₂)) W)) rD = [true])
    (listToNat (pairSndD (M.runAt n (pairEncode i (expF i (ddhExpo n i u₁))) rM)))
  simp only [Bool.false_eq_true, if_false, if_true] at t₀ t₁ ⊢
  rw [abs_le] at t₀ t₁ ⊢
  constructor <;> linarith [t₀.1, t₀.2, t₁.1, t₁.2]

/-- **Hybrid 3**: for `n ≥ n₀` the random worlds of `D_0` and `D_1` are accepted with
probabilities within `2 · (1/2)^n` (average of `dlc_hyb3_point` over the other coins).

**Proof sketch.** Relabel the seeds and the coins of `D_b` so that the coins `u₃` of `z` come last
(`acceptProb_def`, `uprob_comp_equiv` with `E e_b`), split them off (`uprob_prod`), and bound the
gap of the averages by the pointwise gap (`abs_uexp_sub_le`, `dlc_hyb3_point`). -/
private theorem dlc_hyb3 (H : ArithmeticFP) (G : SafePrimeGen) (M D Db₀ Db₁ : NUPPT) {n : ℕ}
    (hn : G.n₀ ≤ n) (e₀ : M.Coins n × D.Coins n ≃ Db₀.Coins n)
    (he₀ : ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
      Db₀.runAt n w (e₀ (rM, rD)) = D.runAt n (dlc_ddhInput n false w (M.runAt n (dlc_tuplePk w) rM)) rD)
    (e₁ : M.Coins n × D.Coins n ≃ Db₁.Coins n)
    (he₁ : ∀ (w : List Bool) (rM : M.Coins n) (rD : D.Coins n),
      Db₁.runAt n w (e₁ (rM, rD)) = D.runAt n (dlc_ddhInput n true w (M.runAt n (dlc_tuplePk w) rM)) rD) :
    |acceptProb ((ddhRandom (egGroupGen H G)).X n) (Db₀.distinguisher n (ddhLen.eval n)) -
      acceptProb ((ddhRandom (egGroupGen H G)).X n) (Db₁.distinguisher n (ddhLen.eval n))| ≤
      2 * (1 / 2) ^ n := by
  let E : ∀ {Db : NUPPT}, (M.Coins n × D.Coins n ≃ Db.Coins n) →
      ((((egGroupGen H G).gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))) ×
        (M.Coins n × D.Coins n)) × (Fin (n * n) → Bool)) ≃
      (ddhRandom (egGroupGen H G)).σ n × Db.Coins n := fun e =>
    { toFun := fun ω => ((ω.1.1.1, (ω.1.1.2.1, (ω.1.1.2.2, ω.2))), e ω.1.2)
      invFun := fun s => (((s.1.1, (s.1.2.1, s.1.2.2.1)), e.symm s.2), s.1.2.2.2)
      left_inv := fun ω => by simp
      right_inv := fun s => by simp }
  rw [acceptProb_def, acceptProb_def, ← uprob_comp_equiv (E e₀), ← uprob_comp_equiv (E e₁),
    uprob_prod, uprob_prod]
  refine abs_uexp_sub_le (by positivity) fun ρ => ?_
  obtain ⟨⟨r, u₁, u₂⟩, rM, rD⟩ := ρ
  exact dlc_hyb3_point H G M D Db₀ Db₁ hn e₀ he₀ e₁ he₁ r u₁ u₂ rM rD

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

**Proof sketch.** Fix `M, D`. For each bit `b` build the DDH distinguisher `D_b`
(`NUPPT.exists_comp`, `NUPPT.exists_compParam`, `NUPPT.exists_seq`; the advice is `M`'s and `D`'s,
the bit is fixed in the machine, and the coins `M.coins + D.coins` are identified with
`M.Coins n × D.Coins n`): on a tuple `t = ⟨i, ⟨X, ⟨Y, Z⟩⟩⟩` it runs `M(1^n, ⟨i, X⟩)`, takes the
`b`-th message, canonicalises it to `m'_b`, and runs `D(1^n, ⟨⟨i, X⟩, ⟨Y, ⟦Z · m'_b mod p⟧_n⟩⟩)`.
The numbers are read by value (`listToNat`), so the padding to `15n + 14`, lossless from `n₀` on
(`length_ddhTuple`), needs no cut; the pre-processing is polynomial-time over the bundle
(`H.modExp`, `H.mul`, `H.divMod`, `H.le`, `polyTimeComputable_ite`). *Hybrid 1* (the
square-versus-generator event): the coins of `challenge n M b` and of `D_b` on
`ddhReal (egGroupGen H G)` are both relabelled from `G`'s coins, the `n · n`-bit segments of `g`,
`a` and `b'`, and the coins of `M` and `D` (`uprob_comp_equiv`; `egGen_runAt`, `egEnc_runAt`,
`egGroupGenMachine_runAt`). Off the event `g² ≡ 1 (mod p)` the two runs give `D` the same string
and coins: `ddhExpo` is the sampler `sampleBelowL q (Nat.size q) n n` of `egGenParts`/`egEncParts`
(`expOrd_of_valid`), `h^{(ab' mod q)} = h^{ab'}` since `h` has order `q` (`egSquareGen_valid`,
`pow_mod_orderOf`), and `egSquareGen p g = g² mod p`. Hence the gap is at most `Pr[g² ≡ 1]`
(`statClose_of_uprob_ne`). By `statClose_sampleBelowL` with `m = p − 1` and the count of the roots
`v ∈ {0, p − 2}` of `(v + 1)² ≡ 1` in `Fin (p − 1)`, `Pr[g² ≡ 1] ≤ 2/(p − 1) + (1/2)^n`, and
`2/(p − 1) ≤ 8 (1/2)^n` when `2^{n−1} ≤ p`; for `n ≥ n₀`, `hbig` bounds the coins with
`p < 2^{n−1}` by `δ n`. Altogether the hybrid-1 gap is at most `η n := δ n + 9 (1/2)^n`.
*Hybrid 2* (DDH): `hDDH` through `ddhAssumption_iff` and `Ensemble.indist_iff_exists_negligible`
gives a negligible `ε_b` with `|Pr[D_b(ddhReal)] − Pr[D_b(ddhRandom)]| ≤ ε_b n`. *Hybrid 3* (the
two random worlds): in `ddhRandom` the coins of `z = ddhExpo n i e₃` are used nowhere else; with
the other coins fixed, replacing `z` by a uniform `z ∈ Z_q` costs `(1/2)^n` (`ddhExpo_statClose`),
and `m'_b ∈ G_q` is `h^k` (`zpowers_eq_QR`), so the shift `z ↦ z + k` (`Equiv.addRight`,
`uprob_comp_equiv`) shows that `h^z · m'_b` has the law of `h^z`; averaging (`uprob_prod`) gives
`|Pr[D_0(ddhRandom)] − Pr[D_1(ddhRandom)]| ≤ 2 (1/2)^n`. Hence the advantage is at most
`2 (|δ n| + 9 (1/2)^n) + ε_0 n + ε_1 n + 2 (1/2)^n` for `n ≥ n₀` and at most `1` below (the
indicator of `n < n₀`), negligible by `negligible_two_pow_neg`, `negligible_zero`,
`Negligible.const_mul`, `Negligible.add` and `Negligible.mono` (`|δ|`, because `δ` is known to
be nonnegative only from `n₀` on). -/
theorem elGamal_secure (H : ArithmeticFP) (G : SafePrimeGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ)
    (hDDH : DDHAssumption (egGroupGen H G)) : (elGamal H G).Secure := by
  obtain ⟨δ, hδneg, hδ⟩ := hbig
  intro M D
  obtain ⟨Db₀, hDb₀⟩ := dlc_exists_ddhDist H M D false
  obtain ⟨Db₁, hDb₁⟩ := dlc_exists_ddhDist H M D true
  have hind := (Ensemble.indist_iff_exists_negligible _ _).1 ((ddhAssumption_iff _).1 hDDH)
  obtain ⟨ε₀, hε₀, hlt₀⟩ := hind Db₀
  obtain ⟨ε₁, hε₁, hlt₁⟩ := hind Db₁
  have hhalf : Negligible fun n => (1 / 2 : ℝ) ^ n := by
    simpa only [one_div] using negligible_two_pow_neg
  have habs : Negligible fun n => |δ n| := hδneg.mono ⟨0, fun n _ => by rw [abs_abs]⟩
  have hsmall : Negligible fun n => if n < G.n₀ then (1 : ℝ) else 0 :=
    negligible_zero.mono ⟨G.n₀, fun n hn => by rw [if_neg (not_lt.2 hn)]⟩
  refine ⟨fun n => 2 * (|δ n| + 9 * (1 / 2) ^ n) + ε₀ n + ε₁ n + 2 * (1 / 2) ^ n +
      (if n < G.n₀ then 1 else 0),
    (((((habs.add (hhalf.const_mul 9)).const_mul 2).add hε₀).add hε₁).add (hhalf.const_mul 2)).add hsmall,
    fun n => ?_⟩
  beta_reduce
  have hd₀ : 0 ≤ distAdv ((ddhReal (egGroupGen H G)).X n) ((ddhRandom (egGroupGen H G)).X n)
      (Db₀.distinguisher n (ddhLen.eval n)) := by rw [distAdv_def]; exact abs_nonneg _
  have hd₁ : 0 ≤ distAdv ((ddhReal (egGroupGen H G)).X n) ((ddhRandom (egGroupGen H G)).X n)
      (Db₁.distinguisher n (ddhLen.eval n)) := by rw [distAdv_def]; exact abs_nonneg _
  have hε₀n := (hlt₀ n)
  have hε₁n := (hlt₁ n)
  have hδn : 0 ≤ |δ n| := abs_nonneg _
  have h2n : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  by_cases hn : G.n₀ ≤ n
  · obtain ⟨e₀, he₀⟩ := hDb₀ n
    obtain ⟨e₁, he₁⟩ := hDb₁ n
    have h1₀ := dlc_hyb1 H G hδ M D Db₀ false hn e₀ he₀
    have h1₁ := dlc_hyb1 H G hδ M D Db₁ true hn e₁ he₁
    have h3 := dlc_hyb3 H G M D Db₀ Db₁ hn e₀ he₀ e₁ he₁
    rw [distAdv_def] at hε₀n hε₁n ⊢
    rw [if_neg (not_lt.2 hn)]
    have hle : δ n ≤ |δ n| := le_abs_self _
    rw [abs_le] at h1₀ h1₁ h3 ⊢
    rw [abs_lt] at hε₀n hε₁n
    constructor <;> linarith [h1₀.1, h1₀.2, h1₁.1, h1₁.2, h3.1, h3.2, hε₀n.1, hε₀n.2, hε₁n.1, hε₁n.2]
  · rw [if_pos (not_le.1 hn)]
    have hb : distAdv ((elGamal H G).challenge n M false) ((elGamal H G).challenge n M true)
        (D.distinguisherL n) ≤ 1 := by
      rw [distAdv_def, acceptProb_def, acceptProb_def, abs_le]
      constructor <;> linarith [uprob_nonneg (fun z : ((elGamal H G).gen.Coins n ×
          (M.Coins n × (elGamal H G).enc.Coins n)) × D.Coins n =>
          D.distinguisherL n ((elGamal H G).challenge n M false z.1) z.2 = true),
        uprob_le_one (fun z : ((elGamal H G).gen.Coins n ×
          (M.Coins n × (elGamal H G).enc.Coins n)) × D.Coins n =>
          D.distinguisherL n ((elGamal H G).challenge n M false z.1) z.2 = true),
        uprob_nonneg (fun z : ((elGamal H G).gen.Coins n ×
          (M.Coins n × (elGamal H G).enc.Coins n)) × D.Coins n =>
          D.distinguisherL n ((elGamal H G).challenge n M true z.1) z.2 = true),
        uprob_le_one (fun z : ((elGamal H G).gen.Coins n ×
          (M.Coins n × (elGamal H G).enc.Coins n)) × D.Coins n =>
          D.distinguisherL n ((elGamal H G).challenge n M true z.1) z.2 = true)]
    linarith

end TCSlib.Cryptography.Candidates
