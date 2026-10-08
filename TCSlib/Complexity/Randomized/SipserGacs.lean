/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Classes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Sipser–Gács theorem: BPP ⊆ Σ₂ ∩ Π₂

Arora–Barak's Theorem 7.18: `BPP` sits in the second level of the polynomial
hierarchy.  The proof shows `BPP ⊆ Σ₂`: after error reduction the set `S_x`
of accepting random strings is either almost all of `{0,1}^m` or a tiny
fraction, and two quantifier alternations — "there exist shifts `u₁,…,u_k`
whose translates of `S_x` cover `{0,1}^m`" — distinguish the two cases.

## Main definitions

* `Randomized.InSigma2`, `Randomized.InPi2` — verifier-style `Σ₂ᵖ` and `Π₂ᵖ`
  (two quantified witness strings over an efficient predicate), the classes
  in which [AB09, Thm 7.18] places `BPP`.
* `Randomized.shiftOrVerifier` — the predicate
  `(u, v) ↦ ⋁_{i ≤ k} M(x, v ⊕ uᵢ)` built from a `BPP` verifier, where `u`
  encodes the `k` shifts `u₁,…,u_k` as one concatenated string.

## Main results (sorry-stubbed)

* `Randomized.sipser_gacs` — [AB09, Thm 7.18].

## Deviations from the source

`Σ₂ᵖ` is defined here in the same certificate style as the chapter's other
classes (an efficient two-witness predicate with polynomially-bounded
witness lengths), rather than via oracle machines or the book's Chapter 5
definitions; `Π₂ᵖ` is its complement-dual, and `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` becomes
"`L` and `Lᶜ` are both `Σ₂`".  As throughout `Randomized.Classes`,
"polynomial time" is the abstract notion `E`, and the single computability
fact the proof uses — that the shifted-OR predicate built from an efficient
verifier is an efficient two-witness predicate — is the explicit hypothesis
`hShift`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

variable (E : VerifierModel)

/-- `L ∈ Σ₂ᵖ`, certificate-style: there is an efficient two-witness
predicate `N` and polynomial witness-length bounds such that
`x ∈ L ↔ ∃ u ∀ v, N(x, u, v)`.  [AB09, Thm 7.18]'s target class, defined in
the style of [AB09, Def 7.4] (see the module docstring's **Deviations**). -/
def InSigma2 (L : Language Bool) : Prop :=
  ∃ (N : List Bool → List Bool → List Bool → Bool) (a₁ k₁ a₂ k₂ : ℕ),
    E.EffTwoWitness N ∧
    ∀ x : List Bool,
      x ∈ L ↔ ∃ u : List Bool, u.length = polyLen a₁ k₁ x.length ∧
        ∀ v : List Bool, v.length = polyLen a₂ k₂ x.length → N x u v = true

/-- `L ∈ Π₂ᵖ` iff its complement is in `Σ₂ᵖ` (equivalently,
`x ∈ L ↔ ∀ u ∃ v, …`). -/
def InPi2 (L : Language Bool) : Prop :=
  InSigma2 E Lᶜ

/-- The two-witness predicate `(u, v) ↦ ⋁_{i < k} M(x, v ⊕ uᵢ)`, where the
first witness `u` is the concatenation of `k` shift strings `u₁,…,u_k` of
length `p(|x|)` each and `⊕` is bitwise XOR: the predicate with which
[AB09, Thm 7.18]'s proof expresses "the translates of the accepting set by
`u₁,…,u_k` cover all random strings `v`". -/
def shiftOrVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → List Bool → Bool := fun x u v =>
  (List.range (k x.length)).any fun i =>
    M x (List.zipWith xor v ((u.drop (i * p x.length)).take (p x.length)))

/-- `E` recognizes the shifted-OR construction: from an efficient Boolean
verifier, the predicate `shiftOrVerifier M p k` is an efficient two-witness
predicate for polynomial block lengths `p` and shift counts `k` (closure of
polynomial time under XOR-shifts and a polynomial OR). -/
def ClosedUnderShiftOr : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.EffTwoWitness (shiftOrVerifier M (polyLen a k) (polyLen a' k'))

section Helpers

/-- `zipWith` of two `ofFn` lists is the `ofFn` of the pointwise image. -/
theorem zipWith_ofFn {α β γ : Type*} {m : ℕ} (f : α → β → γ)
    (a : Fin m → α) (b : Fin m → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) =
      List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- XOR-ing the random string with a fixed mask (on the left) preserves
probabilities: the map `r ↦ c ⊕ r` is an involution of `{0,1}^m`. -/
theorem randProb_xor_right {m : ℕ} (c : Fin m → Bool)
    (P : List Bool → Prop) [DecidablePred P] :
    randProb m (fun l => P (List.zipWith xor (List.ofFn c) l)) =
      randProb m P := by
  unfold randProb
  congr 2
  have hinv : ∀ r : Fin m → Bool,
      (fun i => xor (c i) (xor (c i) (r i))) = r := by
    intro r
    funext i
    cases c i <;> cases r i <;> rfl
  refine Finset.card_nbij' (fun r => fun i => xor (c i) (r i))
    (fun r => fun i => xor (c i) (r i)) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hr ⊢
    show P (List.ofFn fun i => xor (c i) (r i))
    rw [← zipWith_ofFn]
    exact hr
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hr ⊢
    show P (List.zipWith xor (List.ofFn c)
      (List.ofFn fun i => xor (c i) (r i)))
    rw [zipWith_ofFn, hinv r]
    exact hr
  · intro r _
    funext i
    show xor (c i) (xor (c i) (r i)) = r i
    cases c i <;> cases r i <;> rfl
  · intro r _
    funext i
    show xor (c i) (xor (c i) (r i)) = r i
    cases c i <;> cases r i <;> rfl

/-- XOR-ing the random string with a fixed mask (on the right) preserves
probabilities. -/
theorem randProb_xor_left {m : ℕ} (c : Fin m → Bool)
    (P : List Bool → Prop) [DecidablePred P] :
    randProb m (fun l => P (List.zipWith xor l (List.ofFn c))) =
      randProb m P := by
  have hswap : ∀ r : Fin m → Bool,
      List.zipWith xor (List.ofFn r) (List.ofFn c) =
        List.zipWith xor (List.ofFn c) (List.ofFn r) := by
    intro r
    rw [zipWith_ofFn, zipWith_ofFn]
    congr 1
    funext i
    cases c i <;> cases r i <;> rfl
  rw [randProb_congr (B := fun l => P (List.zipWith xor (List.ofFn c) l))
    fun r => by rw [hswap r]]
  exact randProb_xor_right c P

/-- The exponential beats the linear shift count:
`(19A+20)·X < 2^{(A+7)·X}` for `X ≥ 1`.  (The book's choice `k = ⌈m/n⌉+1`
needs `k < 2^n`, which fails at small `n`; balancing against the error
exponent instead works at every length.) -/
theorem shift_count_lt_two_pow (A X : ℕ) (hX : 1 ≤ X) :
    (19 * A + 20) * X < 2 ^ ((A + 7) * X) := by
  have h128 : 128 * X ≤ 128 ^ X := by
    clear hX
    induction X with
    | zero => omega
    | succ Y ih =>
      rcases Nat.eq_zero_or_pos Y with rfl | hY'
      · norm_num
      · have h1 : 128 ^ (Y + 1) = 128 ^ Y * 128 := pow_succ 128 Y
        nlinarith
  have hA : A + 1 ≤ 2 ^ A := Nat.lt_two_pow_self
  have hsplit : 2 ^ ((A + 7) * X) = (2 ^ A) ^ X * 128 ^ X := by
    rw [pow_mul, pow_add, mul_pow]
    norm_num
  have h3 : 2 ^ A ≤ (2 ^ A) ^ X := by
    conv_lhs => rw [← pow_one (2 ^ A)]
    exact Nat.pow_le_pow_right Nat.one_le_two_pow hX
  calc (19 * A + 20) * X < (128 * (A + 1)) * X :=
      (Nat.mul_lt_mul_right (by omega)).mpr (by omega)
    _ = (A + 1) * (128 * X) := by ring
    _ ≤ (2 ^ A) * (128 * X) := Nat.mul_le_mul_right _ hA
    _ ≤ (2 ^ A) ^ X * 128 ^ X := Nat.mul_le_mul h3 h128
    _ = 2 ^ ((A + 7) * X) := hsplit.symm

/-- The tail crunch for the constant advantage `1/6`: `(18b+18)·(n+1)^e`
majority repetitions drive the error below `2^{-b(n+1)^e}`. -/
theorem const_tail_bound (b e n : ℕ) :
    2 * (1 - 4 * (1/6 : ℚ) ^ 2) ^ (polyLen (18 * b + 18) e n / 2) ≤
      (1/2 : ℚ) ^ polyLen b e n := by
  have hx0 : (0:ℚ) ≤ 4 * (1/6 : ℚ) ^ 2 := by norm_num
  have hx1 : 4 * (1/6 : ℚ) ^ 2 ≤ 1 := by norm_num
  have hm : 1 ≤ ((9 : ℕ) : ℚ) * (4 * (1/6 : ℚ) ^ 2) := by norm_num
  have hexp : 9 * (polyLen b e n + 1) ≤ polyLen (18 * b + 18) e n / 2 := by
    unfold polyLen
    have h1 : (18 * b + 18) * (n + 1) ^ e / 2 = (9 * b + 9) * (n + 1) ^ e := by
      rw [show 18 * b + 18 = 2 * (9 * b + 9) from by ring, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h1]
    have hge : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hhalf := one_sub_pow_le_half_pow hx0 hx1 hm hexp
  calc 2 * (1 - 4 * (1/6 : ℚ) ^ 2) ^ (polyLen (18 * b + 18) e n / 2)
      ≤ 2 * (1/2 : ℚ) ^ (polyLen b e n + 1) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = (1/2 : ℚ) ^ polyLen b e n := by
        rw [pow_succ]
        ring

/-- Error reduction with an explicit error schedule `2^{-b(n+1)^e}` and an
explicit randomness schedule — the form [AB09, Thm 7.18]'s proof consumes:
a `BPP` witness `(M₀, a₀, k₀)` amplified by `(18b+18)·(n+1)^e` majority
repetitions. -/
theorem amplify_concrete (hMaj : ClosedUnderMajority E) {L : Language Bool}
    {M₀ : List Bool → List Bool → Bool} {a₀ k₀ : ℕ}
    (hM₀ : E.Eff (boolVerifier M₀))
    (hprop₀ : ∀ x : List Bool,
      (x ∈ L → 2/3 ≤
        randProb (polyLen a₀ k₀ x.length) fun r => M₀ x r = true) ∧
      (x ∉ L → 2/3 ≤
        randProb (polyLen a₀ k₀ x.length) fun r => M₀ x r = false))
    (b e : ℕ) :
    ∃ M : List Bool → List Bool → Bool,
      E.Eff (boolVerifier M) ∧
      ∀ x : List Bool,
        (x ∈ L → 1 - (1/2 : ℚ) ^ polyLen b e x.length ≤
          randProb (polyLen ((18 * b + 18) * a₀) (e + k₀) x.length)
            fun r => M x r = true) ∧
        (x ∉ L → 1 - (1/2 : ℚ) ^ polyLen b e x.length ≤
          randProb (polyLen ((18 * b + 18) * a₀) (e + k₀) x.length)
            fun r => M x r = false) := by
  classical
  refine ⟨majorityVerifier M₀ (polyLen a₀ k₀) (polyLen (18 * b + 18) e),
    hMaj M₀ a₀ k₀ (18 * b + 18) e hM₀, fun x => ?_⟩
  have hqK : polyLen ((18 * b + 18) * a₀) (e + k₀) x.length
      = polyLen (18 * b + 18) e x.length * polyLen a₀ k₀ x.length := by
    unfold polyLen
    ring
  set n := x.length with hn
  set q := polyLen a₀ k₀ n with hq
  set K := polyLen (18 * b + 18) e n with hK
  have hmaj_iff : ∀ l : List Bool,
      majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x l = true ↔
        K < 2 * blockCount q K (M₀ x) l := by
    intro l
    show decide (K < 2 * blockCount q K (M₀ x) l) = true ↔ _
    rw [decide_eq_true_iff]
  have hcount : ∀ l : List Bool,
      blockCount q K (M₀ x) l +
        blockCount q K (fun l' => !(M₀ x l')) l = K := by
    intro l
    unfold blockCount
    have haux : ∀ (p : ℕ → Bool) (li : List ℕ),
        li.countP p + li.countP (fun i => !(p i)) = li.length := by
      intro p li
      induction li with
      | nil => simp
      | cons hd tl ih =>
        rw [List.countP_cons, List.countP_cons, List.length_cons]
        rcases hp : p hd <;> simp [hp] <;> omega
    rw [haux (fun i => M₀ x ((l.drop (i * q)).take q)) (List.range K)]
    exact List.length_range
  have hs_false : randProb q (fun l => M₀ x l = false)
      = 1 - randProb q (fun l => M₀ x l = true) := randProb_bool_false (M₀ x)
  have hs_not : randProb q (fun l => (!(M₀ x l)) = true)
      = randProb q (fun l => M₀ x l = false) :=
    randProb_congr fun r => by simp
  rw [hqK]
  constructor
  · intro hx
    have hW := (hprop₀ x).1 hx
    have hsf : randProb q (fun l => (!(M₀ x l)) = true) ≤ 1/2 - 1/6 := by
      rw [hs_not, hs_false]
      linarith
    have htail := randProb_tail_le q K (fun l' => !(M₀ x l'))
      (by norm_num : (0:ℚ) ≤ 1/6) hsf
    have hev : randProb (K * q)
        (fun l => ¬ (majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x l = true))
        = randProb (K * q) (fun l =>
            K ≤ 2 * blockCount q K (fun l' => !(M₀ x l')) l) :=
      randProb_congr fun r => by
        rw [hmaj_iff]
        have := hcount (List.ofFn r)
        constructor
        · intro h
          omega
        · intro h
          omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M₀ (polyLen a₀ k₀)
        (polyLen (18 * b + 18) e) x l = true)
    rw [hev] at hnot
    have hfin : randProb (K * q) (fun l =>
        K ≤ 2 * blockCount q K (fun l' => !(M₀ x l')) l)
        ≤ (1/2 : ℚ) ^ polyLen b e n := le_trans htail (by
      rw [hK]
      exact const_tail_bound b e n)
    linarith
  · intro hx
    have hW := (hprop₀ x).2 hx
    have hst : randProb q (fun l => M₀ x l = true) ≤ 1/2 - 1/6 := by
      have := hs_false
      linarith
    have htail := randProb_tail_le q K (M₀ x)
      (by norm_num : (0:ℚ) ≤ 1/6) hst
    have hmono : randProb (K * q)
        (fun l => ¬ (majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x l = false))
        ≤ randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M₀ x) l) := by
      refine randProb_mono fun r hr => ?_
      have h1 : majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x (List.ofFn r) = true := by
        rcases hb : majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x (List.ofFn r)
        · exact absurd hb hr
        · rfl
      have h2 := (hmaj_iff (List.ofFn r)).mp h1
      omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M₀ (polyLen a₀ k₀)
        (polyLen (18 * b + 18) e) x l = false)
    have hfin : randProb (K * q) (fun l =>
        K ≤ 2 * blockCount q K (M₀ x) l)
        ≤ (1/2 : ℚ) ^ polyLen b e n := le_trans htail (by
      rw [hK]
      exact const_tail_bound b e n)
    linarith

end Helpers

/-- **Sipser–Gács** ([AB09, Thm 7.18]): `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` — relative to the
efficiency notion `E`, under the closure hypotheses the proof uses.

**Proof sketch.** It suffices to prove `BPP ⊆ Σ₂ᵖ` and apply it to `Lᶜ`,
since `BPP` is closed under complementation (`InBPP.compl`, which is where
the hypothesis `hNot` is used).  Given `L ∈ BPP` with a verifier using
`m₀ = polyLen a₀ k₀ |x|` random bits — padded so that `a₀ ≥ 7`, hence
`m₀ ≥ 7` at every input length — amplify by majority (`hMaj`,
`majority_error_le`) with `13·m₀` repetitions to error at most `2^{−m₀}`;
the amplified verifier `M` uses `m = 13·m₀²` random bits.  Let
`S_x ⊆ {0,1}^m` be its accepting set, so `|S_x| ≥ (1−2^{−m₀})2^m` if
`x ∈ L` and `|S_x| ≤ 2^{−m₀}2^m` otherwise.  Take `k = 14·m₀` shifts —
note `14·m₀ = (14a₀)·(n+1)^{k₀}` *is* a `polyLen` schedule, as the
`shiftOrVerifier` closure requires.  (Claim 1) if `|S_x| ≤ 2^{m−m₀}` then
no `k` shifts of `S_x` cover `{0,1}^m`: `|⋃ᵢ (S_x ⊕ uᵢ)| ≤ k·2^{m−m₀} <
2^m` since `14m₀ < 2^{m₀}` (which holds for every length because `m₀ ≥ 7`:
`98 < 128` and the right side doubles per step — the book's choice
`k = ⌈m/n⌉ + 1` needs `k < 2^n` and fails at small `n`, so we balance
against `m₀` instead of `n`).  (Claim 2) if `|S_x| ≥ (1−2^{−m₀})2^m` then
random shifts cover: for fixed `v`,
`Pr_{u₁,…,u_k}[∀ i, v ⊕ uᵢ ∉ S_x] ≤ 2^{−m₀k} < 2^{−m}` since
`m₀·k = 14m₀² > 13m₀² = m`, so a union bound over the `2^m` strings `v`
leaves a positive-probability choice of shifts covering everything (the
probabilistic method).  Hence
`x ∈ L ↔ ∃ u₁,…,u_k ∀ v, ⋁ᵢ M(x, v ⊕ uᵢ)`, which is the `Σ₂`-shape
`shiftOrVerifier` expresses; all the lengths involved are `polyLen`
schedules. -/
theorem sipser_gacs (hMaj : ClosedUnderMajority E)
    (hNot : ClosedUnderNot E) (hShift : ClosedUnderShiftOr E)
    {L : Language Bool} (hL : InBPP E L) :
    InSigma2 E L ∧ InPi2 E L := by
  sorry

end Randomized
