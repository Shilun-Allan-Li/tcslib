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

## Main results

* `Randomized.bpp_subset_sigma2` — `BPP ⊆ Σ₂ᵖ`, the core argument.
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

/-- A set smaller than the whole type misses some element. -/
theorem exists_notMem_of_card_lt {α : Type*} [Fintype α]
    {S : Finset α} (h : S.card < Fintype.card α) : ∃ a, a ∉ S := by
  by_contra hall
  push_neg at hall
  have heq : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  rw [heq, Finset.card_univ] at h
  exact absurd h (lt_irrefl _)

/-- **`BPP ⊆ Σ₂ᵖ`**, the core of [AB09, Thm 7.18]. -/
theorem bpp_subset_sigma2 (hMaj : ClosedUnderMajority E)
    (hShift : ClosedUnderShiftOr E) {L : Language Bool} (hL : InBPP E L) :
    InSigma2 E L := by
  classical
  obtain ⟨M₀, a₀, k₀, hM₀, hprop₀⟩ := hL
  obtain ⟨M, hM, hprop⟩ := amplify_concrete E hMaj hM₀ hprop₀ (a₀ + 7) k₀
  refine ⟨shiftOrVerifier M (polyLen ((18 * (a₀ + 7) + 18) * a₀) (k₀ + k₀))
      (polyLen (19 * a₀ + 20) k₀),
    (19 * a₀ + 20) * ((18 * (a₀ + 7) + 18) * a₀), k₀ + (k₀ + k₀),
    (18 * (a₀ + 7) + 18) * a₀, k₀ + k₀,
    hShift M ((18 * (a₀ + 7) + 18) * a₀) (k₀ + k₀) (19 * a₀ + 20) k₀ hM,
    fun x => ?_⟩
  set n := x.length with hn
  set m := polyLen ((18 * (a₀ + 7) + 18) * a₀) (k₀ + k₀) n with hm
  set T := polyLen (a₀ + 7) k₀ n with hT
  set ks := polyLen (19 * a₀ + 20) k₀ n with hks
  have hX1 : 1 ≤ (n + 1) ^ k₀ := Nat.one_le_pow _ _ (by omega)
  have hulen : polyLen ((19 * a₀ + 20) * ((18 * (a₀ + 7) + 18) * a₀))
      (k₀ + (k₀ + k₀)) n = ks * m := by
    rw [hks, hm]
    unfold polyLen
    ring
  have hclaim1 : ((ks : ℕ) : ℚ) < 2 ^ T := by
    rw [hks, hT]
    unfold polyLen
    exact_mod_cast shift_count_lt_two_pow a₀ ((n + 1) ^ k₀) hX1
  have hclaim2 : m < T * ks := by
    rw [hm, hT, hks]
    unfold polyLen
    have hXX : (n + 1) ^ (k₀ + k₀) = (n + 1) ^ k₀ * (n + 1) ^ k₀ :=
      pow_add _ _ _
    rw [hXX]
    have hC : (18 * (a₀ + 7) + 18) * a₀ < (a₀ + 7) * (19 * a₀ + 20) := by
      nlinarith
    calc (18 * (a₀ + 7) + 18) * a₀ * ((n + 1) ^ k₀ * (n + 1) ^ k₀)
        < (a₀ + 7) * (19 * a₀ + 20) * ((n + 1) ^ k₀ * (n + 1) ^ k₀) := by
          have hXp : 0 < (n + 1) ^ k₀ * (n + 1) ^ k₀ := by positivity
          exact (Nat.mul_lt_mul_right hXp).mpr hC
      _ = (a₀ + 7) * (n + 1) ^ k₀ * ((19 * a₀ + 20) * (n + 1) ^ k₀) := by
          ring
  have hacc := hprop x
  rw [← hn, ← hm, ← hT] at hacc
  constructor
  · -- `x ∈ L`: the probabilistic method produces covering shifts
    intro hx
    have haccx := hacc.1 hx
    have hs1 : randProb m (fun l => M x l = true) ≤ 1 := randProb_le_one
    have hfail : 1 - randProb m (fun l => M x l = true) ≤ (1/2 : ℚ) ^ T := by
      linarith
    have hfail0 : (0:ℚ) ≤ 1 - randProb m (fun l => M x l = true) := by
      linarith
    have hbadv : ∀ v : Fin m → Bool,
        ((Finset.univ.filter fun u : Fin (ks * m) → Bool =>
          blockCount m ks (fun w => M x (List.zipWith xor (List.ofFn v) w))
            (List.ofFn u) = 0).card : ℚ)
          ≤ (1/2 : ℚ) ^ (T * ks) * 2 ^ (ks * m) := by
      intro v
      have hsB : randProb m (fun w =>
          M x (List.zipWith xor (List.ofFn v) w) = true)
          = randProb m (fun l => M x l = true) :=
        randProb_xor_right v (fun w => M x w = true)
      have hdist := randProb_blockCount m
        (fun w => M x (List.zipWith xor (List.ofFn v) w)) ks 0
        (Nat.zero_le _)
      rw [hsB] at hdist
      simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul,
        Nat.sub_zero] at hdist
      have hle : randProb (ks * m) (fun l =>
          blockCount m ks (fun w => M x (List.zipWith xor (List.ofFn v) w))
            l = 0) ≤ (1/2 : ℚ) ^ (T * ks) := by
        rw [hdist]
        calc (1 - randProb m (fun l => M x l = true)) ^ ks
            ≤ ((1/2 : ℚ) ^ T) ^ ks := pow_le_pow_left₀ hfail0 hfail ks
          _ = (1/2 : ℚ) ^ (T * ks) := by rw [← pow_mul]
      unfold randProb at hle
      rw [div_le_iff₀ (by positivity)] at hle
      exact hle
    have hexists : ∃ u : Fin (ks * m) → Bool, ∀ v : Fin m → Bool,
        blockCount m ks (fun w => M x (List.zipWith xor (List.ofFn v) w))
          (List.ofFn u) ≠ 0 := by
      by_contra hforall
      push_neg at hforall
      have hcover : (Finset.univ : Finset (Fin (ks * m) → Bool)) ⊆
          Finset.univ.biUnion (fun v : Fin m → Bool =>
            Finset.univ.filter fun u : Fin (ks * m) → Bool =>
              blockCount m ks
                (fun w => M x (List.zipWith xor (List.ofFn v) w))
                (List.ofFn u) = 0) := by
        intro u _
        obtain ⟨v, hv⟩ := hforall u
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v,
          Finset.mem_filter.mpr ⟨Finset.mem_univ u, hv⟩⟩
      have h1 : (2:ℕ) ^ (ks * m) ≤ (Finset.univ.biUnion
          (fun v : Fin m → Bool =>
            Finset.univ.filter fun u : Fin (ks * m) → Bool =>
              blockCount m ks
                (fun w => M x (List.zipWith xor (List.ofFn v) w))
                (List.ofFn u) = 0)).card := by
        rw [← card_univ_bitstrings (ks * m)]
        exact Finset.card_le_card hcover
      have h2 := Finset.card_biUnion_le
        (s := (Finset.univ : Finset (Fin m → Bool)))
        (t := fun v : Fin m → Bool =>
          Finset.univ.filter fun u : Fin (ks * m) → Bool =>
            blockCount m ks
              (fun w => M x (List.zipWith xor (List.ofFn v) w))
              (List.ofFn u) = 0)
      have h3 : ((2:ℚ)) ^ (ks * m) ≤
          ∑ v : Fin m → Bool, ((Finset.univ.filter
            fun u : Fin (ks * m) → Bool =>
              blockCount m ks
                (fun w => M x (List.zipWith xor (List.ofFn v) w))
                (List.ofFn u) = 0).card : ℚ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast le_trans h1 h2
      have h4 : ((2:ℚ)) ^ (ks * m) ≤
          (2:ℚ) ^ m * ((1/2 : ℚ) ^ (T * ks) * 2 ^ (ks * m)) := by
        calc ((2:ℚ)) ^ (ks * m)
            ≤ ∑ _v : Fin m → Bool, ((1/2 : ℚ) ^ (T * ks) * 2 ^ (ks * m)) :=
              le_trans h3 (Finset.sum_le_sum fun v _ => hbadv v)
          _ = (2:ℚ) ^ m * ((1/2 : ℚ) ^ (T * ks) * 2 ^ (ks * m)) := by
              rw [Finset.sum_const, card_univ_bitstrings, nsmul_eq_mul]
              push_cast
              ring
      have hlt : ((2:ℚ)) ^ m < 2 ^ (T * ks) :=
        pow_lt_pow_right₀ (by norm_num) hclaim2
      have hfrac : (2:ℚ) ^ m * (1/2 : ℚ) ^ (T * ks) < 1 := by
        rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
        exact hlt
      nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) (ks * m), h4, hfrac]
    obtain ⟨u, hu⟩ := hexists
    refine ⟨List.ofFn u, ?_, ?_⟩
    · rw [List.length_ofFn]
      exact hulen.symm
    · intro v hvlen
      obtain ⟨v', hv'⟩ := exists_ofFn_eq hvlen
      have hbc := hu v'
      have hpos : 0 < blockCount m ks
          (fun w => M x (List.zipWith xor (List.ofFn v') w))
          (List.ofFn u) := Nat.pos_of_ne_zero hbc
      unfold blockCount at hpos
      rw [List.countP_pos_iff] at hpos
      obtain ⟨i, hi_mem, hi⟩ := hpos
      show (List.range ks).any _ = true
      rw [List.any_eq_true]
      refine ⟨i, hi_mem, ?_⟩
      rw [hv']
      exact hi
  · -- `x ∉ L`: no shifts can cover, by counting the accepted strings
    rintro ⟨u, hu_len, hall⟩
    by_contra hx
    have hrej := hacc.2 hx
    have hboolf := randProb_bool_false (m := m) (M x)
    have hst : randProb m (fun l => M x l = true) ≤ (1/2 : ℚ) ^ T := by
      linarith
    rw [hulen] at hu_len
    have hblock_len : ∀ i, i < ks → ((u.drop (i * m)).take m).length = m := by
      intro i hi
      have h1 : (i + 1) * m ≤ ks * m := Nat.mul_le_mul_right m (by omega)
      rw [Nat.succ_mul] at h1
      rw [List.length_take, List.length_drop, hu_len]
      omega
    have hacc_card : ∀ i ∈ Finset.range ks,
        ((Finset.univ.filter fun v : Fin m → Bool =>
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true).card : ℚ) ≤ (1/2 : ℚ) ^ T * 2 ^ m := by
      intro i hi
      obtain ⟨ci, hci⟩ := exists_ofFn_eq (hblock_len i (Finset.mem_range.mp hi))
      have hxor : randProb m (fun l =>
          M x (List.zipWith xor l (List.ofFn ci)) = true)
          = randProb m (fun l => M x l = true) :=
        randProb_xor_left ci (fun w => M x w = true)
      have hle : randProb m (fun l =>
          M x (List.zipWith xor l ((u.drop (i * m)).take m)) = true)
          ≤ (1/2 : ℚ) ^ T := by
        rw [show (u.drop (i * m)).take m = List.ofFn ci from hci, hxor]
        exact hst
      unfold randProb at hle
      rw [div_le_iff₀ (by positivity)] at hle
      exact hle
    have hcover : (Finset.univ.filter fun v : Fin m → Bool =>
        ∃ i ∈ Finset.range ks,
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true) ⊆
        (Finset.range ks).biUnion (fun i =>
          Finset.univ.filter fun v : Fin m → Bool =>
            M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
              = true) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨-, i, hi, hMi⟩ := hv
      exact Finset.mem_biUnion.mpr ⟨i, hi,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMi⟩⟩
    have hcard : ((Finset.univ.filter fun v : Fin m → Bool =>
        ∃ i ∈ Finset.range ks,
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true).card : ℚ) < 2 ^ m := by
      have h1 := Finset.card_le_card hcover
      have h2 := Finset.card_biUnion_le (s := Finset.range ks)
        (t := fun i => Finset.univ.filter fun v : Fin m → Bool =>
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true)
      have h3 : ((Finset.univ.filter fun v : Fin m → Bool =>
          ∃ i ∈ Finset.range ks, M x (List.zipWith xor (List.ofFn v)
            ((u.drop (i * m)).take m)) = true).card : ℚ) ≤
          ∑ i ∈ Finset.range ks, ((Finset.univ.filter
            fun v : Fin m → Bool => M x (List.zipWith xor (List.ofFn v)
              ((u.drop (i * m)).take m)) = true).card : ℚ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast le_trans h1 h2
      have h6 : (ks : ℚ) * ((1/2 : ℚ) ^ T * 2 ^ m) < 2 ^ m := by
        have h7 : (ks : ℚ) * (1/2 : ℚ) ^ T < 1 := by
          rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
          exact hclaim1
        nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) m, h7]
      calc ((Finset.univ.filter fun v : Fin m → Bool =>
          ∃ i ∈ Finset.range ks, M x (List.zipWith xor (List.ofFn v)
            ((u.drop (i * m)).take m)) = true).card : ℚ)
          ≤ ∑ i ∈ Finset.range ks, ((Finset.univ.filter
              fun v : Fin m → Bool => M x (List.zipWith xor (List.ofFn v)
                ((u.drop (i * m)).take m)) = true).card : ℚ) := h3
        _ ≤ ∑ _i ∈ Finset.range ks, ((1/2 : ℚ) ^ T * 2 ^ m) :=
            Finset.sum_le_sum hacc_card
        _ = (ks : ℚ) * ((1/2 : ℚ) ^ T * 2 ^ m) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ < 2 ^ m := h6
    have hcardN : (Finset.univ.filter fun v : Fin m → Bool =>
        ∃ i ∈ Finset.range ks,
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true).card < Fintype.card (Fin m → Bool) := by
      have hcardfun : Fintype.card (Fin m → Bool) = 2 ^ m := by
        rw [← card_univ_bitstrings m, Finset.card_univ]
      rw [hcardfun]
      exact_mod_cast hcard
    obtain ⟨v', hv'⟩ := exists_notMem_of_card_lt hcardN
    have hvfalse : ∀ i ∈ List.range ks,
        M x (List.zipWith xor (List.ofFn v')
          ((u.drop (i * m)).take m)) = false := by
      intro i hi
      rw [List.mem_range] at hi
      rcases hb : M x (List.zipWith xor (List.ofFn v')
          ((u.drop (i * m)).take m))
      · rfl
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨i, Finset.mem_range.mpr hi, hb⟩⟩) hv'
    have hN := hall (List.ofFn v') (by rw [List.length_ofFn])
    have hfalse : shiftOrVerifier M
        (polyLen ((18 * (a₀ + 7) + 18) * a₀) (k₀ + k₀))
        (polyLen (19 * a₀ + 20) k₀) x u (List.ofFn v') = false := by
      show (List.range ks).any _ = false
      rw [List.any_eq_false]
      intro i hi
      show ¬ (M x (List.zipWith xor (List.ofFn v')
        ((u.drop (i * m)).take m)) = true)
      rw [hvfalse i hi]
      simp
    rw [hN] at hfalse
    exact absurd hfalse (by simp)

/-- **Sipser–Gács** ([AB09, Thm 7.18]): `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` — relative to the
efficiency notion `E`, under the closure hypotheses the proof uses.

**Proof.** It suffices to prove `BPP ⊆ Σ₂ᵖ` (`bpp_subset_sigma2`) and
apply it to `Lᶜ` as well, since `BPP` is closed under complementation
(`InBPP.compl`, which is where the hypothesis `hNot` is used).  Given
`L ∈ BPP` with witness `(M₀, a₀, k₀)`, amplify by majority
(`amplify_concrete`, using `hMaj`) to error `2^{−T(n)}` with
`T(n) = (a₀+7)(n+1)^{k₀}`; the amplified verifier uses
`m(n) = (18(a₀+7)+18)·a₀·(n+1)^{2k₀}` random bits.  Take
`k(n) = (19a₀+20)(n+1)^{k₀}` shifts — a `polyLen` schedule, as the
`shiftOrVerifier` closure (`hShift`) requires.  The two counting claims
are balanced against `T` rather than the book's `n` (whose choice
`k = ⌈m/n⌉ + 1` needs `k < 2^n` and fails at small `n`):
(Claim 1) `k(n) < 2^{T(n)}` (`shift_count_lt_two_pow`), so for `x ∉ L`
the `k` translates of the accepting set, each of measure `≤ 2^{−T}`,
cannot cover `{0,1}^m`; a union bound exhibits an uncovered `v` for
every `u`.  (Claim 2) `m(n) < T(n)·k(n)`, so for `x ∈ L` the probability
that `k` random shifts miss some `v` is at most `2^m·2^{−Tk} < 1`
(the vote-count distribution `randProb_blockCount` at `j = 0` and the
XOR-invariance `randProb_xor_right`), and the probabilistic method
yields covering shifts.  Hence
`x ∈ L ↔ ∃ u₁,…,u_k ∀ v, ⋁ᵢ M(x, v ⊕ uᵢ)`, the `Σ₂`-shape
`shiftOrVerifier` expresses; all the lengths involved are `polyLen`
schedules. -/
theorem sipser_gacs (hMaj : ClosedUnderMajority E)
    (hNot : ClosedUnderNot E) (hShift : ClosedUnderShiftOr E)
    {L : Language Bool} (hL : InBPP E L) :
    InSigma2 E L ∧ InPi2 E L :=
  ⟨bpp_subset_sigma2 E hMaj hShift hL,
    bpp_subset_sigma2 E hMaj hShift (InBPP.compl E hNot hL)⟩

end Randomized
