/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Inclusions
import TCSlib.Complexity.Randomized.RandomBits

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomized reductions and BP·NP

Randomized polynomial-time reductions and the class `BP·NP` of [AB09, §7.6, p. 138];
`BP·NP ⊆ NP/poly` [AB09, Exercise 7.7] is in `TCSlib.Complexity.Randomized.NPPoly`.
Probabilities are exact counting ratios (`Randomized.randProb`); `BPP` is the certificate class
`Randomized.InBPP polyTimeModel`.

## Main definitions

* `Randomized.RandReducible` (notation `B ≤ᵣ C`) — [AB09, Def 7.16].
* `Randomized.BPNP` — `BP·NP = {L | L ≤ᵣ 3SAT}` [AB09, Def 7.17].
* `Randomized.InBPPAt` — `BPP` with success threshold `p`.

## Main results

* `Randomized.InBPP.of_randReducible` — `C ∈ BPP`, `B ≤ᵣ C` ⇒ `B ∈ BPP` [AB09, §7.6].
* `Randomized.RandReducible.of_polyTimeReducible` — `≤ₚ ⊆ ≤ᵣ`;
  `Randomized.RandReducible.of_polyTimeReducible_left` — `A ≤ₚ B ≤ᵣ C ⇒ A ≤ᵣ C`.
* `Randomized.NP_subset_BPNP` — `NP ⊆ BP·NP` [AB09, §7.6].
* `Randomized.InBPPAt.amplify` — majority amplification with a constant number of votes.

## Divergences

* **Certificate form of Def 7.16.** The book's probabilistic transducer `M` is a
  polynomial-time `f` on `pairEncode x r` with `r ∈ {0,1}^{polyLen a k |x|}`, as Def 7.3 does
  for `BPP`. The printed event `B(M(x)) = C(x)` has `B` and `C` swapped; we use
  `C(f(x, r)) = B(x)`, the reading under which the remark and Def 7.17 hold.
* **Transitivity** is not claimed: the book notes `≤ᵣ` is not transitive. Composition with a
  Karp reduction on either side is.
* `3SAT` is `Complexity.SAT3`, with that file's encoding conventions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity Turing

/-! ### `BPP` with an arbitrary success threshold -/

variable (E : VerifierModel)

/-- `L` is decided by an `E`-efficient verifier with success probability at least `p` on every
input; `InBPP E` is the case `p = 2/3`. [AB09, Def 7.3] -/
def InBPPAt (p : ℚ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → p ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → p ≤ randProb (polyLen a k x.length) fun r => M x r = false)

variable {E}

/-- Lowering the threshold keeps the same verifier. -/
theorem InBPPAt.mono {p p' : ℚ} {L : Language Bool} (h : InBPPAt E p L) (hp : p' ≤ p) :
    InBPPAt E p' L := by
  obtain ⟨M, a, k, hM, hL⟩ := h
  exact ⟨M, a, k, hM, fun x => ⟨fun hx => hp.trans ((hL x).1 hx),
    fun hx => hp.trans ((hL x).2 hx)⟩⟩

/-- `InBPP` is `InBPPAt` at threshold `2/3`. -/
theorem inBPP_iff_inBPPAt (L : Language Bool) : InBPP E L ↔ InBPPAt E (2/3) L := Iff.rfl

/-- **Constant-factor majority amplification**: a constant number `K` of independent runs
and a majority vote turn success probability `1/2 + ε` into `1 − η` whenever
`2(1 − 4ε²)^{⌊K/2⌋} ≤ η`. [AB09, Thm 7.10] (with a constant repetition count, from any
success `1/2 + ε`; `amplify_concrete` starts from success `2/3`)

**Proof sketch.** As `bpp_error_reduction`: the majority errs exactly when at least half of
the `K` blocks err, and each block errs with probability at most `1/2 − ε`, so the binomial
tail bound `randProb_tail_le` applies; the vote counts of a test and of its negation add up
to `K` (`blockCount_add_not`). -/
theorem InBPPAt.amplify (hMaj : ClosedUnderMajority E) (K : ℕ) {ε η : ℚ} (hε : 0 ≤ ε)
    (hK : 2 * (1 - 4 * ε ^ 2) ^ (K / 2) ≤ η) {L : Language Bool}
    (h : InBPPAt E (1/2 + ε) L) : InBPPAt E (1 - η) L := by
  classical
  obtain ⟨M, a, k, hM, hprop⟩ := h
  refine ⟨majorityVerifier M (polyLen a k) (polyLen K 0), K * a, k,
    hMaj M a k K 0 hM, fun x => ?_⟩
  set q := polyLen a k x.length with hq
  have hK0 : polyLen K 0 x.length = K := by simp [polyLen]
  have hlen : polyLen (K * a) k x.length = K * q := by
    simp only [hq, polyLen]
    ring
  have hmaj : ∀ l : List Bool,
      majorityVerifier M (polyLen a k) (polyLen K 0) x l = true ↔
        K < 2 * blockCount q K (M x) l := by
    intro l
    show decide (polyLen K 0 x.length < 2 * blockCount q (polyLen K 0 x.length) (M x) l) = true ↔ _
    rw [decide_eq_true_iff, hK0]
  have hs_not : randProb q (fun l => (!(M x l)) = true) =
      1 - randProb q (fun l => M x l = true) := by
    rw [← randProb_bool_false]
    exact randProb_congr fun r => by simp
  rw [hlen]
  constructor
  · intro hx
    have hW := (hprop x).1 hx
    have htail := randProb_tail_le q K (fun l' => !(M x l')) hε (by rw [hs_not]; linarith)
    have hev : randProb (K * q)
        (fun l => ¬ (majorityVerifier M (polyLen a k) (polyLen K 0) x l = true)) =
        randProb (K * q) (fun l => K ≤ 2 * blockCount q K (fun l' => !(M x l')) l) :=
      randProb_congr fun r => by
        rw [hmaj]
        have := blockCount_add_not q K (M x) (List.ofFn r)
        omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M (polyLen a k) (polyLen K 0) x l = true)
    rw [hev] at hnot
    linarith
  · intro hx
    have hW := (hprop x).2 hx
    have hst : randProb q (fun l => M x l = true) ≤ 1/2 - ε := by
      have := randProb_bool_false (m := q) (M x)
      linarith
    have htail := randProb_tail_le q K (M x) hε hst
    have hmono : randProb (K * q)
        (fun l => ¬ (majorityVerifier M (polyLen a k) (polyLen K 0) x l = false)) ≤
        randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M x) l) := by
      refine randProb_mono fun r hr => ?_
      have h1 : majorityVerifier M (polyLen a k) (polyLen K 0) x (List.ofFn r) = true := by
        simpa using hr
      have := (hmaj _).mp h1
      omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M (polyLen a k) (polyLen K 0) x l = false)
    linarith

/-- A `BPP` language has an efficient verifier erring with probability at most `1/24` on
every input (via `amplify_concrete`, error `2^{-5}`). -/
theorem InBPP.inBPPAt_23_24 (hMaj : ClosedUnderMajority E) {L : Language Bool}
    (h : InBPP E L) : InBPPAt E (23/24) L := by
  obtain ⟨M₀, a₀, k₀, hM₀, hprop₀⟩ := h
  obtain ⟨M, hM, hprop⟩ := amplify_concrete E hMaj hM₀ hprop₀ 5 0
  have hth : ∀ n, (23/24 : ℚ) ≤ 1 - (1/2) ^ polyLen 5 0 n := fun n => by
    simp only [polyLen, pow_zero, mul_one]
    norm_num
  exact ⟨M, _, _, hM, fun x => ⟨fun hx => (hth _).trans ((hprop x).1 hx),
    fun hx => (hth _).trans ((hprop x).2 hx)⟩⟩

/-- Success probability `5/8` suffices for `BPP` (`60` majority votes). -/
theorem InBPPAt.inBPP_of_5_8 (hMaj : ClosedUnderMajority E) {L : Language Bool}
    (h : InBPPAt E (5/8) L) : InBPP E L := by
  have h' : InBPPAt E (1/2 + 1/8) L := h.mono (by norm_num)
  exact (h'.amplify hMaj 60 (by norm_num) (η := 1/3) (by norm_num)).mono (by norm_num)

/-! ### Randomized reductions -/

open Classical in
/-- **Randomized reduction** `B ≤ᵣ C` [AB09, Def 7.16]: a polynomial-time computable `f`,
run on the input `x` paired with a random string `r` of length `polyLen a k |x|`, satisfies
`Pr_r[f(x, r) ∈ C ↔ x ∈ B] ≥ 2/3`. -/
def RandReducible (B C : Language Bool) : Prop :=
  ∃ (f : List Bool → List Bool) (a k : ℕ), PolyTimeComputable f ∧
    ∀ x : List Bool,
      2/3 ≤ randProb (polyLen a k x.length) fun r => (f (Turing.pairEncode x r) ∈ C ↔ x ∈ B)

@[inherit_doc] scoped infix:50 " ≤ᵣ " => RandReducible

/-- A Karp reduction is a randomized reduction that ignores its coins. [AB09, §7.6] -/
theorem RandReducible.of_polyTimeReducible {B C : Language Bool} (h : B ≤ₚ C) : B ≤ᵣ C := by
  classical
  obtain ⟨f, hf, hfB⟩ := h
  refine ⟨fun z => f (pairFstD z), 0, 0, hf.comp polyTimeComputable_pairFstD, fun x => ?_⟩
  rw [randProb_congr (B := fun _ => True) fun r => by simp [hfB x], randProb_true]
  norm_num

/-- A Karp reduction followed by a randomized reduction is a randomized reduction:
`A ≤ₚ B` and `B ≤ᵣ C` give `A ≤ᵣ C`.

**Proof sketch.** Run the randomized reduction on `g x` with the first
`polyLen a k |g x|` coins; that length is bounded by a schedule in `|x|` because `|g x|` is
polynomial in `|x|`, and surplus coins are ignored (`randProb_take`). -/
theorem RandReducible.of_polyTimeReducible_left {A B C : Language Bool} (h₁ : A ≤ₚ B)
    (h₂ : B ≤ᵣ C) : A ≤ᵣ C := by
  classical
  obtain ⟨g, hg, hgA⟩ := h₁
  obtain ⟨f, a, k, hf, hprob⟩ := h₂
  obtain ⟨Cg, cg, hCg⟩ := hg.output_length_le
  refine ⟨fun z => f (sliceTake a k (Turing.pairEncode (g (pairFstD z)) (pairSndD z))),
    a * (Cg + 1) ^ k, cg * k, hf.comp ((polyTimeComputable_sliceTake a k).comp
      ((hg.comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)),
    fun x => ?_⟩
  have hle : polyLen a k (g x).length ≤ polyLen (a * (Cg + 1) ^ k) (cg * k) x.length := by
    have hp : 1 ≤ (x.length + 1) ^ cg := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have h1 : (g x).length + 1 ≤ (Cg + 1) * (x.length + 1) ^ cg := by
      nlinarith [hCg x]
    calc polyLen a k (g x).length = a * ((g x).length + 1) ^ k := rfl
      _ ≤ a * ((Cg + 1) * (x.length + 1) ^ cg) ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 k)
      _ = polyLen (a * (Cg + 1) ^ k) (cg * k) x.length := by
          unfold polyLen
          rw [mul_pow, ← pow_mul]
          ring
  have key := randProb_take hle (fun s => (f (Turing.pairEncode (g x) s) ∈ C ↔ g x ∈ B))
  refine (hprob (g x)).trans (le_of_eq ?_)
  rw [← key]
  exact randProb_congr fun r => by
    simp [sliceTake, hgA x]

/-- The composite of the reduction's first stage and a second-stage slice: on
`pairEncode x t` it is `pairEncode y (t'.take (polyLen a₂ k₂ |y|))`, where `t'` drops the first
`polyLen a₁ k₁ |x|` bits of `t` and `y = f (pairEncode x (t.take (polyLen a₁ k₁ |x|)))`. -/
def composeMap (a₁ k₁ a₂ k₂ : ℕ) (f : List Bool → List Bool) (z : List Bool) : List Bool :=
  sliceTake a₂ k₂ (Turing.pairEncode (f (sliceTake a₁ k₁ z)) (pairSndD (sliceDrop a₁ k₁ z)))

/-- `composeMap` on a pair, unfolded. -/
theorem composeMap_pairEncode (a₁ k₁ a₂ k₂ : ℕ) (f : List Bool → List Bool) (x t : List Bool) :
    composeMap a₁ k₁ a₂ k₂ f (Turing.pairEncode x t) =
      Turing.pairEncode (f (Turing.pairEncode x (t.take (polyLen a₁ k₁ x.length))))
        ((t.drop (polyLen a₁ k₁ x.length)).take (polyLen a₂ k₂
          (f (Turing.pairEncode x (t.take (polyLen a₁ k₁ x.length)))).length)) := by
  simp [composeMap, sliceTake, sliceDrop]

/-- `composeMap` is polynomial-time computable when `f` is. -/
theorem polyTimeComputable_composeMap (a₁ k₁ a₂ k₂ : ℕ) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) : PolyTimeComputable (composeMap a₁ k₁ a₂ k₂ f) :=
  (polyTimeComputable_sliceTake a₂ k₂).comp
    ((hf.comp (polyTimeComputable_sliceTake a₁ k₁)).pairEncode
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_sliceDrop a₁ k₁)))

/-- A polynomial schedule evaluated at the output length of a polynomially bounded `f` on
`pairEncode x r`, with `|r| = polyLen a₁ k₁ |x|`, is bounded by a schedule in `|x|`.

**Proof sketch.** `|pairEncode x r| + 1 = 2|x| + 3 + a₁(|x|+1)^{k₁} ≤ (a₁+3)(|x|+1)^{k₁+1}`;
feed this through the output bound of `f` and then through `polyLen a₂ k₂`. -/
theorem polyLen_length_pairEncode_le {f : List Bool → List Bool} {C c : ℕ}
    (hC : ∀ z, (f z).length ≤ C * (z.length + 1) ^ c) (a₁ k₁ a₂ k₂ : ℕ) {x r : List Bool}
    (hr : r.length = polyLen a₁ k₁ x.length) :
    polyLen a₂ k₂ (f (Turing.pairEncode x r)).length ≤
      polyLen (a₂ * ((C + 1) * (a₁ + 3) ^ c) ^ k₂) ((k₁ + 1) * c * k₂) x.length := by
  set n := x.length
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hP : (Turing.pairEncode x r).length + 1 ≤ (a₁ + 3) * (n + 1) ^ (k₁ + 1) := by
    rw [length_pairEncode, hr]
    have h1 : n + 1 ≤ (n + 1) ^ (k₁ + 1) := Nat.le_self_pow (Nat.succ_ne_zero k₁) _
    have h2 : (n + 1) ^ k₁ ≤ (n + 1) ^ (k₁ + 1) := Nat.pow_le_pow_right hN (Nat.le_succ k₁)
    unfold polyLen
    nlinarith [Nat.mul_le_mul_left a₁ h2]
  have hf1 : (f (Turing.pairEncode x r)).length + 1 ≤
      (C + 1) * (a₁ + 3) ^ c * (n + 1) ^ ((k₁ + 1) * c) := by
    have hpos : 1 ≤ ((Turing.pairEncode x r).length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
    calc (f (Turing.pairEncode x r)).length + 1
        ≤ C * ((Turing.pairEncode x r).length + 1) ^ c +
            ((Turing.pairEncode x r).length + 1) ^ c := Nat.add_le_add (hC _) hpos
      _ = (C + 1) * ((Turing.pairEncode x r).length + 1) ^ c := by ring
      _ ≤ (C + 1) * ((a₁ + 3) * (n + 1) ^ (k₁ + 1)) ^ c :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP c)
      _ = (C + 1) * (a₁ + 3) ^ c * (n + 1) ^ ((k₁ + 1) * c) := by
          rw [mul_pow, ← pow_mul]
          ring
  calc polyLen a₂ k₂ (f (Turing.pairEncode x r)).length
      = a₂ * ((f (Turing.pairEncode x r)).length + 1) ^ k₂ := rfl
    _ ≤ a₂ * ((C + 1) * (a₁ + 3) ^ c * (n + 1) ^ ((k₁ + 1) * c)) ^ k₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hf1 k₂)
    _ = polyLen (a₂ * ((C + 1) * (a₁ + 3) ^ c) ^ k₂) ((k₁ + 1) * c * k₂) n := by
        unfold polyLen
        rw [mul_pow, ← pow_mul]
        ring

/-- **`BPP` is closed under randomized reductions** [AB09, §7.6, remark after Def 7.16]: if
`C ∈ BPP` and `B ≤ᵣ C` then `B ∈ BPP` (certificate form over `polyTimeModel`).

**Proof sketch.** Composing the reduction (success `2/3`) with a `2/3`-verifier for `C`
could leave success only `4/9`, so first amplify the verifier for `C` to error `1/24`
(`InBPP.inBPPAt_23_24`). Run the reduction on the first `polyLen a₁ k₁ |x|` coins and the
amplified verifier on `y = f(x, r₁)` with the next coins; the coin length for `y` is bounded
by a schedule in `|x|` (`polyLen_length_pairEncode_le`), and surplus coins are ignored
(`randProb_take`). Conditioning on the first segment (`randProb_append_ge`), the composite
is correct with probability at least `2/3 · 23/24 > 5/8`, and a constant majority vote
(`InBPPAt.inBPP_of_5_8`) restores `2/3`. The composite is polynomial-time because its answer
sets are preimages of the verifier's under `composeMap`. -/
theorem InBPP.of_randReducible {B C : Language Bool} (hred : B ≤ᵣ C)
    (hC : InBPP polyTimeModel C) : InBPP polyTimeModel B := by
  classical
  obtain ⟨f, a₁, k₁, hf, hprob⟩ := hred
  obtain ⟨Cf, cf, hCf⟩ := hf.output_length_le
  obtain ⟨M, a₂, k₂, ⟨V₁, V₀, hV₁, hV₀, hM⟩, hMC⟩ :=
    hC.inBPPAt_23_24 polyTimeModel_closedUnderMajority
  set A := a₂ * ((Cf + 1) * (a₁ + 3) ^ cf) ^ k₂
  set K := (k₁ + 1) * cf * k₂
  -- the composite verifier
  let V : List Bool → List Bool → Bool := fun x t =>
    M (f (Turing.pairEncode x (t.take (polyLen a₁ k₁ x.length))))
      ((t.drop (polyLen a₁ k₁ x.length)).take (polyLen a₂ k₂
        (f (Turing.pairEncode x (t.take (polyLen a₁ k₁ x.length)))).length))
  have hEff : polyTimeModel.Eff (boolVerifier V) := by
    refine ⟨composeMap a₁ k₁ a₂ k₂ f ⁻¹' V₁, composeMap a₁ k₁ a₂ k₂ f ⁻¹' V₀,
      preimage_mem_P hV₁ (polyTimeComputable_composeMap _ _ _ _ hf),
      preimage_mem_P hV₀ (polyTimeComputable_composeMap _ _ _ _ hf), fun x t => ?_⟩
    show (_ ↔ composeMap a₁ k₁ a₂ k₂ f (Turing.pairEncode x t) ∈ V₁) ∧
      (_ ↔ composeMap a₁ k₁ a₂ k₂ f (Turing.pairEncode x t) ∈ V₀)
    rw [composeMap_pairEncode]
    exact hM _ _
  refine InBPPAt.inBPP_of_5_8 polyTimeModel_closedUnderMajority
    ⟨V, a₁ + A, k₁ + K, hEff, fun x => ?_⟩
  set n := x.length
  set q := polyLen a₁ k₁ n
  have hq : q + polyLen A K n ≤ polyLen (a₁ + A) (k₁ + K) n := by
    have h1 : (n + 1) ^ k₁ ≤ (n + 1) ^ (k₁ + K) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    have h2 : (n + 1) ^ K ≤ (n + 1) ^ (k₁ + K) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    simp only [q, polyLen]
    nlinarith [Nat.mul_le_mul_left a₁ h1, Nat.mul_le_mul_left A h2]
  obtain ⟨m₂, hm₂⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right q _) hq)
  have hm₂' : polyLen A K n ≤ m₂ := by omega
  -- the second-stage coin length fits in the second segment
  have hfit : ∀ u : Fin q → Bool,
      polyLen a₂ k₂ (f (Turing.pairEncode x (List.ofFn u))).length ≤ m₂ := fun u =>
    (polyLen_length_pairEncode_le hCf a₁ k₁ a₂ k₂ (by simp [q, n])).trans hm₂'
  -- one bound for both answers
  have key : ∀ b : Bool, (∀ y, (y ∈ C ↔ x ∈ B) →
      23/24 ≤ randProb (polyLen a₂ k₂ y.length) fun s => M y s = b) →
      5/8 ≤ randProb (polyLen (a₁ + A) (k₁ + K) n) fun t => V x t = b := by
    intro b hb
    rw [hm₂]
    have hA : 2/3 ≤ randProb q (fun r => (f (Turing.pairEncode x r) ∈ C ↔ x ∈ B)) :=
      (hprob x).trans_eq (randProb_congr fun _ => Iff.rfl)
    have hlow := randProb_append_ge q m₂
      (fun r => (f (Turing.pairEncode x r) ∈ C ↔ x ∈ B))
      (fun r s => M (f (Turing.pairEncode x r))
        (s.take (polyLen a₂ k₂ (f (Turing.pairEncode x r)).length)) = b)
      (ε := 23/24) (fun u hu => by
        refine le_of_le_of_eq (hb _ hu) ?_
        exact (randProb_take (hfit u)
          (fun s => M (f (Turing.pairEncode x (List.ofFn u))) s = b)).symm)
    have heq : randProb (q + m₂) (fun t => V x t = b) =
        randProb (q + m₂) (fun t => M (f (Turing.pairEncode x (t.take q)))
          ((t.drop q).take (polyLen a₂ k₂ (f (Turing.pairEncode x (t.take q))).length)) = b) :=
      randProb_congr fun _ => Iff.rfl
    rw [heq]
    nlinarith
  refine ⟨fun hx => key true fun y hy => (hMC y).1 (hy.mpr hx),
    fun hx => key false fun y hy => (hMC y).2 fun hyC => hx (hy.mp hyC)⟩

/-! ### `BP·NP` -/

/-- **`BP·NP`** [AB09, Def 7.17]: the languages randomly reducible to `3SAT`. -/
def BPNP : Set (Language Bool) :=
  {L | L ≤ᵣ SAT3}

/-- **`NP ⊆ BP·NP`**: a Karp reduction to `3SAT` (Cook–Levin) is a randomized one.
[AB09, §7.6] -/
theorem NP_subset_BPNP : NP ⊆ BPNP :=
  fun L hL => RandReducible.of_polyTimeReducible (SAT3_NPHard L hL)

end Randomized
