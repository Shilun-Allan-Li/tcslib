/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.UPathLoops
import TCSlib.Complexity.Randomized.RandomWalkPad

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The random walk of the machine for `UPATH`

[AB09, Theorem 7.19]: "take a random walk of length `100n⁴` starting from `s` … accept iff
the walk reaches `t`". The walk loop of `Complexity.LogProg.upA` is the walk on the padded
graph `Randomized.padGraph` of the input's edge relation: a step reads `size n` coins into
`i < 2^{size n} = padDegree n` and moves along slot `i` (`Randomized.padNbr`). Its acceptance
probability is exactly the hitting probability `Randomized.RegularMultigraph.hitProb`
(`Complexity.LogProg.ups_walk`): both satisfy the one-step recursion
`Randomized.RegularMultigraph.hitProb_succ`, the coin loop averaging over the `2^{size n}`
indices (`Complexity.LogProg.ups_coin`).

## Main definitions

* `Complexity.upGraph` — the padded graph of the input's edge relation.

## Main results

* `Complexity.LogProg.ups_len` — the computation of `L = 100 n⁴`.
* `Complexity.LogProg.ups_coin` — `size n` coins give a uniform index.
* `Complexity.LogProg.ups_lt` — the comparison `i < n`.
* `Complexity.LogProg.ups_walk` — the walk accepts with the hitting probability.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7, Theorem 7.19; Exercise 7.11.)
-/

namespace Complexity

/-- The padded graph of the input's edge relation on `Fin n`, of degree `padDegree n`
[AB09, Exercise 7.11(e)]. -/
def upGraph (x : List Bool) {n : ℕ} (h : SymRest x n) :
    Randomized.RegularMultigraph (Fin n) (Randomized.padDegree n) :=
  Randomized.padGraph (inEdge x n) (symmetric_inEdge h) _ (Randomized.le_padDegree n)

namespace LogProg

open Turing ULabel UPathTac Randomized

variable {x : List Bool} {B : ℕ}

/-- **The length computation**: from `e = f = L = 0`, the machine reaches the walk with
`e = 10 n`, `f = n · 10 n` and `L = f · f = 100 n⁴`.

**Proof sketch.** Five add-twice loops add `2n` to `e` each (`ups_ad`); then the two
multiplications (`ups_mul`). -/
lemma ups_len (q : ℚ) (σ : UReg) (hσ : σ.Le B) (he : σ.e = 0) (hf : σ.f = 0) (hL : σ.L = 0)
    (hBn : 100 * σ.n ^ 4 + 10 * σ.n ≤ B)
    (hK : ∀ a b, a ≤ B → b ≤ B → UPS x B w0 { σ with
      e := 10 * σ.n, f := σ.n * (10 * σ.n),
      L := σ.n * (10 * σ.n) * (σ.n * (10 * σ.n)), a := a, b := b } q) :
    UPS x B (lc 0) σ q := by
  have hn4 : σ.n * (10 * σ.n) * (σ.n * (10 * σ.n)) = 100 * σ.n ^ 4 := by ring
  have hn2 : σ.n * (10 * σ.n) ≤ 100 * σ.n ^ 4 + 10 * σ.n := by
    rcases Nat.eq_zero_or_pos σ.n with h | h
    · simp [h]
    · nlinarith [Nat.one_le_pow 2 σ.n h]
  have e0 : adEx (.ten 0) = lc 1 := rfl
  have e1 : adEx (.ten 1) = lc 2 := rfl
  have e2 : adEx (.ten 2) = lc 3 := rfl
  have e3 : adEx (.ten 3) = lc 4 := rfl
  have e4 : adEx (.ten 4) = mc .m0 := rfl
  refine PSem.clr rfl (UReg.reg hσ _ _) ?_
  uw_regs
  refine ups_ad (.ten 0) q _ (by uw_le) (by simp [adY]) (by simp [adY, adP]; omega) ?_
  simp only [adY, adP, e0]
  uw_regs
  refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  refine ups_ad (.ten 1) q _ (by uw_le) (by simp [adY]) (by simp [adY, adP]; omega) ?_
  simp only [adY, adP, e1]
  uw_regs
  refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  refine ups_ad (.ten 2) q _ (by uw_le) (by simp [adY]) (by simp [adY, adP]; omega) ?_
  simp only [adY, adP, e2]
  uw_regs
  refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  refine ups_ad (.ten 3) q _ (by uw_le) (by simp [adY]) (by simp [adY, adP]; omega) ?_
  simp only [adY, adP, e3]
  uw_regs
  refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  refine ups_ad (.ten 4) q _ (by uw_le) (by simp [adY]) (by simp [adY, adP]; omega) ?_
  simp only [adY, adP, e4]
  uw_regs
  refine UPS.of_eq (σ' := { σ with e := 10 * σ.n, b := σ.n }) (by uw_ext) ?_
  refine ups_mul .m0 q _ (by uw_le) (by
    simp only [mulA, mulB, mulR, UReg.v_1, UReg.v_13, UReg.v_14]; omega) fun z hz => ?_
  simp only [mulA, mulB, mulR, mulEx]
  uw_regs
  refine UPS.of_eq
    (σ' := { σ with e := 10 * σ.n, b := z, a := σ.n, f := σ.n * (10 * σ.n) }) (by uw_ext) ?_
  refine ups_mul .m1 q _ (by uw_le) (by
    simp only [mulA, mulB, mulR, UReg.v_10, UReg.v_14]; rw [hn4]; omega) fun z' hz' => ?_
  simp only [mulA, mulB, mulR, mulEx]
  uw_regs
  exact UPS.of_eq (by uw_ext) (hK (σ.n * (10 * σ.n)) z' (by omega) hz')

/-- The bits of a positive number are one more than the bits of its half. -/
private lemma size_eq_succ {τ : ℕ} (h : τ ≠ 0) : Nat.size τ = Nat.size (τ / 2) + 1 := by
  rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len, bits_eq_cons h, List.length_cons]

/-- **The coin loop**: from the index `i₀` and a copy `τ` of `n`, the machine halves `τ` until
`0`, setting `i := 2 i + coin` each time; the probability is the average over the
`2^{size τ}` final indices `i₀ · 2^{size τ} + j` of the continuation's probability.

**Proof sketch.** Strong induction on `τ`. At `τ = 0` the loop exits. Otherwise the step
doubles `i` (an add-twice loop and a copy), and the `choose` averages the continuations from
`2 i₀` and `2 i₀ + 1`, whose `2^{size (τ/2)}` final indices are the two halves of the
`2^{size τ}` final indices of `i₀` (`Finset.sum_range_add`). -/
lemma ups_coin (F : ℕ → ℚ) : ∀ τ (σ : UReg), σ.tmp = τ → σ.Le B →
    2 * ((σ.nx + 1) * 2 ^ Nat.size τ) ≤ B →
    (∀ i, σ.nx * 2 ^ Nat.size τ ≤ i → i < (σ.nx + 1) * 2 ^ Nat.size τ → ∀ b e, b ≤ B →
      e ≤ B → UPS x B lt { σ with nx := i, tmp := 0, b := b, e := e } (F i)) →
    UPS x B c0 σ
      ((∑ j ∈ Finset.range (2 ^ Nat.size τ), F (σ.nx * 2 ^ Nat.size τ + j)) /
        2 ^ Nat.size τ) := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
  intro σ hτ hσ hb hK
  rcases Nat.eq_zero_or_pos τ with rfl | hpos
  · refine PSem.jz_pos rfl (UReg.reg hσ _ _) (by simpa using hτ) ?_
    refine (UPS.of_eq (by uw_ext) (hK σ.nx (by simp) (by simp) σ.b σ.e (by uw_le)
      (by uw_le))).congr (by simp)
  · have hs := size_eq_succ (Nat.pos_iff_ne_zero.mp hpos)
    set s := Nat.size (τ / 2) with hs'
    rw [hs] at hb hK ⊢
    have hp2 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
    have hb' : 2 * ((2 * σ.nx + 1 + 1) * 2 ^ s) ≤ B := by
      have : (2 * σ.nx + 1 + 1) * 2 ^ s = (σ.nx + 1) * 2 ^ (s + 1) := by ring
      omega
    have hnx : 2 * σ.nx + 2 ≤ B := by
      have h2 : 2 ≤ 2 ^ (s + 1) := by
        have := Nat.one_le_two_pow (n := s); rw [pow_succ]; omega
      have : (σ.nx + 1) * 2 ≤ (σ.nx + 1) * 2 ^ (s + 1) := Nat.mul_le_mul_left _ h2
      omega
    refine PSem.jz_neg rfl (UReg.reg hσ _ _) (by simp only [UReg.v_6]; omega) ?_
    refine PSem.clr rfl (UReg.reg hσ _ _) ?_
    uw_regs
    refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
    uw_regs
    refine ups_ad .dbl _ _ (by uw_le) (by simp [adY]) (by simp [adY, adP]; omega) ?_
    simp only [adY, adP, adEx]
    uw_regs
    refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
    uw_regs
    refine ups_cp .wNx _ _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
    simp only [cpDst, cpSrc, cpEx]
    uw_regs
    -- the two continuations after the coin
    have hc : ∀ c : ℕ, c ≤ 1 → UPS x B c6
        { σ with e := 0 + 2 * (σ.nx - 0), b := σ.nx, nx := 2 * σ.nx + c }
        ((∑ j ∈ Finset.range (2 ^ s), F ((2 * σ.nx + c) * 2 ^ s + j)) / 2 ^ s) := by
      intro c hc1
      have hcs : (2 * σ.nx + c + 1) * 2 ^ s ≤ (2 * σ.nx + 1 + 1) * 2 ^ s :=
        Nat.mul_le_mul_right _ (by omega)
      refine PSem.half rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      have := ih (τ / 2) (by omega) { σ with
        e := 0 + 2 * (σ.nx - 0), b := σ.nx,
        nx := 2 * σ.nx + c, tmp := τ / 2 } rfl (by uw_le)
        (by change 2 * ((2 * σ.nx + c + 1) * 2 ^ s) ≤ B; omega)
        (fun i h1 h2 b e hb he => UPS.of_eq (by uw_ext) (hK i ?_ ?_ b e hb he))
      · exact UPS.of_eq (by uw_ext) this
      · change (2 * σ.nx + c) * 2 ^ s ≤ i at h1; rw [pow_succ]; nlinarith
      · change i < (2 * σ.nx + c + 1) * 2 ^ s at h2; rw [pow_succ]; nlinarith
    have h1 := hc 1 le_rfl
    have h0 := hc 0 (Nat.zero_le _)
    have h1' : UPS x B c5 { σ with e := 2 * σ.nx, b := σ.nx, nx := 2 * σ.nx }
        ((∑ j ∈ Finset.range (2 ^ s), F ((2 * σ.nx + 1) * 2 ^ s + j)) / 2 ^ s) := by
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      exact UPS.of_eq (by uw_ext) h1
    refine UPS.of_eq (σ' := { σ with e := 2 * σ.nx, b := σ.nx, nx := 2 * σ.nx }) (by uw_ext) ?_
    refine (PSem.choose (A := upA) rfl (UReg.reg (by uw_le) _ _) h1'
      (UPS.of_eq (by uw_ext) h0)).congr ?_
    · rw [hp2, Finset.sum_range_add, pow_succ]
      have ea : ∀ j, F ((2 * σ.nx + 0) * 2 ^ s + j) = F (σ.nx * (2 ^ s + 2 ^ s) + j) :=
        fun j => by congr 1; ring
      have eb : ∀ j, F ((2 * σ.nx + 1) * 2 ^ s + j) =
          F (σ.nx * (2 ^ s + 2 ^ s) + (2 ^ s + j)) := fun j => by congr 1; ring
      simp only [ea, eb]
      field_simp
      ring

/-- **The comparison `i < n`**: counting `a` up from `0`, the machine meets `n` first iff
`n ≤ i`; it continues with the index computation if `i < n` and with the step count
otherwise.

**Proof sketch.** Induction on `n - a` with `a ≤ min(i, n)`: `a = n` exits to the step
count, `a = i` to the index computation, otherwise `a` is incremented. -/
lemma ups_lt (q : ℚ) (σ : UReg) (hσ : σ.Le B)
    (h1 : σ.nx < σ.n → ∀ a, a ≤ B → UPS x B (ix0 .w) { σ with a := a } q)
    (h0 : σ.n ≤ σ.nx → ∀ a, a ≤ B → UPS x B stay { σ with a := a } q) :
    UPS x B lt σ q := by
  refine PSem.clr rfl (UReg.reg hσ _ _) ?_
  uw_regs
  suffices H : ∀ dd a, σ.n - a = dd → a ≤ σ.n → a ≤ σ.nx → UPS x B lt0 { σ with a := a } q from
    H _ 0 rfl (Nat.zero_le _) (Nat.zero_le _)
  intro dd
  induction dd with
  | zero =>
    intro a hd ha han
    have he : a = σ.n := by omega
    exact PSem.jeq_pos rfl (UReg.reg (by uw_le) _ _) (by simpa using he)
      (h0 (by omega) a (by uw_le))
  | succ dd ih =>
    intro a hd ha han
    refine PSem.jeq_neg rfl (UReg.reg (by uw_le) _ _) (by simp; omega) ?_
    by_cases he : a = σ.nx
    · exact PSem.jeq_pos rfl (UReg.reg (by uw_le) _ _) (by simpa using he)
        (h1 (by omega) a (by uw_le))
    · refine PSem.jeq_neg rfl (UReg.reg (by uw_le) _ _) (by simpa using he) ?_
      refine PSem.inc rfl (UReg.reg (by uw_le) _ _) ?_
      uw_regs
      exact UPS.of_eq (by uw_ext) (ih (a + 1) (by omega) (by omega) (by omega))

/-- The coin loop's average over `2^{size n}` indices is the walk's average over the slots of
the padded graph. -/
private lemma sum_slots {n : ℕ} (G : RegularMultigraph (Fin n) (padDegree n)) (f : Fin n → ℚ)
    (v : Fin n) :
    (∑ j ∈ Finset.range (2 ^ Nat.size n),
        (if h : j < padDegree n then f (G.nbr v ⟨j, h⟩) else 0)) / 2 ^ Nat.size n =
      (∑ i, f (G.nbr v i)) / (padDegree n : ℚ) := by
  have hD : (padDegree n : ℚ) = 2 ^ Nat.size n := by simp [padDegree]
  rw [hD, ← Fin.sum_univ_eq_sum_range (fun j => if h : j < padDegree n then
    f (G.nbr v ⟨j, h⟩) else 0) (2 ^ Nat.size n)]
  congr 1
  show ∑ i : Fin (2 ^ Nat.size n), _ = ∑ i : Fin (padDegree n), _
  exact Finset.sum_congr rfl fun i _ => by simp [padDegree, i.isLt]

/-- **The walk** [AB09, Theorem 7.19]: at the walk head with current vertex `v`, target
`t` and `k = L - st` steps left, the machine accepts with probability the `k`-step hitting
probability of `t` from `v` in the padded graph.

**Proof sketch.** Induction on `k`, along `hitProb_succ`. At `v = t` the machine accepts
(probability `1`); at `k = 0` it rejects otherwise. Else it copies `n`, draws an index `i`
with `size n` coins (`ups_coin`, an average over the `2^{size n} = padDegree n` slots,
`sum_slots`), and moves along slot `i`: if `i < n` (`ups_lt`) it reads the matrix bit of
`(v, i)` (`ups_index`) and moves to `i` on a `1`, otherwise it stays — exactly
`padNbr v i`; by induction the rest accepts with probability `hitProb t k (padNbr v i)`. -/
theorem ups_walk {n : ℕ} (hsym : SymRest x n) (tt : Fin n) (hBx : 2 * x.length + 2 ≤ B)
    (hm : 2 * n + 2 + 2 * (n * n) ≤ x.length) :
    ∀ k (σ : UReg) (v : Fin n), σ.L - σ.st = k → σ.Le B → σ.n = n → (σ.cur : ℕ) = v →
      σ.t = tt → σ.st ≤ σ.L →
      UPS x B w0 σ ((upGraph x hsym).hitProb tt k v) := by
  have hn2 : 2 * (1 * 2 ^ Nat.size n) ≤ B := by
    have h := padDegree_le (n := n)
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp; omega
    · have := h h0; simp only [padDegree] at this; omega
  intro k
  induction k with
  | zero =>
    intro σ v hk hσ hn hv ht hst
    rw [RegularMultigraph.hitProb_zero]
    by_cases hvt : v = tt
    · refine (PSem.jeq_pos rfl (UReg.reg hσ _ _) (by simp [hv, ht, hvt])
        (PSem.acc rfl (UReg.reg hσ _ _))).congr (by simp [hvt])
    · refine PSem.jeq_neg rfl (UReg.reg hσ _ _) (by simp [hv, ht]; omega) ?_
      exact (PSem.jeq_pos rfl (UReg.reg hσ _ _) (by simp; omega)
        (PSem.rej rfl (UReg.reg hσ _ _))).congr (by simp [hvt])
  | succ k ih =>
    intro σ v hk hσ hn hv ht hst
    rw [RegularMultigraph.hitProb_succ]
    by_cases hvt : v = tt
    · refine (PSem.jeq_pos rfl (UReg.reg hσ _ _) (by simp [hv, ht, hvt])
        (PSem.acc rfl (UReg.reg hσ _ _))).congr (by simp [hvt])
    rw [if_neg hvt]
    refine PSem.jeq_neg rfl (UReg.reg hσ _ _) (by simp [hv, ht]; omega) ?_
    refine PSem.jeq_neg rfl (UReg.reg hσ _ _) (by simp; omega) ?_
    refine PSem.clr rfl (UReg.reg hσ _ _) ?_
    uw_regs
    refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
    uw_regs
    refine ups_cp .wTmp _ _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
    simp only [cpDst, cpSrc, cpEx]
    uw_regs
    set F : ℕ → ℚ := fun j => if h : j < padDegree n then (upGraph x hsym).hitProb tt k
      ((upGraph x hsym).nbr v ⟨j, h⟩) else 0 with hF
    -- the step from slot `j`, then the rest of the walk
    have hstep : ∀ (j : ℕ) (hj : j < 2 ^ Nat.size n) (b e : ℕ), b ≤ B → e ≤ B →
        UPS x B lt { σ with tmp := 0, nx := j, b := b, e := e } (F j) := by
      intro j hj b e hb he
      have hjD : j < padDegree n := hj
      simp only [hF, dif_pos hjD]
      -- the rest of the walk from `w`, after counting the step
      have hrest : ∀ (w : Fin n) (σ' : UReg), σ'.Le B → σ'.n = n → (σ'.cur : ℕ) = w →
          σ'.t = tt → σ'.L = σ.L → σ'.st = σ.st → UPS x B stay σ'
            ((upGraph x hsym).hitProb tt k w) := by
        intro w σ' hσ' hn' hw' ht' hL' hst'
        refine PSem.inc rfl (UReg.reg hσ' _ _) ?_
        uw_regs
        exact ih _ w (by dsimp only; omega) (by uw_le) hn' hw' ht' (by dsimp only; omega)
      have hnbr : (upGraph x hsym).nbr v ⟨j, hjD⟩ = padNbr (inEdge x n) v ⟨j, hjD⟩ := rfl
      rw [hnbr]
      have hvn : (v : ℕ) < n := v.isLt
      have hm' : 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ x.length := by rw [hn]; exact hm
      refine ups_lt _ _ (by uw_le) (fun hjn a ha => ?_) (fun hjn a ha => ?_)
      · simp only at hjn
        have hidx : σ.cur * σ.n + j < σ.n * σ.n := rowMajor_lt (by omega) hjn
        have hpad : ∀ c : Bool, (c = true ↔ inEdge x n v ⟨j, by omega⟩) →
            padNbr (inEdge x n) v ⟨j, hjD⟩ = if c then ⟨j, by omega⟩ else v := by
          intro c hc
          unfold padNbr
          simp only [show j < n by omega, dif_pos]
          cases c <;> simp_all
        refine ups_index .w _ _ (by uw_le) (by simp [ixRow, hn, hv])
          (by simpa [ixCol, hn] using hjn) (by simp only; rw [hn]; omega) ?_
        simp only [ixRow, ixCol, ixEx, UReg.v_4, UReg.v_8]
        by_cases hedge : inEdge x n v ⟨j, by omega⟩
        · refine PSem.call_pos rfl (UReg.reg (by uw_le) _ _)
            (by simp only [UReg.v_0, pathOr_bit, hn, hv]; exact hedge) ?_
          refine PSem.clr rfl (UReg.reg (by uw_le) _ _) ?_
          uw_regs
          refine ups_cp .wCur _ _ (by uw_le) (by simp [cpDst, cpSrc]) ?_
          simp only [cpDst, cpSrc, cpEx]
          uw_regs
          rw [hpad true (by simpa using hedge), if_pos rfl]
          exact hrest _ _ (by uw_le) hn rfl ht rfl rfl
        · refine PSem.call_neg rfl (UReg.reg (by uw_le) _ _)
            (by simp only [UReg.v_0, pathOr_bit, hn, hv]; simpa [inEdge, pathEdge] using hedge) ?_
          rw [hpad false (by simpa using hedge), if_neg (by simp)]
          exact hrest _ _ (by uw_le) hn hv ht rfl rfl
      · have hjn' : n ≤ j := by simp only at hjn; omega
        have hpad : padNbr (inEdge x n) v ⟨j, hjD⟩ = v := by
          unfold padNbr
          rw [dif_neg (by simp only; omega)]
        rw [hpad]
        exact hrest _ _ (by uw_le) hn hv ht rfl rfl
    refine (ups_coin F n _ (by simp [hn]) (by uw_le) (by simpa using hn2)
      fun j h1 h2 b e hb he => ?_).congr ?_
    · simp only [Nat.zero_mul, zero_add, one_mul] at h1 h2 ⊢
      exact UPS.of_eq (by uw_ext) (hstep j h2 b e hb he)
    · simp only [Nat.zero_mul, Nat.zero_add]
      exact sum_slots _ _ v

end LogProg

end Complexity
