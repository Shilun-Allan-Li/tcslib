/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.UPathMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The shared loops of the random-walk machine for `UPATH`

[AB09, Theorem 7.19]: the loops of `Complexity.LogProg.upA` used at several sites, in the
probabilistic continuation semantics of `TCSlib.Complexity.SpaceComplexity.Machines.NARMPSem`
— a copy, an add-twice loop, the multiplication `R := R + A · B` (two generic loops of
`Complexity.LogProg.NARM`), and the computation of the matrix position
`2n + 2 + 2(r · n + c)` of an edge `(r, c)`, after `Complexity.LogProg.ps_index`.

## Main definitions

None: the results are phase lemmas about `Complexity.LogProg.upA`.

## Main results

* `Complexity.LogProg.psem_addOnce`, `Complexity.LogProg.psem_mul` — generic loops.
* `Complexity.LogProg.ups_cp`, `Complexity.LogProg.ups_ad`, `Complexity.LogProg.ups_mul` —
  the sites of the copies, add-twice loops and multiplications.
* `Complexity.LogProg.ups_index` — the matrix position of an edge.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7.)
-/

namespace Complexity.LogProg

open Turing ULabel UPathTac

variable {m d : ℕ} {Λ : Type}

section Generic

variable (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool) (B : ℕ)

/-- **Adding a register**: the loop `test: if j = y exit; R += 1; j += 1; goto test` (with
`j`, `y`, `R` distinct), from `j ≤ y`, adds `y - j` to `R` and leaves `j = y`.

**Proof sketch.** Induction on `y - j`; each round increments `R` and `j` once, both bounded
by the final value of `R` (resp. `y`). -/
theorem psem_addOnce (j y R : Fin m) (hjy : j ≠ y) (hjR : j ≠ R) (hRy : R ≠ y)
    (test i₁ i₂ ex : Λ)
    (htest : A test = .det (.jeq j y ex i₁)) (h₁ : A i₁ = .det (.inc R i₂))
    (h₂ : A i₂ = .det (.inc j test)) (q : ℚ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B)
    (hle : v j ≤ v y) (hb : v R + (v y - v j) ≤ B)
    (hK : PSem A oracle x (RegLe m Λ B)
      (some ex, Function.update (Function.update v R (v R + (v y - v j))) j (v y), none) q) :
    PSem A oracle x (RegLe m Λ B) (some test, v, none) q := by
  generalize hc : v y - v j = c at hb hK
  induction c generalizing v with
  | zero =>
    have he : v j = v y := by omega
    simp only [Nat.add_zero, Function.update_eq_self, ← he] at hK
    exact PSem.jeq_pos htest hv he hK
  | succ c ih =>
    have hne : v j ≠ v y := by omega
    let v₁ := Function.update v R (v R + 1)
    let v₂ := Function.update v₁ j (v₁ j + 1)
    have hv₁ : ∀ r, v₁ r ≤ B := register_update_le v R B _ hv (by omega)
    have e₁j : v₁ j = v j := by simp [v₁, Function.update_of_ne hjR]
    have hv₂ : ∀ r, v₂ r ≤ B := register_update_le v₁ j B _ hv₁ (by
      rw [e₁j]; have := hv y; omega)
    have e₂j : v₂ j = v j + 1 := by simp [v₂, e₁j]
    have e₂y : v₂ y = v y := by
      simp [v₂, v₁, Function.update_of_ne hjy.symm, Function.update_of_ne hRy.symm]
    have e₂R : v₂ R = v R + 1 := by simp [v₂, v₁, Function.update_of_ne hjR.symm]
    have hfin : Function.update (Function.update v₂ R (v₂ R + c)) j (v₂ y) =
        Function.update (Function.update v R (v R + (c + 1))) j (v y) := by
      rw [e₂R, e₂y]
      funext r
      by_cases hr : r = j
      · subst hr; simp
      · by_cases hp : r = R
        · subst hp; simp [Function.update_of_ne hjR.symm]; omega
        · simp [v₂, v₁, Function.update_of_ne hr, Function.update_of_ne hp]
    have hrest := ih v₂ hv₂ (by omega) (by omega) (by omega) (by rw [hfin]; exact hK)
    exact PSem.jeq_neg htest hv hne (PSem.inc h₁ hv (PSem.inc h₂ hv₁ hrest))

/-- **Multiplying**: the loop `mo: if i = a exit; j := 0; [add b to R]; i += 1; goto mo`
(counters `i ≠ j`, bounds `a`, `b`, result `R`), from `i ≤ a`, adds `(a - i) · b` to `R` and
leaves `i = a` (and `j` at some value at most `B`).

**Proof sketch.** Induction on `a - i`, each round one `psem_addOnce`. -/
theorem psem_mul (i j a b R : Fin m) (hia : i ≠ a) (hjb : j ≠ b) (hjR : j ≠ R) (hRb : R ≠ b)
    (hij : i ≠ j) (hiR : i ≠ R) (hRa : R ≠ a) (hja : j ≠ a) (hib : i ≠ b)
    (mo mo₁ mi mi₁ mi₂ mo₂ ex : Λ)
    (hmo : A mo = .det (.jeq i a ex mo₁)) (hmo₁ : A mo₁ = .det (.clr j mi))
    (hmi : A mi = .det (.jeq j b mo₂ mi₁)) (hmi₁ : A mi₁ = .det (.inc R mi₂))
    (hmi₂ : A mi₂ = .det (.inc j mi)) (hmo₂ : A mo₂ = .det (.inc i mo))
    (q : ℚ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hle : v i ≤ v a)
    (hb : v R + (v a - v i) * v b ≤ B)
    (hK : ∀ z, z ≤ B → PSem A oracle x (RegLe m Λ B)
      (some ex, Function.update (Function.update (Function.update v R
        (v R + (v a - v i) * v b)) i (v a)) j z, none) q) :
    PSem A oracle x (RegLe m Λ B) (some mo, v, none) q := by
  generalize hc : v a - v i = c at hb hK
  induction c generalizing v with
  | zero =>
    have he : v i = v a := by omega
    have := hK (v j) (hv j)
    simp only [Nat.zero_mul, Nat.add_zero, Function.update_eq_self, ← he] at this
    exact PSem.jeq_pos hmo hv he this
  | succ c ih =>
    have hne : v i ≠ v a := by omega
    have hb' : v b ≤ B := hv b
    let v₁ := Function.update v j 0
    have hv₁ : ∀ r, v₁ r ≤ B := register_update_le v j B _ hv (by omega)
    have e₁b : v₁ b = v b := by simp [v₁, Function.update_of_ne hjb.symm]
    have e₁R : v₁ R = v R := by simp [v₁, Function.update_of_ne hjR.symm]
    have e₁j : v₁ j = 0 := by simp [v₁]
    let v₂ := Function.update (Function.update v₁ R (v₁ R + (v₁ b - v₁ j))) j (v₁ b)
    let v₃ := Function.update v₂ i (v₂ i + 1)
    have e₂i : v₂ i = v i := by
      simp [v₂, v₁, Function.update_of_ne hij, Function.update_of_ne hiR]
    have e₂R : v₂ R = v R + v b := by
      simp [v₂, Function.update_of_ne hjR.symm, e₁R, e₁b, e₁j]
    have e₂a : v₂ a = v a := by
      simp [v₂, v₁, Function.update_of_ne hja.symm, Function.update_of_ne hRa.symm]
    have e₂b : v₂ b = v b := by
      simp [v₂, v₁, Function.update_of_ne hjb.symm, Function.update_of_ne hRb.symm]
    have hmul : (c + 1) * v b = c * v b + v b := by ring
    have hv₂ : ∀ r, v₂ r ≤ B := by
      refine register_update_le _ j B _ (register_update_le v₁ R B _ hv₁ ?_) (by omega)
      rw [e₁R, e₁b, e₁j, Nat.sub_zero]; rw [hmul] at hb; omega
    have hv₃ : ∀ r, v₃ r ≤ B := register_update_le v₂ i B _ hv₂ (by rw [e₂i]; have := hv a; omega)
    have e₃i : v₃ i = v i + 1 := by simp [v₃, e₂i]
    have e₃a : v₃ a = v a := by simp [v₃, Function.update_of_ne hia.symm, e₂a]
    have e₃b : v₃ b = v b := by simp [v₃, Function.update_of_ne hib.symm, e₂b]
    have e₃R : v₃ R = v R + v b := by simp [v₃, Function.update_of_ne hiR.symm, e₂R]
    have hrest : PSem A oracle x (RegLe m Λ B) (some mo, v₃, none) q := by
      refine ih v₃ hv₃ (by omega) (by rw [e₃a, e₃i]; omega) ?_ fun z hz => ?_
      · rw [e₃R, e₃b]; rw [hmul] at hb; omega
      · have := hK z hz
        convert this using 3
        funext r
        by_cases hrj : r = j
        · subst hrj; simp
        · by_cases hri : r = i
          · subst hri; simp [Function.update_of_ne hij, e₃a]
          · by_cases hrR : r = R
            · subst hrR
              simp [Function.update_of_ne hjR.symm, Function.update_of_ne hiR.symm, e₃R, e₃b]
              rw [hmul]; ring
            · simp [v₃, v₂, v₁, Function.update_of_ne hrj, Function.update_of_ne hri,
                Function.update_of_ne hrR]
    refine PSem.jeq_neg hmo hv hne (PSem.clr hmo₁ hv ?_)
    refine psem_addOnce A oracle x B j b R hjb hjR hRb mi mi₁ mi₂ mo₂ hmi hmi₁ hmi₂ q v₁ hv₁
      (by rw [e₁j]; omega) (by rw [e₁R, e₁b, e₁j, Nat.sub_zero]; rw [hmul] at hb; omega) ?_
    exact PSem.inc hmo₂ hv₂ hrest

end Generic

variable {x : List Bool} {B : ℕ}

/-- **A copy site**: `dst := src`, from `dst ≤ src`. -/
lemma ups_cp (k : CpSite) (p : ℚ) (σ : UReg) (hσ : σ.Le B)
    (hle : σ.v (cpDst k) ≤ σ.v (cpSrc k))
    (hK : PSem upA pathOr x (RegLe 15 ULabel B)
      (some (cpEx k), Function.update σ.v (cpDst k) (σ.v (cpSrc k)), none) p) :
    UPS x B (cp k) σ p :=
  psem_copy upA pathOr x B (cpDst k) (cpSrc k) (by cases k <;> decide) (cp k) (cpb k) (cpEx k)
    rfl rfl p σ.v (UReg.reg hσ none none) hle hK

/-- The counter of an add-twice site is distinct from its other registers. -/
private lemma adSite_ne (k : AdSite) : (3 : Fin 15) ≠ adY k ∧ (3 : Fin 15) ≠ adP k ∧
    adP k ≠ adY k := by
  cases k with
  | ix k j => cases k <;> fin_cases j <;> decide
  | ten j => fin_cases j <;> decide
  | dbl => decide

/-- **An add-twice site**: `P := P + 2 (Y - b)`, `b := Y`, from `b ≤ Y`. -/
lemma ups_ad (k : AdSite) (q : ℚ) (σ : UReg) (hσ : σ.Le B) (hle : σ.b ≤ σ.v (adY k))
    (hb : σ.v (adP k) + 2 * (σ.v (adY k) - σ.b) ≤ B)
    (hK : PSem upA pathOr x (RegLe 15 ULabel B)
      (some (adEx k), Function.update (Function.update σ.v (adP k)
        (σ.v (adP k) + 2 * (σ.v (adY k) - σ.b))) 3 (σ.v (adY k)), none) q) :
    UPS x B (ad0 k) σ q :=
  psem_addTwice upA pathOr x B 3 (adY k) (adP k) (adSite_ne k).1 (adSite_ne k).2.1
    (adSite_ne k).2.2 (ad0 k) (ad1 k) (ad2 k) (ad3 k) (adEx k) rfl rfl rfl rfl q σ.v
    (UReg.reg hσ none none) hle hb hK

/-- **A multiplication site**: `R := R + A · B` (counters `a`, `b`), entered at the clear of
the outer counter.

**Proof sketch.** Clear the outer counter, then `psem_mul` at the site's registers. -/
lemma ups_mul (k : MulSite) (q : ℚ) (σ : UReg) (hσ : σ.Le B)
    (hb : σ.v (mulR k) + σ.v (mulA k) * σ.v (mulB k) ≤ B)
    (hK : ∀ z, z ≤ B → PSem upA pathOr x (RegLe 15 ULabel B)
      (some (mulEx k), Function.update (Function.update (Function.update
        (Function.update σ.v 2 0) (mulR k) (σ.v (mulR k) + σ.v (mulA k) * σ.v (mulB k)))
        2 (σ.v (mulA k))) 3 z, none) q) :
    UPS x B (mc k) σ q := by
  have hne : ∀ r : Fin 15, r = mulA k ∨ r = mulB k ∨ r = mulR k → r ≠ 2 ∧ r ≠ 3 := by
    intro r hr; cases k <;> rcases hr with rfl | rfl | rfl <;> decide
  have hRA : mulR k ≠ mulA k := by cases k <;> decide
  have hRB : mulR k ≠ mulB k := by cases k <;> decide
  have e : ∀ r : Fin 15, r ≠ 2 → Function.update σ.v 2 0 r = σ.v r := fun r h =>
    Function.update_of_ne h _ _
  refine PSem.clr (A := upA) rfl (UReg.reg hσ _ _) ?_
  have := psem_mul upA pathOr x B 2 3 (mulA k) (mulB k) (mulR k)
    (hne _ (Or.inl rfl)).1.symm (hne _ (Or.inr (Or.inl rfl))).2.symm
    (hne _ (Or.inr (Or.inr rfl))).2.symm hRB (by decide) (hne _ (Or.inr (Or.inr rfl))).1.symm
    hRA (hne _ (Or.inl rfl)).2.symm (hne _ (Or.inr (Or.inl rfl))).1.symm
    (mo k) (mo1 k) (mi k) (mi1 k) (mi2 k) (mo2 k) (mulEx k)
    rfl rfl rfl rfl rfl rfl q (Function.update σ.v 2 0)
    (register_update_le σ.v 2 B 0 (UReg.reg hσ none none) (Nat.zero_le _))
    (by simp) (by
      rw [e _ (hne _ (Or.inr (Or.inr rfl))).1, e _ (hne _ (Or.inl rfl)).1,
        e _ (hne _ (Or.inr (Or.inl rfl))).1]
      simpa using hb)
  refine this fun z hz => ?_
  have h1 := e _ (hne _ (Or.inr (Or.inr rfl))).1
  have h2 := e _ (hne _ (Or.inl rfl)).1
  have h3 := e _ (hne _ (Or.inr (Or.inl rfl))).1
  simp only [Function.update_self] at h1 h2 h3 ⊢
  rw [h1, h2, h3, Nat.sub_zero]
  exact hK z hz

/-- Index sites read their row and column outside the registers `p`, `a`, `b`. -/
lemma ixRow_ne (k : IxSite) : ixRow k ≠ 0 ∧ ixRow k ≠ 2 ∧ ixRow k ≠ 3 := by
  cases k <;> decide

/-- Index sites read their column outside the registers `p`, `a`, `b`. -/
lemma ixCol_ne (k : IxSite) : ixCol k ≠ 0 ∧ ixCol k ≠ 2 ∧ ixCol k ≠ 3 := by
  cases k <;> decide

/-- The row and column of an index site do not see writes of `p`, `a`, `b`. -/
lemma ix_v_upd (k : IxSite) (σ : UReg) (p a b : ℕ) :
    ({ σ with p := p, a := a, b := b } : UReg).v (ixRow k) = σ.v (ixRow k) ∧
    ({ σ with p := p, a := a, b := b } : UReg).v (ixCol k) = σ.v (ixCol k) := by
  cases k <;> exact ⟨rfl, rfl⟩

/-- **The row loop** of index site `k`: from row `a ≤ r` (`r` the row register) with the
pointer at the start of row `a`, the machine reaches the start of row `r`.

**Proof sketch.** Induction on `r - a`, as `Complexity.LogProg.ps_row`: at `a = r` the loop
exits; otherwise it clears the column counter, adds `2n` to the pointer and increments the
row. -/
lemma ups_row (k : IxSite) (q : ℚ) : ∀ dd (σ : UReg), σ.v (ixRow k) - σ.a = dd → σ.Le B →
    σ.a ≤ σ.v (ixRow k) → σ.v (ixRow k) < σ.n → σ.p = 2 * σ.n + 2 + 2 * (σ.a * σ.n) →
    σ.b ≤ σ.n → 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ B →
    (∀ b', b' ≤ σ.n → UPS x B (ix7 k)
      { σ with a := σ.v (ixRow k), p := 2 * σ.n + 2 + 2 * (σ.v (ixRow k) * σ.n), b := b' } q) →
    UPS x B (ix5 k) σ q := by
  intro dd
  induction dd with
  | zero =>
    intro σ hd hσ hi hs hp hb hm hK
    have he : σ.a = σ.v (ixRow k) := by omega
    refine PSem.jeq_pos (A := upA) rfl (UReg.reg hσ _ _) (by simpa using he) ?_
    refine UPS.of_eq ?_ (hK σ.b hb)
    ext <;> simp [← he, hp]
  | succ dd ih =>
    intro σ hd hσ hi hs hp hb hm hK
    have hne : σ.a ≠ σ.v (ixRow k) := by omega
    have h1 : (σ.a + 1) * σ.n ≤ σ.v (ixRow k) * σ.n := Nat.mul_le_mul_right _ (by omega)
    have h2 : (σ.v (ixRow k) + 1) * σ.n ≤ σ.n * σ.n := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1 h2
    refine PSem.jeq_neg (A := upA) rfl (UReg.reg hσ _ _) (by simpa using hne) ?_
    refine PSem.clr (A := upA) rfl (UReg.reg hσ _ _) ?_
    uw_regs
    refine ups_ad (.ix k 1) q _ (by uw_le) (by simp [adY]) (by simp [adY, adP]; omega) ?_
    simp only [adY, adP, adEx]
    uw_regs
    refine PSem.inc (A := upA) rfl (UReg.reg (by uw_le) _ _) ?_
    uw_regs
    have hr := (ix_v_upd k σ (σ.p + 2 * σ.n) (σ.a + 1) σ.n).1
    refine UPS.of_eq (σ' := { σ with p := σ.p + 2 * σ.n, a := σ.a + 1, b := σ.n })
      (by ext <;> simp) ?_
    refine ih _ (by rw [hr]; dsimp only; omega) (by uw_le) (by rw [hr]; dsimp only; omega)
      (by rw [hr]; exact hs) (by dsimp only; rw [Nat.add_mul, Nat.one_mul]; omega) le_rfl hm
      fun b' hb' => UPS.of_eq ?_ (hK b' hb')
    rw [hr]

/-- **Index site `k`**: the machine sets the pointer to the matrix position
`2n + 2 + 2(r · n + c)` of the edge from the row register `r` to the column register `c`.

**Proof sketch.** As `Complexity.LogProg.ps_index`: clear the pointer, add `2n` and `2` to
reach the matrix, walk `r` rows (`ups_row`), then add `2c`. -/
lemma ups_index (k : IxSite) (q : ℚ) (σ : UReg) (hσ : σ.Le B)
    (hs : σ.v (ixRow k) < σ.n) (hj : σ.v (ixCol k) < σ.n)
    (hm : 2 * σ.n + 2 + 2 * (σ.n * σ.n) ≤ B)
    (hK : UPS x B (ixEx k) { σ with
      p := 2 * σ.n + 2 + 2 * (σ.v (ixRow k) * σ.n + σ.v (ixCol k)),
      a := σ.v (ixRow k), b := σ.v (ixCol k) } q) :
    UPS x B (ix0 k) σ q := by
  have hidx := rowMajor_lt hs hj
  have h0 : σ.v (ixRow k) * σ.n ≤ σ.n * σ.n := by omega
  refine PSem.clr (A := upA) rfl (UReg.reg hσ _ _) ?_
  uw_regs
  refine PSem.clr (A := upA) rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  refine ups_ad (.ix k 0) q _ (by uw_le) (by simp [adY]) (by simp [adY, adP]; omega) ?_
  simp only [adY, adP, adEx]
  uw_regs
  refine PSem.inc (A := upA) rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  refine PSem.inc (A := upA) rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  refine PSem.clr (A := upA) rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  have hr := ix_v_upd k σ (0 + 2 * (σ.n - 0) + 1 + 1) 0 σ.n
  refine ups_row k q _ _ rfl (by uw_le) (by rw [hr.1]; simp) (by rw [hr.1]; simpa using hs)
    (by simp) (by simp) (by simpa using hm) fun b' hb' => ?_
  simp only at hb' ⊢
  rw [hr.1]
  refine PSem.clr (A := upA) rfl (UReg.reg (by uw_le) _ _) ?_
  uw_regs
  have hr' := ix_v_upd k σ (2 * σ.n + 2 + 2 * (σ.v (ixRow k) * σ.n)) (σ.v (ixRow k)) 0
  refine ups_ad (.ix k 2) q _ (by uw_le) (by simp [adY]) (by
    simp only [adY, adP, UReg.v_0]; rw [hr'.2]; omega) ?_
  simp only [adY, adP, adEx]
  uw_regs
  refine UPS.of_eq ?_ hK
  rw [hr'.2]
  ext <;> simp; ring

end Complexity.LogProg
