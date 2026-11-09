/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenStage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The setup and the radius loop of the window-growing counting machine

The parts of `Complexity.LogProg.ISGen.igA` [AB09, §4.3.2] around its stages, in the
continuation semantics of `TCSlib.Complexity.SpaceComplexity.Machines.NARMKit`, for arbitrary
deciders' answers `orc`:

* the setup (`gscan_run`, `ghalf_run`): `n := |x|`, then `lg := size |x| + 1` and `n := 0`;
* one iteration of the radius loop (`iter_run`): the exponent `e = 2E · lg + 2E · s` by
  add-twice rounds (`grounds_run`), the code bound `K = 2 ^ e` by doubling (`gdouble_run`),
  the stage start `i = 0`, `i1 = 1`, `cp = 1`, and the stages (`gstage`), which reach the
  comparison `cmp` with `cp = |C_K|`;
* the comparison (`cmp_run`): accept if `cp` equals the previous count (register `n`),
  otherwise store `cp` in `n`, increment the radius and iterate.

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ISGen.gev`, `Complexity.LogProg.ISGen.gKv` — the exponent and the code
  bound at a radius.

## Main results

* `Complexity.LogProg.ISGen.iter_run`, `Complexity.LogProg.ISGen.cmp_run`,
  `Complexity.LogProg.ISGen.start_run`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing ISCount ISTac

variable {E : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B : ℕ}

/-- The exponent `2E · lg + 2E · s` at radius `s` (`lg` the halving count). -/
def gev (E lg s : ℕ) : ℕ := 2 * E * lg + 2 * E * s

/-- The code bound `2 ^ (2E · lg + 2E · s)` at radius `s`. -/
def gKv (E lg s : ℕ) : ℕ := 2 ^ gev E lg s

/-! ## The setup -/

/-- **The length scan**: from `scan` with `n ≤ |x|`, the machine counts `n` up to `|x|`.

**Proof sketch.** Induction on `|x| - n`, the input-length decider answering `n < |x|`. -/
theorem gscan_run
    (hq : ∀ k ≤ x.length, orc 0 (pairEncode x (Nat.bits k)) = decide (k < x.length))
    (Q : Prop) (σ : St) (hσ : σ.Bd B) (hn : σ.n ≤ x.length) (hx : x.length ≤ B)
    (hQ : IG (E := E) orc x B .lg0 { σ with n := x.length } Q) :
    IG (E := E) orc x B .scan σ Q := by
  suffices H : ∀ d (σ : St), x.length - σ.n = d → σ.Bd B → σ.n ≤ x.length →
      IG (E := E) orc x B .lg0 { σ with n := x.length } Q → IG (E := E) orc x B .scan σ Q by
    exact H _ σ rfl hσ hn hQ
  intro d
  induction d with
  | zero =>
    intro σ hd hσ hn hQ
    have he : σ.n = x.length := by omega
    refine NSem.call_neg rfl (St.greg hσ _ _) (by isr; rw [hq _ hn]; simp [he]) ?_
    exact IG.of_eq (by ext <;> simp [he]) hQ
  | succ d ih =>
    intro σ hd hσ hn hQ
    refine NSem.call_pos rfl (St.greg hσ _ _) (by isr; rw [hq _ hn]; simp; omega) ?_
    refine NSem.inc rfl (St.greg hσ _ _) ?_
    isr
    exact ih _ (by dsimp only; omega) (by isb) (by dsimp only; omega)
      (IG.of_eq (by ext <;> rfl) hQ)

/-- **The halving loop**: from `hz`, the machine halves `n` down to `0`, adding its binary
length `size n` to `lg`, and enters the radius loop.

**Proof sketch.** Strong induction on `n` (`size_half`). -/
theorem ghalf_run (Q : Prop) (σ : St) (hσ : σ.Bd B) (hb : σ.lg + Nat.size σ.n ≤ B)
    (hQ : IG (E := E) orc x B (.rd false (Fin.last E))
      { σ with n := 0, lg := σ.lg + Nat.size σ.n } Q) :
    IG (E := E) orc x B .hz σ Q := by
  suffices H : ∀ m (σ : St), σ.n = m → σ.Bd B → σ.lg + Nat.size σ.n ≤ B →
      IG (E := E) orc x B (.rd false (Fin.last E))
        { σ with n := 0, lg := σ.lg + Nat.size σ.n } Q →
      IG (E := E) orc x B .hz σ Q by
    exact H _ σ rfl hσ hb hQ
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro σ hm hσ hb hQ
  by_cases h0 : σ.n = 0
  · refine NSem.jz_pos rfl (St.greg hσ _ _) (by isr; exact h0) ?_
    exact IG.of_eq (by ext <;> simp [h0]) hQ
  · have hs := size_half h0
    refine NSem.jz_neg rfl (St.greg hσ _ _) (by isr; exact h0) ?_
    refine NSem.half rfl (St.greg hσ _ _) ?_
    isr
    refine NSem.inc rfl (St.greg (by isb) _ _) ?_
    isr
    refine ih (σ.n / 2) (by omega) _ rfl (by simp only [St.Bd] at hσ ⊢; omega)
      (by dsimp only; omega) (IG.of_eq (by ext <;> simp; omega) hQ)

/-! ## One iteration of the radius loop -/

/-- **The rounds**: from `rd ph j`, the machine adds `2 j · y` to `e` by `j` add-twice rounds
(`y = s` for `ph`, `y = lg` otherwise) and reaches `rd ph 0` (with some value of the counter
`k`).

**Proof sketch.** Induction on `j`; each round clears `k` and adds `2y` (`nsem_addTwice`). -/
theorem grounds_run (Q : Prop) (ph : Bool) : ∀ (j : ℕ) (hj : j < E + 1) (σ : St), σ.Bd B →
    σ.e + 2 * j * (if ph then σ.s else σ.lg) ≤ B →
    (∀ k', k' ≤ B → IG (E := E) orc x B (.rd ph 0)
      { σ with e := σ.e + 2 * j * (if ph then σ.s else σ.lg), k := k' } Q) →
    IG (E := E) orc x B (.rd ph ⟨j, hj⟩) σ Q := by
  intro j
  induction j with
  | zero =>
    intro hj σ hσ _ hK
    exact IG.of_eq (by ext <;> simp) (hK σ.k (by isb))
  | succ j ih =>
    intro hj σ hσ hb hK
    cases ph
    · simp only [Bool.false_eq_true, if_false] at hb hK ih ⊢
      have e1 : 2 * (j + 1) * σ.lg = 2 * σ.lg + 2 * j * σ.lg := by ring
      refine NSem.clr (r := rk) (l' := .ak false ⟨j + 1, hj⟩) (by simp [igA]) (St.greg hσ _ _) ?_
      isr
      refine nsem_addTwice (igA E) orc x B rk (rY false) re (by decide)
        (by decide) (by decide) (.ak false ⟨j + 1, hj⟩) (.ak1 false ⟨j + 1, hj⟩)
        (.ak2 false ⟨j + 1, hj⟩) (.ak3 false ⟨j + 1, hj⟩) (.rd false ⟨j, by omega⟩) rfl rfl rfl rfl
        _ _ (St.greg (E := E) (by isb) none none) (by simp) (by simp; omega) ?_
      simp only [toV_rY, St.toV_e, St.toV_k, Nat.sub_zero, Bool.false_eq_true, if_false]
      isr
      refine ih (by omega) _ (by isb) (by dsimp only; omega) fun k' hk' => ?_
      exact IG.of_eq (by ext <;> simp; omega) (hK k' hk')
    · simp only [if_true] at hb hK ih ⊢
      have e1 : 2 * (j + 1) * σ.s = 2 * σ.s + 2 * j * σ.s := by ring
      refine NSem.clr (r := rk) (l' := .ak true ⟨j + 1, hj⟩) (by simp [igA]) (St.greg hσ _ _) ?_
      isr
      refine nsem_addTwice (igA E) orc x B rk (rY true) re (by decide)
        (by decide) (by decide) (.ak true ⟨j + 1, hj⟩) (.ak1 true ⟨j + 1, hj⟩)
        (.ak2 true ⟨j + 1, hj⟩) (.ak3 true ⟨j + 1, hj⟩) (.rd true ⟨j, by omega⟩) rfl rfl rfl rfl
        _ _ (St.greg (E := E) (by isb) none none) (by simp) (by simp; omega) ?_
      simp only [toV_rY, St.toV_e, St.toV_k, Nat.sub_zero, if_true]
      isr
      refine ih (by omega) _ (by isb) (by dsimp only; omega) fun k' hk' => ?_
      exact IG.of_eq (by ext <;> simp; omega) (hK k' hk')

/-- **The doubling loop**: from `db` with `e = m`, the machine multiplies `K` by `2 ^ m`,
clears `e`, and reaches `st0` (with some values of the scratch registers `k`, `T`).

**Proof sketch.** Induction on `m`; each round decrements `e` (`nsem_dec`), sets `T := 2K`
(`nsem_addTwice`), clears `K` and copies `T` back (`nsem_copy`). -/
theorem gdouble_run (Q : Prop) : ∀ (m : ℕ) (σ : St), σ.e = m → σ.Bd B → σ.K * 2 ^ m ≤ B →
    (∀ k' T', k' ≤ B → T' ≤ B →
      IG (E := E) orc x B .st0 { σ with e := 0, K := σ.K * 2 ^ m, k := k', T := T' } Q) →
    IG (E := E) orc x B .db σ Q := by
  intro m
  induction m with
  | zero =>
    intro σ hm hσ _ hK
    refine NSem.jz_pos rfl (St.greg hσ _ _) (by isr; exact hm) ?_
    exact IG.of_eq (by ext <;> simp [hm]) (hK σ.k σ.T (by isb) (by isb))
  | succ m ih =>
    intro σ hm hσ hb hK
    have e1 : σ.K * 2 ^ (m + 1) = 2 * σ.K * 2 ^ m := by ring
    have e2 : σ.K ≤ σ.K * 2 ^ m := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos m)
    have e3 : 2 * σ.K * 2 ^ m = 2 * (σ.K * 2 ^ m) := by ring
    refine NSem.jz_neg rfl (St.greg hσ _ _) (by isr; omega) ?_
    refine nsem_dec rfl (St.greg hσ _ _) ?_
    isr
    refine NSem.clr rfl (St.greg (by isb) _ _) ?_
    isr
    refine NSem.clr rfl (St.greg (by isb) _ _) ?_
    isr
    refine nsem_addTwice (igA E) orc x B rk rK rT (by decide) (by decide) (by decide)
      .dk .dk1 .dk2 .dk3 .dcl rfl rfl rfl rfl _ _ (St.greg (E := E) (by isb) none none)
      (by simp) (by simp; omega) ?_
    isr
    refine NSem.clr rfl (St.greg (by isb) _ _) ?_
    isr
    refine nsem_copy (igA E) orc x B rK rT (by decide) .dcp .dcb .db rfl rfl _ _
      (St.greg (E := E) (by isb) none none) (by simp) ?_
    isr
    refine ih _ (by dsimp only; omega) (by isb)
      (by dsimp only; rw [Nat.sub_zero, Nat.zero_add]; omega) fun k' T' hk' hT' => ?_
    exact IG.of_eq (by ext <;> (try simp); ring_nf) (hK k' T' hk' hT')

/-- **One iteration of the radius loop**: at `rd false E` with `e = 0`, clear scratch
registers and the code bound `K = gKv E lg s` (plus one) at most `B`, if the ball `C_0` of
the configuration graph read from `orc` at radius `s` over codes below `K` has one element,
then some branch accepts iff no ball `C_1, …, C_K` contains an accepting code and the
continuation at `cmp` accepts, entered with `e = 0`, the code bound `K`, `i = K`,
`i1 = K + 1` and the count `cp = |C_K|`; every branch terminates.

**Proof sketch.** The rounds (`grounds_run`, twice) compute `e = 2E · lg + 2E · s`; `K := 1`
and the doubling loop (`gdouble_run`) compute `K = 2 ^ e`; the stage start sets `i = 0`,
`i1 = 1`, `cp = 1 = |C_0|`, and the stages run with the correct count (`gstage`). -/
theorem iter_run (Q : Prop) (σ : St) (hσ : σ.Bd B) (he : σ.e = 0) (hz : σ.Clear)
    (hKB : gKv E σ.lg σ.s + 1 ≤ B)
    (h0 : (ball (gKv E σ.lg σ.s) (RelO orc x σ.s) (InitO orc x σ.s) 0).card = 1)
    (hQ : ∀ k' T' v' c', k' ≤ B → T' ≤ B → v' ≤ B → c' ≤ B →
      IG (E := E) orc x B .cmp
        { σ with e := 0, K := gKv E σ.lg σ.s, k := k', T := T', i := gKv E σ.lg σ.s,
                 i1 := gKv E σ.lg σ.s + 1, v := v', c := c',
                 cp := (ball (gKv E σ.lg σ.s) (RelO orc x σ.s) (InitO orc x σ.s)
                   (gKv E σ.lg σ.s)).card } Q) :
    IG (E := E) orc x B (.rd false (Fin.last E)) σ
      ((∀ j, 0 < j → j ≤ gKv E σ.lg σ.s →
        ∀ t ∈ ball (gKv E σ.lg σ.s) (RelO orc x σ.s) (InitO orc x σ.s) j,
          ¬ AccO orc x σ.s t) ∧ Q) := by
  set K := gKv E σ.lg σ.s with hKdef
  have hge : gev E σ.lg σ.s < K := Nat.lt_two_pow_self
  have hlgK : 2 * E * σ.lg ≤ gev E σ.lg σ.s := by simp only [gev]; omega
  have hsK : 2 * E * σ.s ≤ gev E σ.lg σ.s := by simp only [gev]; omega
  have hgev : gev E σ.lg σ.s = 2 * E * σ.lg + 2 * E * σ.s := rfl
  have hKB' : 2 ^ gev E σ.lg σ.s + 1 ≤ B := hKB
  -- the `lg` rounds
  refine grounds_run _ false E (Nat.lt_succ_self E) σ hσ (by simp; omega) fun k1 hk1 => ?_
  simp only [Bool.false_eq_true, if_false, he, Nat.zero_add]
  refine NSem.clr (r := rk) (l' := .rd true (Fin.last E)) (by simp [igA, grdX])
    (St.greg (by isb) _ _) ?_
  isr
  -- the `s` rounds
  refine grounds_run _ true E (Nat.lt_succ_self E) _ (by isb) (by simp; omega)
    fun k2 hk2 => ?_
  simp only [if_true]
  refine NSem.clr (r := rK) (l' := .k1) (by simp [igA, grdX]) (St.greg (by isb) _ _) ?_
  isr
  refine NSem.inc rfl (St.greg (by isb) _ _) ?_
  isr
  -- the doubling loop
  refine gdouble_run _ (gev E σ.lg σ.s) _ (by simp [gev]) (by isb)
    (by simp only [Nat.zero_add, Nat.one_mul]; exact Nat.le_of_succ_le hKB)
    fun k3 T3 hk3 hT3 => ?_
  -- the stage start
  refine NSem.clr rfl (St.greg (by isb) _ _) ?_
  isr
  refine NSem.clr rfl (St.greg (by isb) _ _) ?_
  isr
  refine NSem.inc rfl (St.greg (by isb) _ _) ?_
  isr
  refine NSem.clr rfl (St.greg (by isb) _ _) ?_
  isr
  refine NSem.inc rfl (St.greg (by isb) _ _) ?_
  isr
  obtain ⟨hg, hcur, hstp, hu, hcnt⟩ := hz
  refine IG.of_eq ?_ (gstage (E := E) (orc := orc) (x := x) (B := B) Q
    { σ with e := 0, K := K, k := k3, T := T3, i := 0, i1 := 1, cp := 1 }
    (by isb) (by simpa using hKB) (Nat.zero_le _) rfl (by simpa using h0.symm)
    ⟨hg, hcur, hstp, hu, hcnt⟩ fun v' c' hv' hc' => IG.of_eq (by ext <;> rfl)
      (hQ k3 T3 v' c' hk3 hT3 hv' hc'))
  ext <;> simp [hKdef, gKv]

/-! ## The comparison -/

/-- **The comparison of the counts**: at `cmp`, if the count `cp` equals the previous count
`n` the machine accepts; otherwise it stores `cp` in `n`, increments the radius `s`, and
continues at `rd false E`.

**Proof sketch.** An equality test; the store is a clear and a copy loop (`nsem_copy`). -/
theorem cmp_run (Q : Prop) (σ : St) (hσ : σ.Bd B) (hs : σ.s + 1 ≤ B)
    (hQ : σ.cp ≠ σ.n →
      IG (E := E) orc x B (.rd false (Fin.last E)) { σ with n := σ.cp, s := σ.s + 1 } Q) :
    IG (E := E) orc x B .cmp σ (σ.cp = σ.n ∨ (σ.cp ≠ σ.n ∧ Q)) := by
  by_cases he : σ.cp = σ.n
  · exact (NSem.jeq_pos rfl (St.greg hσ _ _) (by isr; exact he)
      (NSem.ret rfl (St.greg hσ _ _))).congr (by simp [he])
  refine (NSem.jeq_neg (P := Q) rfl (St.greg hσ _ _) (by isr; exact he) ?_).congr (by simp [he])
  refine NSem.clr rfl (St.greg hσ _ _) ?_
  isr
  refine nsem_copy (igA E) orc x B rn rcp (by decide) .nx1 .nx2 .nx3 rfl rfl _ _
    (St.greg (E := E) (by isb) none none) (by simp) ?_
  isr
  refine NSem.inc rfl (St.greg (by isb) _ _) ?_
  isr
  exact IG.of_eq (by ext <;> rfl) (hQ he)

/-! ## The start -/

/-- **The start**: from the zero register file, the setup reaches the radius loop at radius
`0`, with previous count `0`, `lg = size |x| + 1` and every other register clear.

**Proof sketch.** The length scan (`gscan_run`), `lg := 1`, and the halving loop
(`ghalf_run`). -/
theorem start_run
    (hq : ∀ k ≤ x.length, orc 0 (pairEncode x (Nat.bits k)) = decide (k < x.length))
    (Q : Prop) (hB : 2 ^ lgv x.length ≤ B)
    (hQ : IG (E := E) orc x B (.rd false (Fin.last E)) { St.zero with lg := lgv x.length } Q) :
    IG (E := E) orc x B .scan St.zero Q := by
  have hxl : x.length < 2 ^ lgv x.length := lt_two_pow_size_succ x.length
  have hlg : lgv x.length < 2 ^ lgv x.length := Nat.lt_two_pow_self
  refine gscan_run hq _ St.zero (by simp only [St.Bd, St.zero]; omega) (by simp [St.zero])
    (by omega) ?_
  refine NSem.inc rfl (St.greg (by simp only [St.Bd, St.zero]; omega) _ _) ?_
  isr
  refine ghalf_run _ _ (by simp only [St.Bd, St.zero]; omega)
    (by simp only [St.zero, lgv] at hxl hlg hB ⊢; omega) (IG.of_eq ?_ hQ)
  ext <;> simp [St.zero, lgv]; omega

end ISGen

end Complexity.LogProg
