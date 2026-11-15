/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.SpaceComplexity.Machines.NARMKit
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProb
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProof
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic semantics of nondeterministic register machines

A nondeterministic abstract register machine (`Complexity.LogProg.NARM`) whose `choose` bits
are fair coins is a probabilistic logspace algorithm [AB09, §7.7]. This file gives the
probabilistic counterpart of the continuation semantics `Complexity.LogProg.NSem`:
`Complexity.LogProg.PSem a p` says that every branch from `a` terminates and that, over choice
words long enough for all branches to halt, the answer is `true` with probability `p` and
`false` with probability `1 - p`. A deterministic step keeps `p` (its choice bit is ignored),
a `choose` averages its two targets. The bridge to logspace PTMs and to `RL` is
`TCSlib.Complexity.SpaceComplexity.Machines.NARMLogspace`.

This is infrastructure for [AB09, Theorem 7.19] (`TCSlib.Complexity.Randomized.UPathRL`), not
itself a result of the book.

## Main definitions

* `Complexity.LogProg.ansProb` — the probability of an answer over choice words of a length.
* `Complexity.LogProg.PSem` — the probabilistic semantics of a configuration.

## Main results

* the step lemmas `PSem.det`, `PSem.choose`, `PSem.inc`, `PSem.clr`, `PSem.half`,
  `PSem.jeq_pos`, `PSem.jeq_neg`, `PSem.jz_pos`, `PSem.jz_neg`, `PSem.call_pos`,
  `PSem.call_neg`, `PSem.ret`, and the loops `psem_copy`, `psem_addTwice`.
* `Complexity.LogProg.PSem.decides` — the length-`N` form.
* `Complexity.LogProg.PSem.of_reach`, `PSem.call`, `PSem.dec` — deterministic runs, calls with
  any arguments, decrements; `searchUp_run`, `searchDown_run` — linear searches.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7.)
-/

namespace Complexity.LogProg

open Turing Randomized

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- The probability that a choice word of length `N` drives the machine from `a` to the
answer `b`. -/
noncomputable def ansProb (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (a : AConf m Λ) (N : ℕ) (b : Bool) : ℚ :=
  randProb N (fun σ => (narun A oracle x σ a).2.2 = some b)

/-- **The probabilistic semantics of a configuration**: every branch from `a` terminates
through the guard `G`, and over choice words of any length `N` within which every branch
halts, the answer is `true` with probability `p` and `false` with probability `1 - p`. -/
def PSem (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a : AConf m Λ) (p : ℚ) : Prop :=
  NTerm A oracle x G a ∧ ∀ N, NHalts A oracle x (fun _ => True) a N →
    ansProb A oracle x a N true = p ∧ ansProb A oracle x a N false = 1 - p

section Semantics

variable {A : NARM m d Λ} {oracle : Fin d → List Bool → Bool} {G : AConf m Λ → Prop}

/-- Change the probability to an equal one. -/
lemma PSem.congr {a : AConf m Λ} {p q : ℚ} (h : PSem A oracle x G a p) (e : p = q) :
    PSem A oracle x G a q := e ▸ h

/-- A halted configuration answering `b` answers `true` with probability `1` or `0`. -/
lemma PSem.halted (v : Fin m → ℕ) (b : Bool) :
    PSem A oracle x G (none, v, some b) (if b then 1 else 0) := by
  refine ⟨NTerm.halted v _, fun N _ => ?_⟩
  unfold ansProb
  simp only [narun_halted]
  rw [randProb_const, randProb_const]
  cases b <;> simp

/-- A live configuration does not halt within `0` steps. -/
private lemma succ_of_nhalts {l : Λ} {v : Fin m → ℕ} {N : ℕ}
    (h : NHalts A oracle x (fun _ => True) (some l, v, none) N) : ∃ N', N = N' + 1 := by
  cases N with
  | zero => exact absurd (h [] rfl).1 (by simp)
  | succ N => exact ⟨N, rfl⟩

/-- **A deterministic step** keeps the probability. -/
lemma PSem.det {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) {v : Fin m → ℕ} {p : ℚ}
    (hG : G (some l, v, none))
    (h : PSem A oracle x G (astep (fun _ => i) oracle x (some l, v, none)) p) :
    PSem A oracle x G (some l, v, none) p := by
  have e : astep (A.detPart false) oracle x (some l, v, none) =
      astep (fun _ => i) oracle x (some l, v, none) := by
    rw [← nastep_det hA false false, nastep_det' hA]
  refine ⟨NTerm.step l v none hG fun b => ?_, fun N hN => ?_⟩
  · rw [nastep_det' hA]; exact h.1
  · obtain ⟨N, rfl⟩ := succ_of_nhalts hN
    have hN' := hN.of_det hA false
    rw [e] at hN'
    obtain ⟨h1, h0⟩ := h.2 N hN'
    unfold ansProb at h1 h0 ⊢
    rw [randProb_narun_det hA false v none N (fun a => a.2.2 = some true),
      randProb_narun_det hA false v none N (fun a => a.2.2 = some false), e]
    exact ⟨h1, h0⟩

/-- **A `choose`** averages the probabilities of its two targets. -/
lemma PSem.choose {l l₁ l₀ : Λ} (hA : A l = .choose l₁ l₀) {v : Fin m → ℕ} {p₁ p₀ : ℚ}
    (hG : G (some l, v, none)) (h₁ : PSem A oracle x G (some l₁, v, none) p₁)
    (h₀ : PSem A oracle x G (some l₀, v, none) p₀) :
    PSem A oracle x G (some l, v, none) ((p₁ + p₀) / 2) := by
  have e : ∀ b, nastep A oracle x b (some l, v, none) =
      (some (if b then l₁ else l₀), v, none) := fun b => nastep_choose hA b v none
  refine ⟨NTerm.step l v none hG fun b => ?_, fun N hN => ?_⟩
  · rw [e]; cases b
    · exact h₀.1
    · exact h₁.1
  · obtain ⟨N, rfl⟩ := succ_of_nhalts hN
    have k₁ := hN.of_choose hA true
    have k₀ := hN.of_choose hA false
    simp only [if_true, Bool.false_eq_true, if_false] at k₁ k₀
    obtain ⟨a₁, b₁⟩ := h₁.2 N k₁
    obtain ⟨a₀, b₀⟩ := h₀.2 N k₀
    unfold ansProb at a₁ b₁ a₀ b₀ ⊢
    rw [randProb_narun_choose hA v none N (fun a => a.2.2 = some true),
      randProb_narun_choose hA v none N (fun a => a.2.2 = some false), a₁, b₁, a₀, b₀]
    constructor <;> ring

/-- An increment. -/
lemma PSem.inc {l l' : Λ} {r : Fin m} (hA : A l = .det (.inc r l')) {v : Fin m → ℕ} {p : ℚ}
    (hG : G (some l, v, none))
    (h : PSem A oracle x G (some l', Function.update v r (v r + 1), none) p) :
    PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep] using h)

/-- A clear. -/
lemma PSem.clr {l l' : Λ} {r : Fin m} (hA : A l = .det (.clr r l')) {v : Fin m → ℕ} {p : ℚ}
    (hG : G (some l, v, none)) (h : PSem A oracle x G (some l', Function.update v r 0, none) p) :
    PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep] using h)

/-- A halving. -/
lemma PSem.half {l l' : Λ} {r : Fin m} (hA : A l = .det (.half r l')) {v : Fin m → ℕ}
    {p : ℚ} (hG : G (some l, v, none))
    (h : PSem A oracle x G (some l', Function.update v r (v r / 2), none) p) :
    PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep] using h)

/-- An equality test that succeeds. -/
lemma PSem.jeq_pos {l l₁ l₀ : Λ} {r s : Fin m} (hA : A l = .det (.jeq r s l₁ l₀))
    {v : Fin m → ℕ} {p : ℚ} (hG : G (some l, v, none)) (he : v r = v s)
    (h : PSem A oracle x G (some l₁, v, none) p) : PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep, if_pos he] using h)

/-- An equality test that fails. -/
lemma PSem.jeq_neg {l l₁ l₀ : Λ} {r s : Fin m} (hA : A l = .det (.jeq r s l₁ l₀))
    {v : Fin m → ℕ} {p : ℚ} (hG : G (some l, v, none)) (he : v r ≠ v s)
    (h : PSem A oracle x G (some l₀, v, none) p) : PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep, if_neg he] using h)

/-- A zero test that succeeds. -/
lemma PSem.jz_pos {l l₁ l₀ : Λ} {r : Fin m} (hA : A l = .det (.jz r l₁ l₀))
    {v : Fin m → ℕ} {p : ℚ} (hG : G (some l, v, none)) (he : v r = 0)
    (h : PSem A oracle x G (some l₁, v, none) p) : PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep, if_pos he] using h)

/-- A zero test that fails. -/
lemma PSem.jz_neg {l l₁ l₀ : Λ} {r : Fin m} (hA : A l = .det (.jz r l₁ l₀))
    {v : Fin m → ℕ} {p : ℚ} (hG : G (some l, v, none)) (he : v r ≠ 0)
    (h : PSem A oracle x G (some l₀, v, none) p) : PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep, if_neg he] using h)

/-- A parity test that succeeds. -/
lemma PSem.jodd_pos {l l₁ l₀ : Λ} {r : Fin m} (hA : A l = .det (.jodd r l₁ l₀))
    {v : Fin m → ℕ} {p : ℚ} (hG : G (some l, v, none)) (he : v r % 2 = 1)
    (h : PSem A oracle x G (some l₁, v, none) p) : PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep, if_pos he] using h)

/-- A parity test that fails. -/
lemma PSem.jodd_neg {l l₁ l₀ : Λ} {r : Fin m} (hA : A l = .det (.jodd r l₁ l₀))
    {v : Fin m → ℕ} {p : ℚ} (hG : G (some l, v, none)) (he : ¬ v r % 2 = 1)
    (h : PSem A oracle x G (some l₀, v, none) p) : PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep, if_neg he] using h)

/-- A `whole`-mode call on one register that answers `true`. -/
lemma PSem.call_pos {l l₁ l₀ : Λ} {j : Fin d} {r : Fin m}
    (hA : A l = .det (.call j .whole [r] l₁ l₀)) {v : Fin m → ℕ} {p : ℚ}
    (hG : G (some l, v, none)) (he : oracle j (pairEncode x (Nat.bits (v r))) = true)
    (h : PSem A oracle x G (some l₁, v, none) p) : PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep, vword_whole₁, he, if_true] using h)

/-- A `whole`-mode call on one register that answers `false`. -/
lemma PSem.call_neg {l l₁ l₀ : Λ} {j : Fin d} {r : Fin m}
    (hA : A l = .det (.call j .whole [r] l₁ l₀)) {v : Fin m → ℕ} {p : ℚ}
    (hG : G (some l, v, none)) (he : oracle j (pairEncode x (Nat.bits (v r))) = false)
    (h : PSem A oracle x G (some l₀, v, none) p) : PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep, vword_whole₁, he, Bool.false_eq_true, if_false] using h)

/-- An answer: `true` with probability `1` or `0`. -/
lemma PSem.ret {l : Λ} {b : Bool} (hA : A l = .det (.ret b)) {v : Fin m → ℕ}
    (hG : G (some l, v, none)) : PSem A oracle x G (some l, v, none) (if b then 1 else 0) :=
  have hh : PSem A oracle x G (none, v, some b) (if b then 1 else 0) := PSem.halted v b
  PSem.det hA hG (by simpa only [astep] using hh)

/-- A rejection: probability `0`. -/
lemma PSem.rej {l : Λ} (hA : A l = .det (.ret false)) {v : Fin m → ℕ}
    (hG : G (some l, v, none)) : PSem A oracle x G (some l, v, none) 0 :=
  (PSem.ret hA hG).congr (by simp)

/-- An acceptance: probability `1`. -/
lemma PSem.acc {l : Λ} (hA : A l = .det (.ret true)) {v : Fin m → ℕ}
    (hG : G (some l, v, none)) : PSem A oracle x G (some l, v, none) 1 :=
  (PSem.ret hA hG).congr (by simp)

/-- **The length-`N` form**: some length `N` halts every branch through the guard, with the
answers' probabilities `p` and `1 - p`. -/
theorem PSem.decides {a : AConf m Λ} {p : ℚ} (h : PSem A oracle x G a p) :
    ∃ N, NHalts A oracle x G a N ∧ ansProb A oracle x a N true = p ∧
      ansProb A oracle x a N false = 1 - p := by
  obtain ⟨N, hN⟩ := h.1.nhalts
  exact ⟨N, hN, h.2 N (hN.mono fun _ _ => trivial)⟩

end Semantics

/-! ## Generic loops -/

section Loops

variable (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool) (B : ℕ)

/-- **Copying a register** by counting the destination up to the source (the destination
starting at most the source): the semantics at the loop head is that at the exit with the
destination equal to the source. -/
theorem psem_copy (dst src : Fin m) (hne : dst ≠ src) (test bump ex : Λ)
    (htest : A test = .det (.jeq dst src ex bump)) (hbump : A bump = .det (.inc dst test))
    (p : ℚ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hle : v dst ≤ v src)
    (hK : PSem A oracle x (RegLe m Λ B) (some ex, Function.update v dst (v src), none) p) :
    PSem A oracle x (RegLe m Λ B) (some test, v, none) p := by
  generalize hk : v src - v dst = k
  induction k generalizing v with
  | zero =>
    have he : v dst = v src := by omega
    rw [← he, Function.update_eq_self] at hK
    exact PSem.jeq_pos htest hv he hK
  | succ k ih =>
    have hlt : v dst ≠ v src := by omega
    let v' := Function.update v dst (v dst + 1)
    have hv' : ∀ r, v' r ≤ B := register_update_le v dst B _ hv (by have := hv src; omega)
    have hs : v' src = v src := by simp [v', Function.update_of_ne hne.symm]
    have hd : v' dst = v dst + 1 := by simp [v']
    refine PSem.jeq_neg htest hv hlt (PSem.inc hbump hv ?_)
    refine ih v' hv' (by omega) ?_ (by omega)
    simpa only [hs, v', Function.update_idem] using hK

/-- **Adding twice a register**: the loop `test: if k = y exit; p += 2; k += 1; goto test`
(with `k`, `y`, `p` distinct), from `k ≤ y`, adds `2 (y - k)` to `p` and leaves `k = y`.

**Proof sketch.** Induction on `y - k`; each round is two increments of `p` and one of
`k`, all bounded by the final value of `p`. -/
theorem psem_addTwice (k y p : Fin m) (hky : k ≠ y) (hkp : k ≠ p) (hpy : p ≠ y)
    (test i₁ i₂ i₃ ex : Λ)
    (htest : A test = .det (.jeq k y ex i₁)) (h₁ : A i₁ = .det (.inc p i₂))
    (h₂ : A i₂ = .det (.inc p i₃)) (h₃ : A i₃ = .det (.inc k test))
    (q : ℚ) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hle : v k ≤ v y)
    (hb : v p + 2 * (v y - v k) ≤ B)
    (hK : PSem A oracle x (RegLe m Λ B)
      (some ex, Function.update (Function.update v p (v p + 2 * (v y - v k))) k (v y), none) q) :
    PSem A oracle x (RegLe m Λ B) (some test, v, none) q := by
  suffices H : ∀ c (v : Fin m → ℕ), (∀ r, v r ≤ B) → v k ≤ v y → v y - v k = c →
      v p + 2 * c ≤ B →
      PSem A oracle x (RegLe m Λ B)
        (some ex, Function.update (Function.update v p (v p + 2 * c)) k (v y), none) q →
      PSem A oracle x (RegLe m Λ B) (some test, v, none) q from
    H _ v hv hle rfl hb hK
  intro c
  induction c with
  | zero =>
    intro v hv hle hc _ hK
    have he : v k = v y := by omega
    simp only [Nat.mul_zero, Nat.add_zero, Function.update_eq_self, ← he] at hK
    exact PSem.jeq_pos htest hv he hK
  | succ c ih =>
    intro v hv hle hc hb hK
    have hne : v k ≠ v y := by omega
    let v₁ := Function.update v p (v p + 1)
    let v₂ := Function.update v₁ p (v₁ p + 1)
    let v₃ := Function.update v₂ k (v₂ k + 1)
    have hv₁ : ∀ r, v₁ r ≤ B := register_update_le v p B _ hv (by omega)
    have e₁ : v₁ p = v p + 1 := by simp [v₁]
    have hv₂ : ∀ r, v₂ r ≤ B := register_update_le v₁ p B _ hv₁ (by omega)
    have e₂k : v₂ k = v k := by simp [v₂, v₁, Function.update_of_ne hkp]
    have hv₃ : ∀ r, v₃ r ≤ B := register_update_le v₂ k B _ hv₂ (by
      rw [e₂k]; have := hv y; omega)
    have e₃k : v₃ k = v k + 1 := by simp [v₃, e₂k]
    have e₃y : v₃ y = v y := by
      simp [v₃, v₂, v₁, Function.update_of_ne hky.symm, Function.update_of_ne hpy.symm]
    have e₃p : v₃ p = v p + 2 := by
      simp [v₃, v₂, v₁, Function.update_of_ne hkp.symm]
    have hfin : Function.update (Function.update v₃ p (v₃ p + 2 * c)) k (v₃ y) =
        Function.update (Function.update v p (v p + 2 * (c + 1))) k (v y) := by
      rw [e₃p, e₃y]
      funext r
      by_cases hr : r = k
      · subst hr; simp
      · by_cases hp : r = p
        · subst hp; simp [Function.update_of_ne hkp.symm]; omega
        · simp [v₃, v₂, v₁, Function.update_of_ne hr, Function.update_of_ne hp]
    have hrest := ih v₃ hv₃ (by omega) (by omega) (by omega) (by rw [hfin]; exact hK)
    exact PSem.jeq_neg htest hv hne (PSem.inc h₁ hv (PSem.inc h₂ hv₁ (PSem.inc h₃ hv₂ hrest)))

end Loops

/-! ## Deterministic runs and searches -/

/-- **A deterministic run keeps the probabilistic semantics**: if the deterministic part runs
from `a` to a live configuration through the guard, the semantics at `a` is that at the end.

**Proof sketch.** Induction on the run length `T`. The deterministic part turns a `choose`
into `ret false`, and the answer slot stays `none` along a run ending live
(`astep_cases`), so every configuration before the end is live at a deterministic label;
each such step is `PSem.det`. -/
theorem PSem.of_areach {A : NARM m d Λ} {oracle : Fin d → List Bool → Bool}
    {G : AConf m Λ → Prop} {l' : Λ} {v' : Fin m → ℕ} {p : ℚ}
    (hp : PSem A oracle x G (some l', v', none) p) :
    ∀ (T : ℕ) (a : AConf m Λ), arun (A.detPart false) oracle x a T = (some l', v', none) →
      (∀ t < T, G (arun (A.detPart false) oracle x a t)) → PSem A oracle x G a p := by
  intro T
  induction T with
  | zero => intro a ha _; rw [show a = _ from ha]; exact hp
  | succ T ih =>
    intro a ha hG
    have hstuck : ∀ v res n, arun (A.detPart false) oracle x (none, v, res) n = (none, v, res) :=
      fun v res n => Function.iterate_fixed rfl n
    rcases a with ⟨_ | l, v, res⟩
    · rw [hstuck] at ha; cases ha
    · rw [arun, Function.iterate_succ_apply] at ha
      rcases astep_cases (A.detPart false) oracle l v res with ⟨l'', v'', he⟩ | ⟨b, he⟩
      · rw [he] at ha
        have hres : res = none := by
          have key : ∀ n (l₀ : Λ) (v₀ : Fin m → ℕ),
              arun (A.detPart false) oracle x (some l₀, v₀, res) n = (some l', v', none) →
                res = none := by
            intro n
            induction n with
            | zero => intro l₀ v₀ h; simp only [arun, Function.iterate_zero, id] at h; cases h; rfl
            | succ n ihn =>
              intro l₀ v₀ h
              rw [arun, Function.iterate_succ_apply] at h
              rcases astep_cases (A.detPart false) oracle l₀ v₀ res with ⟨l₁, v₁, e⟩ | ⟨b, e⟩
              · rw [e] at h; exact ihn l₁ v₁ h
              · rw [e] at h; rw [show ((astep (A.detPart false) oracle x)^[n] (none, v₀, some b))
                  = (none, v₀, some b) from Function.iterate_fixed rfl n] at h; cases h
          exact key T l'' v'' ha
        subst hres
        cases hA : A l with
        | choose l₁ l₀ =>
          have : astep (A.detPart false) oracle x (some l, v, none) = (none, v, some false) := by
            simp [astep, NARM.detPart_choose hA]
          rw [this] at he; cases he
        | det i =>
          have e : astep (A.detPart false) oracle x (some l, v, none) =
              astep (fun _ => i) oracle x (some l, v, none) := by
            rw [← nastep_det hA false false, nastep_det' hA]
          refine PSem.det hA (hG 0 (by omega)) ?_
          rw [← e, he]
          refine ih _ ha fun t ht => ?_
          have := hG (t + 1) (by omega)
          rwa [arun, Function.iterate_succ_apply, he] at this
      · rw [he, show ((astep (A.detPart false) oracle x)^[T] (none, v, some b)) = (none, v, some b)
          from Function.iterate_fixed rfl T] at ha
        cases ha

/-- The semantics transfers back along a run of the deterministic part (`AReach`). -/
theorem PSem.of_reach {A : NARM m d Λ} {oracle : Fin d → List Bool → Bool}
    {G : AConf m Λ → Prop} {a : AConf m Λ} {l' : Λ} {v' : Fin m → ℕ} {p : ℚ}
    (h : AReach (A.detPart false) oracle x G a (some l', v', none))
    (hp : PSem A oracle x G (some l', v', none) p) : PSem A oracle x G a p := by
  obtain ⟨T, hT, hG⟩ := h
  exact PSem.of_areach hp T a hT hG

/-- **Searching upwards**: from `r = c₀`, the loop `test: if P r goto yes else inc; inc: r++`
stops at the least `c ≥ c₀` with `P c`. -/
theorem searchUp_run (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
    (P : ℕ → Prop) [DecidablePred P] (test inc yes : Λ) (B : ℕ) (v : Fin m → ℕ)
    (hv : ∀ s, v s ≤ B)
    (htest : ∀ c', astep A oracle x (some test, Function.update v r c', none) =
      (some (if P c' then yes else inc), Function.update v r c', none))
    (hpre : ∀ w : Fin m → ℕ, PreS A x (some test, w, none)) (hinc : A inc = .inc r test)
    (c : ℕ) (hc : P c) (hcB : c ≤ B) :
    ∀ c₀, c₀ ≤ c → (∀ c', c₀ ≤ c' → c' < c → ¬ P c') →
      AReach A oracle x (GuardLe A x B) (some test, Function.update v r c₀, none)
        (some yes, Function.update v r c, none) := by
  intro c₀ hle hmin
  generalize hk : c - c₀ = k
  induction k generalizing c₀ with
  | zero =>
    have he : c₀ = c := by omega
    subst he
    refine AReach.step ⟨hpre _, register_update_le v r B _ hv hcB⟩ ?_
    rw [htest, if_pos hc]
    exact AReach.refl _
  | succ k ih =>
    have hlt : c₀ < c := by omega
    have hn : ¬ P c₀ := hmin _ le_rfl hlt
    have hb : ∀ s, Function.update v r c₀ s ≤ B := register_update_le v r B _ hv (by omega)
    refine AReach.step ⟨hpre _, hb⟩ ?_
    rw [htest, if_neg hn]
    refine AReach.step ⟨by simp [PreS, hinc], hb⟩ ?_
    simp only [astep, hinc, Function.update_self, Function.update_idem]
    exact ih (c₀ + 1) (by omega) (fun c' h1 h2 => hmin c' (by omega) h2) (by omega)

/-- **Searching downwards**: from `r = c₀`, the loop `dec: r--; test: if P r goto yes else
dec` stops at the greatest `c < c₀` with `P c`. -/
theorem searchDown_run (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
    (P : ℕ → Prop) [DecidablePred P] (dec test yes : Λ) (B : ℕ) (v : Fin m → ℕ)
    (hv : ∀ s, v s ≤ B)
    (htest : ∀ c', astep A oracle x (some test, Function.update v r c', none) =
      (some (if P c' then yes else dec), Function.update v r c', none))
    (hpre : ∀ w : Fin m → ℕ, PreS A x (some test, w, none)) (hdec : A dec = .dec r test)
    (c : ℕ) (hc : P c) :
    ∀ c₀, c < c₀ → c₀ ≤ B → (∀ c', c < c' → c' < c₀ → ¬ P c') →
      AReach A oracle x (GuardLe A x B) (some dec, Function.update v r c₀, none)
        (some yes, Function.update v r c, none) := by
  intro c₀ hlt hB hmax
  generalize hk : c₀ - (c + 1) = k
  induction k generalizing c₀ with
  | zero =>
    have he : c₀ - 1 = c := by omega
    have hb : ∀ s, Function.update v r c₀ s ≤ B := register_update_le v r B _ hv hB
    refine AReach.step ⟨by simp [PreS, hdec], hb⟩ ?_
    simp only [astep, hdec, Function.update_self, Function.update_idem, he]
    refine AReach.step ⟨hpre _, register_update_le v r B _ hv (by omega)⟩ ?_
    rw [htest, if_pos hc]
    exact AReach.refl _
  | succ k ih =>
    have hb : ∀ s, Function.update v r c₀ s ≤ B := register_update_le v r B _ hv hB
    have hn : ¬ P (c₀ - 1) := hmax _ (by omega) (by omega)
    refine AReach.step ⟨by simp [PreS, hdec], hb⟩ ?_
    simp only [astep, hdec, Function.update_self, Function.update_idem]
    refine AReach.step ⟨hpre _, register_update_le v r B _ hv (by omega)⟩ ?_
    rw [htest, if_neg hn]
    exact ih (c₀ - 1) (by omega) (by omega) (fun c' h1 h2 => hmax c' h1 (by omega)) (by omega)

section CallDec

variable {A : NARM m d Λ} {oracle : Fin d → List Bool → Bool} {G : AConf m Λ → Prop}

/-- A call: the semantics at the branch the oracle selects. -/
lemma PSem.call {l l₁ l₀ : Λ} {j : Fin d} {md : Mode} {args : List (Fin m)}
    (hA : A l = .det (.call j md args l₁ l₀)) {v : Fin m → ℕ} {p : ℚ} (hG : G (some l, v, none))
    (h : PSem A oracle x G (some (if oracle j (vword (callSegs ⟨j, md, args, l₁, l₀⟩ x
      (fun r => Nat.bits (v r)))) then l₁ else l₀), v, none) p) :
    PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep] using h)

/-- A decrement. -/
lemma PSem.dec {l l' : Λ} {r : Fin m} (hA : A l = .det (.dec r l')) {v : Fin m → ℕ} {p : ℚ}
    (hG : G (some l, v, none)) (h : PSem A oracle x G (some l', Function.update v r (v r - 1),
        none) p) :
    PSem A oracle x G (some l, v, none) p :=
  PSem.det hA hG (by simpa only [astep] using h)

end CallDec

end Complexity.LogProg
