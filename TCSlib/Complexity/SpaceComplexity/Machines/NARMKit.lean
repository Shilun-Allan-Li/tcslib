/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.NARM
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proving nondeterministic register machines correct by continuation

The combinators of `TCSlib.Complexity.SpaceComplexity.Machines.NARM` (`NHalts`, `NAns`) fix
the length `N` of the choice words in advance, which is awkward for loops whose length
depends on earlier guesses. This file proves machines correct without explicit lengths:

* `Complexity.LogProg.NTerm` — every branch terminates, through configurations meeting a
  guard (an inductive, well-founded predicate);
* `Complexity.LogProg.NAcc` — some choice word, of any length, halts with answer `true`;
* `Complexity.LogProg.NSem a P` — both: every branch from `a` terminates, and some branch
  accepts iff `P`.

Since every configuration has only two successors, termination of every branch gives a
uniform length bound (`Complexity.LogProg.NTerm.nhalts`, by induction on the inductive
termination predicate), and then `NAcc` agrees with `NAns` at that length
(`Complexity.LogProg.NSem.decides`) — the form `narm_decides` consumes. Machine-specific
loop lemmas are proved in continuation-passing style: the semantics at a loop head is
derived from the semantics at its exits. Three generic loops are included: guessing a value
below a register bound (`nsem_guess`), copying a register (`nsem_copy`), and adding twice a
register to another (`nsem_addTwice`).

This is infrastructure for [AB09, §4.3] (nondeterministic logspace algorithms), not itself a
result of the book; it is written for `Complexity.PATH_mem_NL`.

## Main definitions

* `Complexity.LogProg.NTerm`, `Complexity.LogProg.NAcc`, `Complexity.LogProg.NSem`.
* `Complexity.LogProg.RegLe` — the register-bound guard.

## Main results

* `Complexity.LogProg.NTerm.nhalts`, `Complexity.LogProg.NSem.decides`.
* the step lemmas `NSem.det`, `NSem.choose`, `NSem.inc`, `NSem.clr`, `NSem.half`,
  `NSem.jeq_pos`, `NSem.jeq_neg`, `NSem.jz_pos`, `NSem.jz_neg`, `NSem.jodd_pos`,
  `NSem.jodd_neg`, `NSem.call_pos`, `NSem.call_neg`, `NSem.ret`.
* the loops `Complexity.LogProg.nsem_guess`, `Complexity.LogProg.nsem_copy`,
  `Complexity.LogProg.nsem_addTwice`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- **Every branch terminates** from a configuration, through live configurations satisfying
the guard `G`: a halted configuration terminates, and a live one satisfying `G` terminates if
both of its successors do. -/
inductive NTerm (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) : AConf m Λ → Prop
  /-- a halted configuration -/
  | halted (v : Fin m → ℕ) (res : Option Bool) : NTerm A oracle x G (none, v, res)
  /-- a live configuration satisfying the guard, both of whose successors terminate -/
  | step (l : Λ) (v : Fin m → ℕ) (res : Option Bool) (hG : G (some l, v, res))
      (h : ∀ b, NTerm A oracle x G (nastep A oracle x b (some l, v, res))) :
      NTerm A oracle x G (some l, v, res)

/-- **Some branch accepts**: some choice word, of any length, halts the machine from `a` with
the answer `true`. -/
def NAcc (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (a : AConf m Λ) : Prop :=
  ∃ σ : List Bool, (narun A oracle x σ a).1 = none ∧ (narun A oracle x σ a).2.2 = some true

/-- **The semantics of a configuration**: every branch from `a` terminates through the guard
`G`, and some branch accepts iff `P`. -/
def NSem (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a : AConf m Λ) (P : Prop) : Prop :=
  NTerm A oracle x G a ∧ (NAcc A oracle x a ↔ P)

/-- The register-bound guard: every register value is at most `B`. -/
def RegLe (m : ℕ) (Λ : Type) (B : ℕ) (a : AConf m Λ) : Prop := ∀ r, a.2.1 r ≤ B

section Semantics

variable {A : NARM m d Λ} {oracle : Fin d → List Bool → Bool} {G : AConf m Λ → Prop}

/-- **Termination of every branch gives a uniform length bound**: if every branch terminates
from `a`, then for some `N` every choice word of length `N` halts the machine.

**Proof sketch.** Induction on `NTerm`; at a live configuration take one more than the
larger of the bounds of the two successors (`NHalts.mono_len`), the guard at time `0` being
the hypothesis. -/
theorem NTerm.nhalts {a : AConf m Λ} (h : NTerm A oracle x G a) :
    ∃ N, NHalts A oracle x G a N := by
  induction h with
  | halted v res => exact ⟨0, NHalts.halted v res 0⟩
  | step l v res hG _ ih =>
    obtain ⟨N₁, h₁⟩ := ih true
    obtain ⟨N₀, h₀⟩ := ih false
    refine ⟨max N₁ N₀ + 1, fun σ hσ => ?_⟩
    obtain ⟨b, σ', rfl⟩ : ∃ b σ', σ = b :: σ' := by
      cases σ with
      | nil => simp at hσ
      | cons b σ' => exact ⟨b, σ', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hσ
    have hb : NHalts A oracle x G (nastep A oracle x b (some l, v, res)) (max N₁ N₀) := by
      cases b
      · exact h₀.mono_len (le_max_right _ _)
      · exact h₁.mono_len (le_max_left _ _)
    obtain ⟨h1, h2⟩ := hb σ' hσ
    refine ⟨by rw [narun_cons]; exact h1, fun t ht hl => ?_⟩
    cases t with
    | zero => simpa using hG
    | succ t =>
      simp only [List.take_succ_cons, narun_cons] at hl ⊢
      exact h2 t (by omega) hl

/-- A halted configuration accepts iff its answer is `true`. -/
lemma nacc_halted (v : Fin m → ℕ) (res : Option Bool) :
    NAcc A oracle x (none, v, res) ↔ res = some true := by
  constructor
  · rintro ⟨σ, -, h⟩; simpa using h
  · intro h; exact ⟨[], rfl, h⟩

/-- A live configuration accepts iff one of its successors does. -/
lemma nacc_live (l : Λ) (v : Fin m → ℕ) :
    NAcc A oracle x (some l, v, none) ↔
      ∃ b, NAcc A oracle x (nastep A oracle x b (some l, v, none)) := by
  constructor
  · rintro ⟨σ, h1, h2⟩
    cases σ with
    | nil => simp at h1
    | cons b σ => exact ⟨b, σ, h1, h2⟩
  · rintro ⟨b, σ, h1, h2⟩
    exact ⟨b :: σ, h1, h2⟩

/-- At a deterministic label a step does not depend on the choice bit. -/
lemma nastep_det' {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) (b : Bool) (v : Fin m → ℕ)
    (res : Option Bool) :
    nastep A oracle x b (some l, v, res) = astep (fun _ => i) oracle x (some l, v, res) := by
  simp only [nastep, hA]

/-- **Semantics transfer along an equivalence of the predicate.** -/
lemma NSem.congr {a : AConf m Λ} {P Q : Prop} (h : NSem A oracle x G a P) (hPQ : P ↔ Q) :
    NSem A oracle x G a Q :=
  ⟨h.1, h.2.trans hPQ⟩

/-- A halted configuration answering `b` accepts iff `b = true`. -/
lemma NSem.halted (v : Fin m → ℕ) (b : Bool) :
    NSem A oracle x G (none, v, some b) (b = true) :=
  ⟨NTerm.halted v _, by rw [nacc_halted]; cases b <;> simp⟩

/-- **A deterministic step.** -/
lemma NSem.det {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) {v : Fin m → ℕ} {P : Prop}
    (hG : G (some l, v, none))
    (h : NSem A oracle x G (astep (fun _ => i) oracle x (some l, v, none)) P) :
    NSem A oracle x G (some l, v, none) P := by
  refine ⟨NTerm.step l v none hG fun b => ?_, ?_⟩
  · rw [nastep_det' hA]; exact h.1
  · rw [nacc_live]
    simp only [nastep_det' hA]
    exact ⟨fun ⟨_, h'⟩ => h.2.mp h', fun hp => ⟨false, h.2.mpr hp⟩⟩

/-- **A `choose`**: some branch accepts iff some branch from either target does. -/
lemma NSem.choose {l l₁ l₀ : Λ} (hA : A l = .choose l₁ l₀) {v : Fin m → ℕ} {P₁ P₀ : Prop}
    (hG : G (some l, v, none)) (h₁ : NSem A oracle x G (some l₁, v, none) P₁)
    (h₀ : NSem A oracle x G (some l₀, v, none) P₀) :
    NSem A oracle x G (some l, v, none) (P₁ ∨ P₀) := by
  have e : ∀ b, nastep A oracle x b (some l, v, none) =
      (some (if b then l₁ else l₀), v, none) := fun b => nastep_choose hA b v none
  refine ⟨NTerm.step l v none hG fun b => ?_, ?_⟩
  · rw [e]; cases b
    · exact h₀.1
    · exact h₁.1
  · rw [nacc_live]
    simp only [e]
    constructor
    · rintro ⟨b, hb⟩
      cases b
      · exact Or.inr (h₀.2.mp hb)
      · exact Or.inl (h₁.2.mp hb)
    · rintro (hp | hp)
      · exact ⟨true, h₁.2.mpr hp⟩
      · exact ⟨false, h₀.2.mpr hp⟩

/-- An increment. -/
lemma NSem.inc {l l' : Λ} {r : Fin m} (hA : A l = .det (.inc r l')) {v : Fin m → ℕ} {P : Prop}
    (hG : G (some l, v, none))
    (h : NSem A oracle x G (some l', Function.update v r (v r + 1), none) P) :
    NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep] using h)

/-- A clear. -/
lemma NSem.clr {l l' : Λ} {r : Fin m} (hA : A l = .det (.clr r l')) {v : Fin m → ℕ} {P : Prop}
    (hG : G (some l, v, none)) (h : NSem A oracle x G (some l', Function.update v r 0, none) P) :
    NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep] using h)

/-- A halving. -/
lemma NSem.half {l l' : Λ} {r : Fin m} (hA : A l = .det (.half r l')) {v : Fin m → ℕ}
    {P : Prop} (hG : G (some l, v, none))
    (h : NSem A oracle x G (some l', Function.update v r (v r / 2), none) P) :
    NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep] using h)

/-- An equality test that succeeds. -/
lemma NSem.jeq_pos {l l₁ l₀ : Λ} {r s : Fin m} (hA : A l = .det (.jeq r s l₁ l₀))
    {v : Fin m → ℕ} {P : Prop} (hG : G (some l, v, none)) (he : v r = v s)
    (h : NSem A oracle x G (some l₁, v, none) P) : NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep, if_pos he] using h)

/-- An equality test that fails. -/
lemma NSem.jeq_neg {l l₁ l₀ : Λ} {r s : Fin m} (hA : A l = .det (.jeq r s l₁ l₀))
    {v : Fin m → ℕ} {P : Prop} (hG : G (some l, v, none)) (he : v r ≠ v s)
    (h : NSem A oracle x G (some l₀, v, none) P) : NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep, if_neg he] using h)

/-- A zero test that succeeds. -/
lemma NSem.jz_pos {l l₁ l₀ : Λ} {r : Fin m} (hA : A l = .det (.jz r l₁ l₀))
    {v : Fin m → ℕ} {P : Prop} (hG : G (some l, v, none)) (he : v r = 0)
    (h : NSem A oracle x G (some l₁, v, none) P) : NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep, if_pos he] using h)

/-- A zero test that fails. -/
lemma NSem.jz_neg {l l₁ l₀ : Λ} {r : Fin m} (hA : A l = .det (.jz r l₁ l₀))
    {v : Fin m → ℕ} {P : Prop} (hG : G (some l, v, none)) (he : v r ≠ 0)
    (h : NSem A oracle x G (some l₀, v, none) P) : NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep, if_neg he] using h)

/-- A parity test that succeeds. -/
lemma NSem.jodd_pos {l l₁ l₀ : Λ} {r : Fin m} (hA : A l = .det (.jodd r l₁ l₀))
    {v : Fin m → ℕ} {P : Prop} (hG : G (some l, v, none)) (he : v r % 2 = 1)
    (h : NSem A oracle x G (some l₁, v, none) P) : NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep, if_pos he] using h)

/-- A parity test that fails. -/
lemma NSem.jodd_neg {l l₁ l₀ : Λ} {r : Fin m} (hA : A l = .det (.jodd r l₁ l₀))
    {v : Fin m → ℕ} {P : Prop} (hG : G (some l, v, none)) (he : ¬ v r % 2 = 1)
    (h : NSem A oracle x G (some l₀, v, none) P) : NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep, if_neg he] using h)

/-- A `whole`-mode call on one register that answers `true`. -/
lemma NSem.call_pos {l l₁ l₀ : Λ} {j : Fin d} {r : Fin m}
    (hA : A l = .det (.call j .whole [r] l₁ l₀)) {v : Fin m → ℕ} {P : Prop}
    (hG : G (some l, v, none)) (he : oracle j (pairEncode x (Nat.bits (v r))) = true)
    (h : NSem A oracle x G (some l₁, v, none) P) : NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep, vword_whole₁, he, if_true] using h)

/-- A `whole`-mode call on one register that answers `false`. -/
lemma NSem.call_neg {l l₁ l₀ : Λ} {j : Fin d} {r : Fin m}
    (hA : A l = .det (.call j .whole [r] l₁ l₀)) {v : Fin m → ℕ} {P : Prop}
    (hG : G (some l, v, none)) (he : oracle j (pairEncode x (Nat.bits (v r))) = false)
    (h : NSem A oracle x G (some l₀, v, none) P) : NSem A oracle x G (some l, v, none) P :=
  NSem.det hA hG (by simpa only [astep, vword_whole₁, he, Bool.false_eq_true, if_false] using h)

/-- An answer: some branch accepts iff the answer is `true`. -/
lemma NSem.ret {l : Λ} {b : Bool} (hA : A l = .det (.ret b)) {v : Fin m → ℕ}
    (hG : G (some l, v, none)) : NSem A oracle x G (some l, v, none) (b = true) := by
  have hh : NSem A oracle x G (none, v, some b) (b = true) := NSem.halted v b
  exact NSem.det hA hG (by simpa only [astep] using hh)

/-- **Semantics gives the decision interface**: if every branch from `a` terminates through
`G` and some branch accepts iff `P`, then for some `N` every choice word of length `N` halts
through `G`, and `P` holds iff some choice word of length `N` answers `true`.

**Proof sketch.** `NTerm.nhalts` gives `N`. An accepting word shorter than `N` is padded (the
run is halted); a longer one is cut to its prefix of length `N`, after which the run is
halted already; conversely a word of length `N` answering `true` is halted, hence accepting. -/
theorem NSem.decides {a : AConf m Λ} {P : Prop} (h : NSem A oracle x G a P) :
    ∃ N, NHalts A oracle x G a N ∧ (P ↔ NAns A oracle x a N true) := by
  obtain ⟨N, hN⟩ := h.1.nhalts
  refine ⟨N, hN, h.2.symm.trans ⟨?_, ?_⟩⟩
  swap
  · rintro ⟨σ, hσ, h2⟩
    exact ⟨σ, (hN σ hσ).1, h2⟩
  rintro ⟨σ, h1, h2⟩
  rcases Nat.lt_or_ge σ.length N with hl | hl
  · refine ⟨σ ++ List.replicate (N - σ.length) false, by simp; omega, ?_⟩
    rwa [narun_append_of_halted h1]
  · have hlen : (σ.take N).length = N := by simp; omega
    refine ⟨σ.take N, hlen, ?_⟩
    rwa [← List.take_append_drop N σ, narun_append_of_halted (hN _ hlen).1] at h2

end Semantics

/-! ## Generic loops -/

section Loops

variable (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool) (B : ℕ)

/-- **Guessing a value below a bound**: the loop `test: if g = nr reject; ch: choose (exit,
more); more: g := g + 1; goto test` has, from `g ≤ nr`, an accepting branch iff some value
`j ∈ [g, nr)` has an accepting branch from the exit with `g := j`; every branch terminates.

**Proof sketch.** Induction on `nr - g`: at `g = nr` the test rejects; otherwise the choice
either exits with the current value or increments and recurs. -/
theorem nsem_guess (g nr : Fin m) (hgn : g ≠ nr) (test ch more ex rej : Λ)
    (htest : A test = .det (.jeq g nr rej ch)) (hch : A ch = .choose ex more)
    (hmore : A more = .det (.inc g test)) (hrej : A rej = .det (.ret false))
    (Q : ℕ → Prop) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hle : v g ≤ v nr)
    (hK : ∀ j, v g ≤ j → j < v nr →
      NSem A oracle x (RegLe m Λ B) (some ex, Function.update v g j, none) (Q j)) :
    NSem A oracle x (RegLe m Λ B) (some test, v, none) (∃ j, v g ≤ j ∧ j < v nr ∧ Q j) := by
  generalize hk : v nr - v g = k
  induction k generalizing v with
  | zero =>
    have he : v g = v nr := by omega
    refine (NSem.jeq_pos htest hv he (NSem.ret hrej hv)).congr ?_
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro j h1 h2; omega
  | succ k ih =>
    have hne : v g ≠ v nr := by omega
    let v' := Function.update v g (v g + 1)
    have hv' : ∀ r, v' r ≤ B := register_update_le v g B _ hv (by have := hv nr; omega)
    have hg' : v' g = v g + 1 := by simp [v']
    have hn' : v' nr = v nr := by simp [v', Function.update_of_ne hgn.symm]
    have hrec := ih v' hv' (by omega)
      (fun j h1 h2 => by
        have := hK j (by omega) (by omega)
        simpa only [v', Function.update_idem] using this)
      (by omega)
    rw [hg', hn'] at hrec
    have hstay := hK (v g) le_rfl (by omega)
    rw [Function.update_eq_self] at hstay
    refine (NSem.jeq_neg htest hv hne
      (NSem.choose hch hv hstay (NSem.inc hmore hv hrec))).congr ?_
    constructor
    · rintro (h | ⟨j, h1, h2, h3⟩)
      · exact ⟨v g, le_rfl, by omega, h⟩
      · exact ⟨j, by omega, h2, h3⟩
    · rintro ⟨j, h1, h2, h3⟩
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · exact Or.inl (h ▸ h3)
      · exact Or.inr ⟨j, h, h2, h3⟩

/-- **Copying a register** by counting the destination up to the source (the destination
starting at most the source): the semantics at the loop head is that at the exit with the
destination equal to the source.

**Proof sketch.** Induction on the difference: equality exits, otherwise increment. -/
theorem nsem_copy (dst src : Fin m) (hne : dst ≠ src) (test bump ex : Λ)
    (htest : A test = .det (.jeq dst src ex bump)) (hbump : A bump = .det (.inc dst test))
    (P : Prop) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hle : v dst ≤ v src)
    (hK : NSem A oracle x (RegLe m Λ B) (some ex, Function.update v dst (v src), none) P) :
    NSem A oracle x (RegLe m Λ B) (some test, v, none) P := by
  generalize hk : v src - v dst = k
  induction k generalizing v with
  | zero =>
    have he : v dst = v src := by omega
    rw [← he, Function.update_eq_self] at hK
    exact NSem.jeq_pos htest hv he hK
  | succ k ih =>
    have hlt : v dst ≠ v src := by omega
    let v' := Function.update v dst (v dst + 1)
    have hv' : ∀ r, v' r ≤ B := register_update_le v dst B _ hv (by have := hv src; omega)
    have hs : v' src = v src := by simp [v', Function.update_of_ne hne.symm]
    have hd : v' dst = v dst + 1 := by simp [v']
    refine NSem.jeq_neg htest hv hlt (NSem.inc hbump hv ?_)
    refine ih v' hv' (by omega) ?_ (by omega)
    simpa only [hs, v', Function.update_idem] using hK

/-- **Adding twice a register**: the loop `test: if k = y exit; p += 2; k += 1; goto test`
(with `k`, `y`, `p` distinct), from `k ≤ y`, adds `2 (y - k)` to `p` and leaves `k = y`.

**Proof sketch.** Induction on `y - k`; each round is two increments of `p` and one of
`k`, all bounded by the final value of `p`. -/
theorem nsem_addTwice (k y p : Fin m) (hky : k ≠ y) (hkp : k ≠ p) (hpy : p ≠ y)
    (test i₁ i₂ i₃ ex : Λ)
    (htest : A test = .det (.jeq k y ex i₁)) (h₁ : A i₁ = .det (.inc p i₂))
    (h₂ : A i₂ = .det (.inc p i₃)) (h₃ : A i₃ = .det (.inc k test))
    (P : Prop) (v : Fin m → ℕ) (hv : ∀ r, v r ≤ B) (hle : v k ≤ v y)
    (hb : v p + 2 * (v y - v k) ≤ B)
    (hK : NSem A oracle x (RegLe m Λ B)
      (some ex, Function.update (Function.update v p (v p + 2 * (v y - v k))) k (v y), none) P) :
    NSem A oracle x (RegLe m Λ B) (some test, v, none) P := by
  suffices H : ∀ c (v : Fin m → ℕ), (∀ r, v r ≤ B) → v k ≤ v y → v y - v k = c →
      v p + 2 * c ≤ B →
      NSem A oracle x (RegLe m Λ B)
        (some ex, Function.update (Function.update v p (v p + 2 * c)) k (v y), none) P →
      NSem A oracle x (RegLe m Λ B) (some test, v, none) P from
    H _ v hv hle rfl hb hK
  intro c
  induction c with
  | zero =>
    intro v hv hle hc _ hK
    have he : v k = v y := by omega
    simp only [Nat.mul_zero, Nat.add_zero, Function.update_eq_self, ← he] at hK
    exact NSem.jeq_pos htest hv he hK
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
    exact NSem.jeq_neg htest hv hne (NSem.inc h₁ hv (NSem.inc h₂ hv₁ (NSem.inc h₃ hv₂ hrest)))

end Loops

end Complexity.LogProg
