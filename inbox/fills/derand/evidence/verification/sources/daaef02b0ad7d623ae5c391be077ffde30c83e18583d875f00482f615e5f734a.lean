/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.NARMCompile
import TCSlib.Complexity.SpaceComplexity.NSPACE

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic abstract register machines decide in small space

The run theorem for nondeterministic abstract register machines
(`Complexity.LogProg.narm_run`): if every choice word of length `N` halts the abstract machine
from `(l, v)`, through configurations meeting the preconditions with register values of at
most `W` binary digits, then there is `T` such that every branch of length `T` of the compiled
nondeterministic machine (`Complexity.LogProg.ncompileTM`) halts, staying within register
range `[-1, W]` and decider range `[-B, B]`, every branch answers what some abstract choice
word answers, and every abstract answer is the output of some branch. The space theorem
`Complexity.LogProg.narm_space` packages this in the form required by
`Turing.FinNDTM.DecidesInSpace`: all branches halt, all use at most
`m (W + 2) + kD (2B + 1)` work cells, and some branch accepts iff some abstract choice word
answers `true`.

This is infrastructure for [AB09, §4.1–4.3] (nondeterministic logspace algorithms described
by "guessing"), not itself a result of the book.

## Main definitions

* `Complexity.LogProg.NGood` — every branch of a given length halts in a box, its final
  configuration satisfying a predicate.

## Main results

* `Complexity.LogProg.narm_run`, `Complexity.LogProg.narm_space`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definition 4.1.)
-/

namespace Complexity.LogProg

open Turing

section Good

variable {K : ℕ} {St : Type} {x : List Bool}

/-- Every choice word of length at most `T` drives `N` from `C` into the box, and every word
of length exactly `T` to a halted configuration satisfying `Q`. -/
def NGood (N : NDTM K Bool St) (C : Cfg K Bool St x) (T : ℕ) (box Q : Cfg K Bool St x → Prop) :
    Prop :=
  (∀ u : List Bool, u.length ≤ T → box (N.runWith u C)) ∧
    ∀ w : List Bool, w.length = T → (N.runWith w C).state = none ∧ Q (N.runWith w C)

variable {N : NDTM K Bool St} {box Q : Cfg K Bool St x → Prop}

/-- A run halted under a prefix stays put under any extension. -/
lemma runWith_append_of_halt {C : Cfg K Bool St x} {u : List Bool}
    (h : (N.runWith u C).state = none) (v : List Bool) : N.runWith (u ++ v) C = N.runWith u C := by
  rw [NDTM.runWith_append, NDTM.runWith_of_halt _ h]

/-- A good run for a final predicate is a good run for any weaker final predicate. -/
lemma NGood.imp {C : Cfg K Bool St x} {T : ℕ} {Q' : Cfg K Bool St x → Prop}
    (h : NGood N C T box Q) (hQ : ∀ c, Q c → Q' c) : NGood N C T box Q' :=
  ⟨h.1, fun w hw => ⟨(h.2 w hw).1, hQ _ (h.2 w hw).2⟩⟩

/-- **`NGood` is monotone in the length**: branches halted at `T` stay put. -/
lemma NGood.mono {C : Cfg K Bool St x} {T T' : ℕ} (h : NGood N C T box Q) (hT : T ≤ T') :
    NGood N C T' box Q := by
  have key : ∀ u : List Bool, T ≤ u.length → N.runWith u C = N.runWith (u.take T) C := by
    intro u hu
    conv_lhs => rw [← List.take_append_drop T u]
    exact runWith_append_of_halt (h.2 _ (by simp; omega)).1 _
  refine ⟨fun u hu => ?_, fun w hw => ?_⟩
  · rcases Nat.lt_or_ge u.length T with h' | h'
    · exact h.1 u h'.le
    · rw [key u h']; exact h.1 _ (by simp)
  · rw [key w (by omega)]; exact h.2 _ (by simp; omega)

/-- **A segment followed by a good run**: if every word of length `S` drives `N` from `C` to
`C'`, staying in the box, and `N` is good from `C'` for `T`, it is good from `C` for `S + T`. -/
lemma NGood.seg {C C' : Cfg K Bool St x} {S T : ℕ}
    (hbox : ∀ u : List Bool, u.length ≤ S → box (N.runWith u C))
    (heq : ∀ u : List Bool, u.length = S → N.runWith u C = C') (h : NGood N C' T box Q) :
    NGood N C (S + T) box Q := by
  have key : ∀ u : List Bool, S ≤ u.length → N.runWith u C = N.runWith (u.drop S) C' := by
    intro u hu
    conv_lhs => rw [← List.take_append_drop S u]
    rw [NDTM.runWith_append, heq _ (by simp; omega)]
  refine ⟨fun u hu => ?_, fun w hw => ?_⟩
  · rcases Nat.lt_or_ge u.length S with h' | h'
    · exact hbox u h'.le
    · rw [key u h']; exact h.1 _ (by simp; omega)
  · rw [key w (by omega)]; exact h.2 _ (by simp; omega)

/-- **A choice followed by good runs**: if `C` is in the box, the step under bit `b` leads to
`Cb b`, and `N` is good from each `Cb b` for `T`, it is good from `C` for `T + 1`. -/
lemma NGood.choose {C : Cfg K Bool St x} {Cb : Bool → Cfg K Bool St x} {T : ℕ} (hC : box C)
    (hstep : ∀ b, N.stepWith b C = Cb b) (h : ∀ b, NGood N (Cb b) T box Q) :
    NGood N C (T + 1) box Q := by
  refine ⟨fun u hu => ?_, fun w hw => ?_⟩
  · cases u with
    | nil => exact hC
    | cons b u =>
      rw [NDTM.runWith_cons, hstep]
      exact (h b).1 u (by simp at hu; omega)
  · cases w with
    | nil => simp at hw
    | cons b w =>
      rw [NDTM.runWith_cons, hstep]
      exact (h b).2 w (by simpa using hw)

end Good

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- The guard of the nondeterministic run theorem: the preconditions of the step, and register
values of at most `W` binary digits (counting one increment). -/
def NGuard (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B W : ℕ) (x : List Bool) (a : AConf m Λ) : Prop :=
  NPre A oracle D q0 B x a ∧ ∀ r, ((Nat.bits (a.2.1 r + 1)).length : ℤ) ≤ W

/-- **The run theorem for nondeterministic abstract register machines.** If every choice word
of length `N` halts the abstract machine from `(l, v)` through configurations satisfying
`NGuard` (preconditions, register widths `≤ W`), then for some `T` every branch of length
`T` of the compiled nondeterministic machine, from the compiled configuration of `(l, v)`
having written `out`, halts in the box (register heads in `[-1, W]`, decider heads in
`[-B, B]`) with output `out ++ [b]` for an abstract answer `b` (`NAns … N b`), and every
abstract answer is the output of some branch of length `T`.

**Proof sketch.** Induction on `N`. At a deterministic label the first abstract step is
either live (`ndet_live`, then the induction hypothesis, `NGood.seg`) or halting
(`ndet_halt`); at a `choose` both targets satisfy the induction hypothesis
(`NHalts.of_choose`), the two lengths are equalized (`NGood.mono`), and the first compiled
step follows the choice bit (`ncompileTM_stepWith_choose`, `NGood.choose`). The answers are
tracked by `nans_det`, `nans_choose`, `nans_halted`. -/
theorem narm_run (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) :
    ∀ (N : ℕ) (l : Λ) (v : Fin m → ℕ) (out : List Bool),
      NHalts A oracle x (NGuard A oracle D q0 B W x) (some l, v, none) N →
      ∃ T, NGood (ncompileTM A l₀ D q0) (seam (aseam x l v out)) T (NBox W B)
          (fun c => ∃ b, NAns A oracle x (some l, v, none) N b ∧ c.output = out ++ [b]) ∧
        ∀ b, NAns A oracle x (some l, v, none) N b → ∃ w : List Bool, w.length = T ∧
          ((ncompileTM A l₀ D q0).runWith w (seam (aseam x l v out))).output = out ++ [b] := by
  intro N
  induction N with
  | zero =>
    intro l v out h
    have := (h [] rfl).1
    simp at this
  | succ N ih =>
    intro l v out h
    obtain ⟨hp, hw⟩ := h.guard
    cases hA : A l with
    | det i =>
      rcases astep_cases (x := x) (A.detPart false) oracle l v none with ⟨l', v', hs⟩ | ⟨b₀, hs⟩
      · -- a live deterministic step
        have h' := h.of_det hA false
        rw [hs] at h'
        obtain ⟨T, hgood, hex⟩ := ih l' v' out h'
        obtain ⟨S, hbox, heq⟩ := ndet_live A l₀ oracle D q0 B W l l' v v' out hs hp hw
        have hans : ∀ b, NAns A oracle x (some l, v, none) (N + 1) b ↔
            NAns A oracle x (some l', v', none) N b := by
          intro b; rw [nans_det hA false, hs]
        refine ⟨S + T, NGood.seg hbox heq (hgood.imp fun c ⟨b, hb, hc⟩ =>
          ⟨b, (hans b).2 hb, hc⟩), fun b hb => ?_⟩
        obtain ⟨w, hw', hwo⟩ := hex b ((hans b).1 hb)
        refine ⟨List.replicate S false ++ w, by simp [hw'], ?_⟩
        rw [NDTM.runWith_append, heq _ (by simp)]
        exact hwo
      · -- a halting deterministic step
        obtain ⟨S, Cf, hbox, heq, hst, hout⟩ :=
          ndet_halt A l₀ oracle D q0 B W l hA v out b₀ hs hp hw
        have hans : ∀ b, NAns A oracle x (some l, v, none) (N + 1) b ↔ b₀ = b := by
          intro b; rw [nans_det hA false, hs, nans_halted]; simp
        refine ⟨S, ⟨hbox, fun w hw' => ?_⟩, fun b hb => ?_⟩
        · rw [heq w hw']
          exact ⟨hst, b₀, (hans b₀).2 rfl, hout⟩
        · obtain rfl := (hans b).1 hb
          exact ⟨List.replicate S false, by simp, by rw [heq _ (by simp)]; exact hout⟩
    | choose l₁ l₀' =>
      have key := fun b : Bool => ih (if b then l₁ else l₀') v out (h.of_choose hA b)
      choose T hgood hex using key
      have hans : ∀ b, NAns A oracle x (some l, v, none) (N + 1) b ↔
          ∃ c : Bool, NAns A oracle x (some (if c then l₁ else l₀'), v, none) N b := by
        intro b
        rw [nans_choose hA]
        constructor
        · rintro (h1 | h0)
          · exact ⟨true, by simpa using h1⟩
          · exact ⟨false, by simpa using h0⟩
        · rintro ⟨c, hc⟩
          cases c
          · exact Or.inr (by simpa using hc)
          · exact Or.inl (by simpa using hc)
      set Tm := max (T true) (T false) with hTm
      have hle : ∀ c, T c ≤ Tm := fun c => by cases c <;> simp [hTm]
      refine ⟨Tm + 1, NGood.choose (nbox_seam W B l v out)
        (fun c => ncompileTM_stepWith_choose A l₀ D q0 hA c v out)
        (fun c => ((hgood c).mono (hle c)).imp fun cf ⟨b, hb, hcf⟩ =>
          ⟨b, (hans b).2 ⟨c, hb⟩, hcf⟩), fun b hb => ?_⟩
      obtain ⟨c, hc⟩ := (hans b).1 hb
      obtain ⟨w, hw', hwo⟩ := hex c b hc
      refine ⟨c :: (w ++ List.replicate (Tm - T c) false), by simp [hw']; have := hle c; omega,
        ?_⟩
      rw [NDTM.runWith_cons, ncompileTM_stepWith_choose A l₀ D q0 hA c v out,
        runWith_append_of_halt ((hgood c).2 w hw').1]
      exact hwo

/-- **Nondeterministic abstract register machines decide in small space.** If every choice
word of length `N` halts the abstract machine, started at `l₀` with all registers `0`, on
input `x`, through configurations meeting the preconditions with values of at most `W` binary
digits (counting one increment), then for some `T` every branch of length `T` of the compiled
nondeterministic machine halts, visiting at most `m (W + 2) + kD (2B + 1)` work cells, and
some branch accepts iff some choice word of length `N` answers `true`.

**Proof sketch.** `narm_run` from the initial configuration (`ncompileTM_init`); the space of
each branch is bounded by its head ranges (`spaceUsedWith_le_of_ranges`), the register tapes
and the decider tapes being the two blocks of `Fin (m + kD)`. -/
theorem narm_space [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B W N : ℕ)
    (h : NHalts A oracle x (NGuard A oracle D q0 B W x) (some l₀, fun _ => 0, none) N) :
    ∃ T, (ncompileFinNDTM A l₀ D q0).tm.HaltsWithin x T ∧
      (∀ w : List Bool, w.length = T →
        (ncompileFinNDTM A l₀ D q0).tm.spaceUsedWith w
          ((ncompileFinNDTM A l₀ D q0).tm.initCfg x) ≤ m * (W + 2) + kD * (2 * B + 1)) ∧
      (NAns A oracle x (some l₀, fun _ => 0, none) N true ↔
        (ncompileFinNDTM A l₀ D q0).AcceptsWithin x T) := by
  obtain ⟨T, ⟨hbox, hfin⟩, hex⟩ := narm_run A l₀ oracle D q0 B W N l₀ (fun _ => 0) [] h
  have hinit : (ncompileFinNDTM A l₀ D q0).tm.initCfg x = seam (aseam x l₀ (fun _ => 0) []) :=
    ncompileTM_init A l₀ D q0 x
  refine ⟨T, fun w hw => ?_, fun w hw => ?_, ⟨fun hb => ?_, fun ⟨w, hw, hst, hout⟩ => ?_⟩⟩
  · rw [hinit]; exact (hfin w hw).1
  · rw [hinit]
    have := spaceUsedWith_le_of_ranges (ncompileTM A l₀ D q0) w (seam (aseam x l₀ (fun _ => 0) []))
      (Fin.append (fun _ => -1) (fun _ => -(B : ℤ))) (Fin.append (fun _ => (W : ℤ))
        (fun _ => (B : ℤ))) (by
        intro u hu i
        obtain ⟨h1, h2⟩ := hbox u (by omega)
        refine Fin.addCases (fun r => ?_) (fun j => ?_) i
        · simpa using h1 r
        · have := h2 j
          simp only [Fin.append_right]
          rw [abs_le] at this
          exact this)
    refine this.trans (le_of_eq ?_)
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    congr 1
    congr 1; omega
  · obtain ⟨w, hw, hwo⟩ := hex true hb
    refine ⟨w, hw, ?_, ?_⟩
    · rw [hinit]; exact (hfin w hw).1
    · rw [hinit]; simpa using hwo
  · rw [hinit] at hst hout
    obtain ⟨b, hb, hbo⟩ := (hfin w hw).2
    rw [hout] at hbo
    simp only [List.nil_append, List.cons.injEq, and_true] at hbo
    rw [← hbo] at hb
    exact hb

end Complexity.LogProg
