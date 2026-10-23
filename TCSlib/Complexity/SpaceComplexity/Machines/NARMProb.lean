/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.NARMRun
import TCSlib.Complexity.Randomized.RandomBits

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic abstract register machines as probabilistic machines

A probabilistic Turing machine is a `Turing.FinNDTM` whose choice word is a uniformly random
coin word, one coin per step [AB09, Def 7.1]. This file shows that the compilation
`Complexity.LogProg.ncompileFinNDTM` of a nondeterministic abstract register machine preserves
not only which answers occur but how often: the fraction of compiled branches of length `T`
with output `[b]` equals the fraction of abstract choice words of length `N` answering `b`
(`Complexity.LogProg.narm_randProb`). The abstract run consumes one bit per step and its
deterministic steps ignore theirs, so the latter is the probability of `b` when every
`choose` flips a fresh fair coin. Combined with `Complexity.LogProg.narm_space` this lets
randomized logspace algorithms [AB09, §7.7] be written as abstract machines.

Counting is by induction along `Complexity.LogProg.narm_run`: forced compiled segments
(`ndet_live`, `ndet_halt`) drop bits that the compiled run ignores, and a `choose` is one
compiled step following its bit, so both sides average the two targets' probabilities
(`Randomized.randProb_succ`, `Randomized.randProb_drop`).

This is infrastructure for [AB09, §7.7], not itself a result of the book.

## Main definitions

None: the probabilities are `Randomized.randProb` over choice words.

## Main results

* `Complexity.LogProg.randProb_runWith_seg`, `randProb_runWith_choose`,
  `randProb_runWith_mono`, `randProb_runWith_const` — probabilities along branches.
* `Complexity.LogProg.randProb_narun_det`, `randProb_narun_choose`, `randProb_narun_mono_len`.
* `Complexity.LogProg.narm_run_randProb`, `narm_randProb`, `narm_randProb_accept`,
  `narm_space_randProb` — the transfer.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definition 7.1, §7.7.)
-/

namespace Complexity.LogProg

open Turing Randomized

/-! ## Probabilities along nondeterministic runs -/

section Runs

variable {K : ℕ} {St : Type} {x : List Bool} {N : NDTM K Bool St}

/-- **A forced segment**: if every word of length `S` drives `N` from `C` to `C'`, an event
of the configuration reached from `C` under `S + T` bits has the probability of the same
event reached from `C'` under `T` bits. -/
lemma randProb_runWith_seg {C C' : Cfg K Bool St x} {S : ℕ}
    (heq : ∀ u : List Bool, u.length = S → N.runWith u C = C') (T : ℕ)
    (Q : Cfg K Bool St x → Prop) [DecidablePred Q] :
    randProb (S + T) (fun w => Q (N.runWith w C)) =
      randProb T (fun w => Q (N.runWith w C')) := by
  refine (randProb_congr (B := fun w => Q (N.runWith (w.drop S) C')) fun r => ?_).trans
    (randProb_drop S T fun w => Q (N.runWith w C'))
  have e : N.runWith (List.ofFn r) C = N.runWith ((List.ofFn r).drop S) C' := by
    conv_lhs => rw [← List.take_append_drop S (List.ofFn r)]
    rw [NDTM.runWith_append, heq _ (by simp)]
  rw [e]

/-- **A choice step**: if the step under bit `b` leads from `C` to `Cb b`, an event of the
configuration reached under `T + 1` bits has the average of the probabilities of the event
from `Cb true` and from `Cb false` under `T` bits. -/
lemma randProb_runWith_choose {C : Cfg K Bool St x} {Cb : Bool → Cfg K Bool St x}
    (hstep : ∀ b, N.stepWith b C = Cb b) (T : ℕ) (Q : Cfg K Bool St x → Prop)
    [DecidablePred Q] :
    randProb (T + 1) (fun w => Q (N.runWith w C)) =
      (randProb T (fun w => Q (N.runWith w (Cb true))) +
        randProb T (fun w => Q (N.runWith w (Cb false)))) / 2 := by
  have h : ∀ c : Bool, randProb T (fun u => Q (N.runWith (c :: u) C)) =
      randProb T (fun w => Q (N.runWith w (Cb c))) := fun c =>
    randProb_congr fun r => by rw [NDTM.runWith_cons, hstep]
  rw [randProb_succ, h true, h false]

/-- **Halted runs are stable**: if every word of length `T` halts `N` from `C`, an event of
the reached configuration has the same probability over any `T' ≥ T` bits. -/
lemma randProb_runWith_mono {C : Cfg K Bool St x} {T T' : ℕ}
    (hT : ∀ w : List Bool, w.length = T → (N.runWith w C).state = none) (hle : T ≤ T')
    (Q : Cfg K Bool St x → Prop) [DecidablePred Q] :
    randProb T' (fun w => Q (N.runWith w C)) = randProb T (fun w => Q (N.runWith w C)) := by
  refine (randProb_congr (B := fun w => Q (N.runWith (w.take T) C)) fun r => ?_).trans
    (randProb_take hle fun w => Q (N.runWith w C))
  have e : N.runWith (List.ofFn r) C = N.runWith ((List.ofFn r).take T) C := by
    conv_lhs => rw [← List.take_append_drop T (List.ofFn r)]
    exact runWith_append_of_halt (hT _ (by simp; omega)) _
  rw [e]

/-- **A forced end**: if every word of length `S` drives `N` from `C` to `Cf`, an event of
the reached configuration has probability `1` or `0` according as it holds at `Cf`. -/
lemma randProb_runWith_const {C Cf : Cfg K Bool St x} {S : ℕ}
    (heq : ∀ u : List Bool, u.length = S → N.runWith u C = Cf)
    (Q : Cfg K Bool St x → Prop) [DecidablePred Q] :
    randProb S (fun w => Q (N.runWith w C)) = if Q Cf then 1 else 0 := by
  rw [← randProb_const S (Q Cf)]
  exact randProb_congr fun r => by rw [heq _ (by simp)]

end Runs

/-! ## Probabilities along abstract runs -/

section Abstract

variable {m d : ℕ} {Λ : Type} {x : List Bool} {A : NARM m d Λ}
  {oracle : Fin d → List Bool → Bool}

/-- At a deterministic label the first bit is ignored: an event of the abstract run under
`N + 1` bits has the probability of the event under `N` bits after the step. -/
lemma randProb_narun_det {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) (β : Bool)
    (v : Fin m → ℕ) (res : Option Bool) (N : ℕ) (R : AConf m Λ → Prop) [DecidablePred R] :
    randProb (N + 1) (fun σ => R (narun A oracle x σ (some l, v, res))) =
      randProb N (fun σ => R (narun A oracle x σ
        (astep (A.detPart β) oracle x (some l, v, res)))) := by
  have h : ∀ c : Bool, randProb N (fun u => R (narun A oracle x (c :: u) (some l, v, res))) =
      randProb N (fun σ => R (narun A oracle x σ
        (astep (A.detPart β) oracle x (some l, v, res)))) := fun c =>
    randProb_congr fun r => by rw [narun_cons, nastep_det hA β]
  rw [randProb_succ, h true, h false]; ring

/-- At a `choose` label the first bit is a fair coin: an event of the abstract run under
`N + 1` bits has the average of its probabilities from the two targets under `N` bits. -/
lemma randProb_narun_choose {l l₁ l₀ : Λ} (hA : A l = .choose l₁ l₀) (v : Fin m → ℕ)
    (res : Option Bool) (N : ℕ) (R : AConf m Λ → Prop) [DecidablePred R] :
    randProb (N + 1) (fun σ => R (narun A oracle x σ (some l, v, res))) =
      (randProb N (fun σ => R (narun A oracle x σ (some l₁, v, res))) +
        randProb N (fun σ => R (narun A oracle x σ (some l₀, v, res)))) / 2 := by
  have h1 : randProb N (fun u => R (narun A oracle x (true :: u) (some l, v, res))) =
      randProb N (fun σ => R (narun A oracle x σ (some l₁, v, res))) :=
    randProb_congr fun r => by rw [narun_cons, nastep_choose hA]; rfl
  have h0 : randProb N (fun u => R (narun A oracle x (false :: u) (some l, v, res))) =
      randProb N (fun σ => R (narun A oracle x σ (some l₀, v, res))) :=
    randProb_congr fun r => by rw [narun_cons, nastep_choose hA]; rfl
  rw [randProb_succ, h1, h0]

/-- **Abstract probabilities are stable beyond all-branch halting**: if every branch halts
within `N`, an event of the final configuration has the same probability over any `N' ≥ N`
bits. -/
lemma randProb_narun_mono_len {G : AConf m Λ → Prop} {a : AConf m Λ} {N N' : ℕ}
    (h : NHalts A oracle x G a N) (hN : N ≤ N') (R : AConf m Λ → Prop) [DecidablePred R] :
    randProb N' (fun σ => R (narun A oracle x σ a)) =
      randProb N (fun σ => R (narun A oracle x σ a)) := by
  refine (randProb_congr (B := fun σ => R (narun A oracle x (σ.take N) a)) fun r => ?_).trans
    (randProb_take hN fun σ => R (narun A oracle x σ a))
  have e : narun A oracle x (List.ofFn r) a = narun A oracle x ((List.ofFn r).take N) a := by
    conv_lhs => rw [← List.take_append_drop N (List.ofFn r)]
    exact narun_append_of_halted (h _ (by simp; omega)).1 _
  rw [e]

end Abstract

/-! ## The transfer -/

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- **The probabilistic run theorem.** If every choice word of length `N` halts the abstract
machine from `(l, v)` through configurations satisfying `NGuard`, then for some `T` every
branch of length `T` of the compiled machine, from the compiled configuration of `(l, v)`
having written `out`, halts, and for each `b` the fraction of those branches ending with
output `out ++ [b]` is the fraction of abstract words of length `N` answering `b`.

**Proof sketch.** Induction on `N`, along the proof of `narm_run`. A live deterministic
step is a forced segment of the compiled machine (`ndet_live`) and ignores one abstract bit;
a halting one is a forced end (`ndet_halt`) with output `out ++ [b₀]`, and the abstract run
answers `b₀` on every word. At a `choose` the first compiled step follows the bit
(`ncompileTM_stepWith_choose`) and the first abstract bit selects the same target, so both
sides average the two targets' probabilities, after equalizing the compiled lengths by
stability of halted runs. -/
theorem narm_run_randProb (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) :
    ∀ (N : ℕ) (l : Λ) (v : Fin m → ℕ) (out : List Bool),
      NHalts A oracle x (NGuard A oracle D q0 B W x) (some l, v, none) N →
      ∃ T, (∀ w : List Bool, w.length = T →
          ((ncompileTM A l₀ D q0).runWith w (seam (aseam x l v out))).state = none) ∧
        ∀ b : Bool,
          randProb T (fun w =>
            ((ncompileTM A l₀ D q0).runWith w (seam (aseam x l v out))).output = out ++ [b]) =
          randProb N (fun σ => (narun A oracle x σ (some l, v, none)).2.2 = some b) := by
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
        obtain ⟨T, hhalt, hprob⟩ := ih l' v' out h'
        obtain ⟨S, -, heq⟩ := ndet_live A l₀ oracle D q0 B W l l' v v' out hs hp hw
        refine ⟨S + T, fun w hw' => ?_, fun b => ?_⟩
        · have e : (ncompileTM A l₀ D q0).runWith w (seam (aseam x l v out)) =
              (ncompileTM A l₀ D q0).runWith (w.drop S) (seam (aseam x l' v' out)) := by
            conv_lhs => rw [← List.take_append_drop S w]
            rw [NDTM.runWith_append, heq _ (by simp; omega)]
          rw [e]; exact hhalt _ (by simp; omega)
        · rw [randProb_narun_det hA false v none N (fun a => a.2.2 = some b), hs]
          exact (randProb_runWith_seg heq T (fun c => c.output = out ++ [b])).trans (hprob b)
      · -- a halting deterministic step
        obtain ⟨S, Cf, -, heq, hst, hout⟩ :=
          ndet_halt A l₀ oracle D q0 B W l hA v out b₀ hs hp hw
        refine ⟨S, fun w hw' => by rw [heq w hw']; exact hst, fun b => ?_⟩
        rw [randProb_narun_det hA false v none N (fun a => a.2.2 = some b), hs,
          randProb_runWith_const heq (fun c => c.output = out ++ [b])]
        rw [randProb_congr (B := fun _ => some b₀ = some b) fun r => by simp, randProb_const]
        simp [hout]
    | choose l₁ l₀' =>
      have key := fun c : Bool => ih (if c then l₁ else l₀') v out (h.of_choose hA c)
      choose T hhalt hprob using key
      have hle : ∀ c, T c ≤ max (T true) (T false) := fun c => by cases c <;> simp
      refine ⟨max (T true) (T false) + 1, fun w hw' => ?_, fun b => ?_⟩
      · cases w with
        | nil => simp at hw'
        | cons c w =>
          rw [NDTM.runWith_cons, ncompileTM_stepWith_choose A l₀ D q0 hA c v out]
          have hl : (w.take (T c)).length = T c := by simp at hw' ⊢; have := hle c; omega
          rw [← List.take_append_drop (T c) w, runWith_append_of_halt (hhalt c _ hl)]
          exact hhalt c _ hl
      · rw [randProb_narun_choose hA v none N (fun a => a.2.2 = some b),
          randProb_runWith_choose (fun c => ncompileTM_stepWith_choose A l₀ D q0 hA c v out) _
            (fun c => c.output = out ++ [b]),
          randProb_runWith_mono (hhalt true) (hle true) (fun c => c.output = out ++ [b]),
          randProb_runWith_mono (hhalt false) (hle false) (fun c => c.output = out ++ [b])]
        exact congrArg₂ (fun p q => (p + q) / 2) (hprob true b) (hprob false b)

/-- **The probabilistic transfer.** If every choice word of length `N` halts the abstract
machine, started at `l₀` with all registers `0`, through configurations satisfying `NGuard`,
then for every `T` within which all branches of the compiled machine halt on `x`, the
fraction of compiled branches of length `T` with output `[b]` is the fraction of abstract
choice words of length `N` answering `b`.

**Proof sketch.** `narm_run_randProb` gives a time `T₀` by which every compiled branch has
halted, with the claimed fraction at `T₀`; as `T` and `T₀` are both halting times, the
fractions at `T`, `max T T₀` and `T₀` agree (`randProb_runWith_mono`). -/
theorem narm_randProb [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B W N : ℕ)
    (h : NHalts A oracle x (NGuard A oracle D q0 B W x) (some l₀, fun _ => 0, none) N)
    {T : ℕ} (hT : (ncompileFinNDTM A l₀ D q0).tm.HaltsWithin x T) (b : Bool) :
    randProb T (fun w => ((ncompileFinNDTM A l₀ D q0).tm.runWith w
        ((ncompileFinNDTM A l₀ D q0).tm.initCfg x)).output = [b]) =
      randProb N (fun σ => (narun A oracle x σ (some l₀, fun _ => 0, none)).2.2 = some b) := by
  obtain ⟨T₀, hh, hp⟩ := narm_run_randProb A l₀ oracle D q0 B W N l₀ (fun _ => 0) [] h
  have hinit : (ncompileFinNDTM A l₀ D q0).tm.initCfg x = seam (aseam x l₀ (fun _ => 0) []) :=
    ncompileTM_init A l₀ D q0 x
  have hT' : ∀ w : List Bool, w.length = T →
      ((ncompileTM A l₀ D q0).runWith w (seam (aseam x l₀ (fun _ => 0) []))).state = none :=
    fun w hw => by rw [← hinit]; exact hT w hw
  rw [hinit]
  calc _ = randProb (max T T₀) (fun w => ((ncompileTM A l₀ D q0).runWith w
          (seam (aseam x l₀ (fun _ => 0) []))).output = [b]) :=
        (randProb_runWith_mono hT' (le_max_left T T₀) (fun c => c.output = [b])).symm
    _ = randProb T₀ (fun w => ((ncompileTM A l₀ D q0).runWith w
          (seam (aseam x l₀ (fun _ => 0) []))).output = [] ++ [b]) :=
        randProb_runWith_mono hh (le_max_right T T₀) (fun c => c.output = [] ++ [b])
    _ = _ := hp b

/-- **The probabilistic transfer, with acceptance.** Under the hypotheses of `narm_randProb`,
the fraction of compiled branches of length `T` that halt with output `[true]` is the
fraction of abstract choice words of length `N` answering `true`. -/
theorem narm_randProb_accept [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B W N : ℕ)
    (h : NHalts A oracle x (NGuard A oracle D q0 B W x) (some l₀, fun _ => 0, none) N)
    {T : ℕ} (hT : (ncompileFinNDTM A l₀ D q0).tm.HaltsWithin x T) :
    randProb T (fun w =>
        ((ncompileFinNDTM A l₀ D q0).tm.runWith w ((ncompileFinNDTM A l₀ D q0).tm.initCfg x)).state
          = none ∧
        ((ncompileFinNDTM A l₀ D q0).tm.runWith w
          ((ncompileFinNDTM A l₀ D q0).tm.initCfg x)).output = [true]) =
      randProb N (fun σ => (narun A oracle x σ (some l₀, fun _ => 0, none)).2.2 = some true) := by
  rw [← narm_randProb A l₀ oracle D q0 B W N h hT true]
  exact randProb_congr fun r => and_iff_right (hT _ (by simp))

/-- **Nondeterministic abstract register machines as probabilistic small-space machines.**
Under the hypotheses of `narm_space`, for some `T` every branch of length `T` of the
compiled machine halts within `m (W + 2) + kD (2B + 1)` work cells, some branch accepts iff
some abstract choice word of length `N` answers `true`, and for each `b` the fraction of
branches with output `[b]` is the fraction of abstract choice words answering `b`. -/
theorem narm_space_randProb [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B W N : ℕ)
    (h : NHalts A oracle x (NGuard A oracle D q0 B W x) (some l₀, fun _ => 0, none) N) :
    ∃ T, (ncompileFinNDTM A l₀ D q0).tm.HaltsWithin x T ∧
      (∀ w : List Bool, w.length = T →
        (ncompileFinNDTM A l₀ D q0).tm.spaceUsedWith w
          ((ncompileFinNDTM A l₀ D q0).tm.initCfg x) ≤ m * (W + 2) + kD * (2 * B + 1)) ∧
      (NAns A oracle x (some l₀, fun _ => 0, none) N true ↔
        (ncompileFinNDTM A l₀ D q0).AcceptsWithin x T) ∧
      ∀ b : Bool, randProb T (fun w => ((ncompileFinNDTM A l₀ D q0).tm.runWith w
          ((ncompileFinNDTM A l₀ D q0).tm.initCfg x)).output = [b]) =
        randProb N (fun σ => (narun A oracle x σ (some l₀, fun _ => 0, none)).2.2 = some b) := by
  obtain ⟨T, hT, hsp, hacc⟩ := narm_space A l₀ oracle D q0 B W N h
  exact ⟨T, hT, hsp, hacc, narm_randProb A l₀ oracle D q0 B W N h hT⟩

end Complexity.LogProg
