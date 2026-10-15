/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reachable codes at growing radii

The exponential-time simulation of a space-bounded nondeterministic decider `N` does not know
the space bound: it searches the configuration graph at the radii `s = 0, 1, 2, …` and stops at
the first radius at which growing the window to `s + 1` does not add a reachable vertex. This
file proves that this works.

At radius `s`, the *reachable codes* (`Complexity.ExpBFS.RCode`) are the codes reachable from
the initial code along step pairs (`Complexity.Codec.StepRel`); they are exactly the codes of
the configurations reached by choice words all of whose prefixes stay in the window `[-s, s]`
(`Complexity.ExpBFS.rcode_iff`). Re-coding a configuration at radius `s + 1` maps the
reachable codes at `s` injectively into those at `s + 1`
(`Complexity.ExpBFS.card_rset_le_succ`). If the two sets have the same size, every one-step
successor of a window-`s` run is again in the window (it is in the window `s + 1`, hence the
re-coding of a window-`s` run, hence of the same vertex), so every run stays in the window and
acceptance is decided by the reachable codes at `s`
(`Complexity.ExpBFS.mem_iff_of_card_eq`). Once `s` is at least the space bound, every run is
in the window and the sizes agree (`Complexity.ExpBFS.card_rset_succ_of_le`).

Configuration-graph infrastructure for [AB09, §4.1.1, Theorem 4.2]; not itself a result of
the book (the book assumes `S` space-constructible and computes the radius instead).

## Main definitions

* `Complexity.ExpBFS.WinRun` — a choice word whose prefixes stay in the window.
* `Complexity.ExpBFS.RCode`, `Complexity.ExpBFS.rset` — reachable codes at a radius.

## Main results

* `Complexity.ExpBFS.rcode_iff` — reachable codes are the codes of window runs.
* `Complexity.ExpBFS.card_rset_le_succ` — the count does not drop when the radius grows.
* `Complexity.ExpBFS.mem_iff_of_card_eq` — equal counts decide membership.
* `Complexity.ExpBFS.card_rset_succ_of_le` — above the space bound the counts agree.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4, Theorem 4.2.)
-/

namespace Complexity.ExpBFS

open Turing Codec LogProg

variable {N : FinNDTM Bool} {x : List Bool}

/-! ## Windows -/

/-- The window grows with the radius. -/
lemma inWin_mono {s s' : ℕ} {C : Cfg N.k Bool N.State x} (h : Cfg.InWindow s C) (hs : s ≤ s') :
    Cfg.InWindow s' C :=
  ⟨fun i => (h.1 i).trans (by exact_mod_cast hs),
    fun i z hz => h.2 i z (lt_of_le_of_lt (by exact_mod_cast hs) hz)⟩

/-- One step from the window `[-s, s]` stays in the window `[-(s + 1), s + 1]`: heads move by
one cell and write under themselves. -/
lemma inWin_stepWith {s : ℕ} {C : Cfg N.k Bool N.State x} (h : Cfg.InWindow s C) (b : Bool) :
    Cfg.InWindow (s + 1) (N.tm.stepWith b C) := by
  unfold NDTM.stepWith
  cases hs : C.state with
  | none => exact inWin_mono h (by omega)
  | some q =>
    refine ⟨fun i => ?_, fun i z hz' => ?_⟩
    · have hp := h.1 i
      have hmove := workTapePos_apply_le (N.tm.tr b q C.inputSymbol C.workTapeSymbols) C i
      push_cast; rw [abs_le] at hp hmove ⊢; constructor <;> linarith [hp.1, hp.2,
        hmove.1, hmove.2]
    · have hp := h.1 i
      have hzs : (s : ℤ) < |z| := by push_cast at hz'; linarith
      rcases hwr : ((N.tm.tr b q C.inputSymbol C.workTapeSymbols).workTapes i).1 with _ | sym
      · simp only [Action.apply, hwr]
        exact h.2 i z hzs
      · simp only [Action.apply, hwr]
        have hzp : z ≠ C.workTapePos i := by
          rintro rfl; exact absurd hp (not_le.mpr hzs)
        rw [Function.update_of_ne hzp]
        exact h.2 i z hzs

/-- A choice word all of whose prefix configurations lie in the window `[-s, s]`. -/
def WinRun (N : FinNDTM Bool) (x : List Bool) (s : ℕ) (w : List Bool) : Prop :=
  ∀ j ≤ w.length, Cfg.InWindow s (N.tm.runWith (w.take j) (N.tm.initCfg x))

/-- The initial configuration is in every window. -/
lemma inWin_init (s : ℕ) : Cfg.InWindow s (N.tm.initCfg x) := Cfg.inWindow_init _ x s

/-- Extending a window run by a step that stays in the window. -/
lemma WinRun.snoc {s : ℕ} {w : List Bool} (h : WinRun N x s w) (b : Bool)
    (hb : Cfg.InWindow s (N.tm.runWith (w ++ [b]) (N.tm.initCfg x))) : WinRun N x s (w ++ [b]) := by
  intro j hj
  simp only [List.length_append, List.length_cons, List.length_nil] at hj
  rcases Nat.lt_or_ge j (w.length + 1) with h' | h'
  · rw [List.take_append_of_le_length (by omega)]; exact h j (by omega)
  · obtain rfl : j = w.length + 1 := by omega
    rw [List.take_of_length_le (by simp)]; exact hb

/-- A window run is a window run at every larger radius. -/
lemma WinRun.mono {s s' : ℕ} {w : List Bool} (h : WinRun N x s w) (hs : s ≤ s') :
    WinRun N x s' w := fun j hj => inWin_mono (h j hj) hs

/-- The whole run of a window run is in the window. -/
lemma WinRun.last {s : ℕ} {w : List Bool} (h : WinRun N x s w) :
    Cfg.InWindow s (N.tm.runWith w (N.tm.initCfg x)) := by
  simpa using h w.length le_rfl

/-! ## Reachable codes -/

/-- **The reachable codes at radius `s`**: codes reachable from the initial code along step
pairs at radius `s`. -/
def RCode (N : FinNDTM Bool) (x : List Bool) (s u : ℕ) : Prop :=
  Relation.ReflTransGen (StepRel N x s) (cfgCode s (N.tm.initCfg x)) u

/-- Equal codes of window configurations are equal vertices. -/
lemma coreSum_eq_of_code_eq {s : ℕ} {C D : Cfg N.k Bool N.State x} (hC : Cfg.InWindow s C)
    (hD : Cfg.InWindow s D) (h : cfgCode s C = cfgCode s D) : NDTM.coreSum C = NDTM.coreSum D :=
  coreSum_eq_of_cfgWord_eq hC hD (by rw [← bits_cfgCode, ← bits_cfgCode, h])

/-- Equal vertices have equal codes. -/
lemma code_eq_of_coreSum_eq {s : ℕ} {C D : Cfg N.k Bool N.State x}
    (h : NDTM.coreSum C = NDTM.coreSum D) : cfgCode s C = cfgCode s D := by
  simp only [cfgCode, cfgWord_congr (s := s) h]

/-- **Reachable codes are the codes of window runs.**

**Proof sketch.** (⇐) The codes of consecutive prefixes of a window run are step pairs.
(⇒) Induction along the path: a step pair from the code of a window run's end leads, by
the vertex's determination of its successors (`Turing.NDTM.coreSum_stepWith`), to the code of
the run extended by the pair's choice bit, still in the window
(`Turing.NDTM.inWindow_of_coreSum_eq`). -/
theorem rcode_iff (s u : ℕ) :
    RCode N x s u ↔ ∃ w, WinRun N x s w ∧ cfgCode s (N.tm.runWith w (N.tm.initCfg x)) = u := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], fun j _ => by simpa using inWin_init s, rfl⟩
    | tail _ hst ih =>
      obtain ⟨w, hw, hcode⟩ := ih
      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ := (mem_stepLang N x _ _ s).mp hst
      have hv : NDTM.coreSum (N.tm.runWith w (N.tm.initCfg x)) = NDTM.coreSum C :=
        coreSum_eq_of_code_eq hw.last hC (hcode.trans hcC.symm)
      have hv' : NDTM.coreSum (N.tm.runWith (w ++ [b]) (N.tm.initCfg x)) = NDTM.coreSum C' := by
        rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil, ← hb]
        exact NDTM.coreSum_stepWith N.tm b hv
      refine ⟨w ++ [b], hw.snoc b (NDTM.inWindow_of_coreSum_eq hv' hC'), ?_⟩
      rw [code_eq_of_coreSum_eq hv', hcC']
  · rintro ⟨w, hw, rfl⟩
    have key : ∀ j ≤ w.length,
        RCode N x s (cfgCode s (N.tm.runWith (w.take j) (N.tm.initCfg x))) := by
      intro j
      induction j with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ j ih =>
        intro hj
        refine (ih (by omega)).tail ?_
        rw [StepRel, mem_stepLang]
        refine ⟨_, hw j (by omega), rfl, _, ⟨w[j]'(by omega), ?_⟩, hw (j + 1) hj, rfl⟩
        rw [List.take_succ, NDTM.runWith_append, List.getElem?_eq_getElem (by omega)]
        rfl
    simpa using key w.length le_rfl

/-- Reachable codes lie below the code bound. -/
lemma rcode_lt {s u : ℕ} (h : RCode N x s u) :
    u < 2 ^ (codeK N * (s + logSpace x.length + 1)) := by
  obtain ⟨w, -, rfl⟩ := (rcode_iff s u).mp h
  exact cfgCode_lt s _

/-- **The reachable codes at radius `s`**, as a finite set. -/
noncomputable def rset (N : FinNDTM Bool) (x : List Bool) (s : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ (codeK N * (s + logSpace x.length + 1)))).filter (RCode N x s)

/-- Membership in the reachable codes. -/
lemma mem_rset {s u : ℕ} : u ∈ rset N x s ↔ RCode N x s u := by
  classical
  simp only [rset, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨rcode_lt h, h⟩⟩

open Classical in
/-- Counting the reachable codes below any bound above the code bound gives their number. -/
lemma card_filter_rcode {s K : ℕ} (hK : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ K) :
    ((Finset.range K).filter (RCode N x s)).card = (rset N x s).card := by
  have e : (Finset.range K).filter (RCode N x s) = rset N x s := by
    apply Finset.ext
    intro u
    rw [mem_rset]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨(rcode_lt h).trans_le hK, h⟩⟩
  rw [e]

/-! ## Growing the radius -/

open Classical in
/-- Re-coding at radius `s + 1`: a reachable code at radius `s` is the code of a window run,
re-coded at radius `s + 1` (well defined up to the vertex). -/
noncomputable def recode (N : FinNDTM Bool) (x : List Bool) (s u : ℕ) : ℕ :=
  if h : RCode N x s u then
    cfgCode (s + 1) (N.tm.runWith (Classical.choose ((rcode_iff s u).mp h)) (N.tm.initCfg x))
  else 0

/-- The re-coding of the code of a window run is the code at radius `s + 1` of its end. -/
lemma recode_spec {s : ℕ} {w : List Bool} (hw : WinRun N x s w) :
    recode N x s (cfgCode s (N.tm.runWith w (N.tm.initCfg x))) =
      cfgCode (s + 1) (N.tm.runWith w (N.tm.initCfg x)) := by
  have h : RCode N x s (cfgCode s (N.tm.runWith w (N.tm.initCfg x))) :=
    (rcode_iff s _).mpr ⟨w, hw, rfl⟩
  rw [recode, dif_pos h]
  obtain ⟨hw', hcode⟩ := Classical.choose_spec ((rcode_iff s _).mp h)
  exact code_eq_of_coreSum_eq (coreSum_eq_of_code_eq hw'.last hw.last hcode)

/-- Re-coding is injective on the reachable codes. -/
lemma recode_injOn (s : ℕ) : Set.InjOn (recode N x s) (rset N x s : Set ℕ) := by
  intro u hu v hv huv
  obtain ⟨w, hw, rfl⟩ := (rcode_iff s u).mp (mem_rset.mp hu)
  obtain ⟨w', hw', rfl⟩ := (rcode_iff s v).mp (mem_rset.mp hv)
  rw [recode_spec hw, recode_spec hw'] at huv
  exact code_eq_of_coreSum_eq
    (coreSum_eq_of_code_eq ((hw.mono (by omega)).last) ((hw'.mono (by omega)).last) huv)

/-- Re-coding maps reachable codes to reachable codes. -/
lemma recode_mem {s u : ℕ} (hu : u ∈ rset N x s) : recode N x s u ∈ rset N x (s + 1) := by
  obtain ⟨w, hw, rfl⟩ := (rcode_iff s u).mp (mem_rset.mp hu)
  rw [recode_spec hw, mem_rset, rcode_iff]
  exact ⟨w, hw.mono (by omega), rfl⟩

/-- **The count of reachable codes does not drop when the radius grows.** -/
theorem card_rset_le_succ (s : ℕ) : (rset N x s).card ≤ (rset N x (s + 1)).card :=
  Finset.card_le_card_of_injOn _ (fun _ hu => recode_mem hu) (recode_injOn s)

/-- With equal counts, every reachable code at radius `s + 1` is a re-coding. -/
lemma image_recode_of_card_eq {s : ℕ} (h : (rset N x s).card = (rset N x (s + 1)).card) :
    (rset N x s).image (recode N x s) = rset N x (s + 1) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact recode_mem hu
  · rw [Finset.card_image_of_injOn (recode_injOn s), h]

/-- **Equal counts close the window**: if the counts at `s` and `s + 1` agree, every choice word
is a window run at radius `s`.

**Proof sketch.** Induction on the word. One more step from a window run is in the window
`s + 1` (`inWin_stepWith`), so its code at `s + 1` is reachable, hence (equal counts) the
re-coding of a window run at `s`; equal codes at `s + 1` are equal vertices, and the window
depends only on the vertex. -/
theorem winRun_of_card_eq {s : ℕ} (h : (rset N x s).card = (rset N x (s + 1)).card) :
    ∀ w : List Bool, WinRun N x s w := by
  intro w
  induction w using List.reverseRecOn with
  | nil => exact fun j _ => by simpa using inWin_init s
  | append_singleton w b ih =>
    refine ih.snoc b ?_
    have hstep : Cfg.InWindow (s + 1) (N.tm.runWith (w ++ [b]) (N.tm.initCfg x)) := by
      rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
      exact inWin_stepWith ih.last b
    have hrun : WinRun N x (s + 1) (w ++ [b]) := (ih.mono (by omega)).snoc b hstep
    have hmem : cfgCode (s + 1) (N.tm.runWith (w ++ [b]) (N.tm.initCfg x)) ∈ rset N x (s + 1) :=
      mem_rset.mpr ((rcode_iff _ _).mpr ⟨_, hrun, rfl⟩)
    rw [← image_recode_of_card_eq h] at hmem
    obtain ⟨u, hu, hre⟩ := Finset.mem_image.mp hmem
    obtain ⟨w', hw', rfl⟩ := (rcode_iff s u).mp (mem_rset.mp hu)
    rw [recode_spec hw'] at hre
    exact NDTM.inWindow_of_coreSum_eq
      (coreSum_eq_of_code_eq ((hw'.mono (by omega)).last) hstep hre).symm hw'.last

/-- **Equal counts decide membership**: if `N` decides `L` (in any space) and the counts of
reachable codes at radii `s` and `s + 1` agree, then `x ∈ L` iff some reachable code at
radius `s` is an accepting code.

**Proof sketch.** (⇐) `Complexity.Codec.mem_of_codePath`. (⇒) An accepting branch is a
window run (`winRun_of_card_eq`), so the code of its halted end is reachable and accepting. -/
theorem mem_iff_of_card_eq {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
    {s : ℕ} (h : (rset N x s).card = (rset N x (s + 1)).card) :
    x ∈ L ↔ ∃ u, RCode N x s u ∧
      pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ acceptLang N := by
  constructor
  · intro hx
    obtain ⟨T, -, -, hiff⟩ := hN x
    obtain ⟨w, -, hhalt, hout⟩ := hiff.mp hx
    have hw := winRun_of_card_eq h w
    refine ⟨_, (rcode_iff s _).mpr ⟨w, hw, rfl⟩, ?_⟩
    rw [mem_acceptLang]
    exact ⟨_, hw.last, rfl, hhalt, hout⟩
  · rintro ⟨u, hu, hacc⟩
    exact mem_of_codePath hN x s _ u (by rw [mem_initLang]) hu hacc

/-- Every configuration reached from initialization by a decider in space `sp` lies in the
window of radius `sp |x|`.

**Proof sketch.** Words of the halting budget's length use at most `sp |x|` cells, so their
prefixes are in the window (`Turing.NDTM.runWith_take_inWindow`); a shorter word is a prefix
of a padded one, a longer one has halted at the budget. -/
lemma inWin_runWith_of_decides {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
    (w : List Bool) : Cfg.InWindow (sp x.length) (N.tm.runWith w (N.tm.initCfg x)) := by
  obtain ⟨T, hHalt, hSpace, -⟩ := hN x
  by_cases hw : w.length ≤ T
  · set w' := w ++ List.replicate (T - w.length) false
    have hw' : w'.length = T := by simp [w']; omega
    have := NDTM.runWith_take_inWindow N.tm w' (hSpace w' hw') w.length
    rwa [show w'.take w.length = w by simp [w']] at this
  · have hlen : (w.take T).length = T := List.length_take_of_le (by omega)
    have frozen : N.tm.runWith w (N.tm.initCfg x) = N.tm.runWith (w.take T) (N.tm.initCfg x) := by
      conv_lhs => rw [← List.take_append_drop T w]
      rw [NDTM.runWith_append, NDTM.runWith_of_halt _ (hHalt _ hlen)]
    rw [frozen]
    have := NDTM.runWith_take_inWindow N.tm (w.take T) (hSpace _ hlen) T
    rwa [show (w.take T).take T = w.take T by simp] at this

/-- **Above the space bound the counts agree.** If `N` decides `L` in space `sp` and
`sp |x| ≤ s`, the counts of reachable codes at radii `s` and `s + 1` agree.

**Proof sketch.** Every run is in the window `sp |x| ≤ s` (`inWin_runWith_of_decides`), so
every window run at `s + 1` is one at `s`, and its code at `s + 1` is the re-coding of its
code at `s`; with `card_rset_le_succ` the counts agree. -/
theorem card_rset_succ_of_le {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp)
    {s : ℕ} (hs : sp x.length ≤ s) : (rset N x s).card = (rset N x (s + 1)).card := by
  classical
  refine le_antisymm (card_rset_le_succ s) ?_
  calc (rset N x (s + 1)).card ≤ ((rset N x s).image (recode N x s)).card := by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨w, -, rfl⟩ := (rcode_iff _ v).mp (mem_rset.mp hv)
        have hw : WinRun N x s w := fun j _ =>
          inWin_mono (inWin_runWith_of_decides hN (w.take j)) hs
        exact Finset.mem_image.mpr ⟨_, mem_rset.mpr ((rcode_iff s _).mpr ⟨w, hw, rfl⟩),
          recode_spec hw⟩
    _ ≤ (rset N x s).card := Finset.card_image_le

end Complexity.ExpBFS
