/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.CallReturn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A whole subroutine call of the compiled machine

From a program configuration at a call node, the compiled machine moves the argument
heads onto their left blanks (*setup*), simulates the decider on the virtual input step for
step (`Complexity.LogProg.sim_step`), and when the decider halts rewinds the input head and
the argument heads (*return*). For a *clean* decider — one that halts with blank work tapes
and heads at the origin — this ends in the compiled configuration of the program
configuration after the call (`Complexity.LogProg.call_run`), with every head in a known
range at every intermediate time.

Compiled configurations (`mkCfg`) and the return phase are in
`TCSlib.Complexity.SpaceComplexity.Machines.CallReturn`, which this file re-exports.

## Main definitions

* `Complexity.LogProg.mkCfg` — a compiled configuration from its register and decider
  blocks.
* `Complexity.LogProg.CleanRun` — the decider halts from a start state cleanly, with heads
  in a given range, answering a given bit.

## Main results

* `Complexity.LogProg.call_run` — a call runs to completion.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-! ## The whole call -/

/-- The decider started in state `q` on `V` halts — at time `T` — with output `[b]`, blank
work tapes and heads at the origin, its heads staying within `[-B, B]`. -/
def CleanRun (D : MultiTapeTM kD Bool SD) (q : SD) (V : List Bool) (b : Bool) (B : ℕ) : Prop :=
  ∃ T, (D.runFrom (Cfg.init q V) T).state = none ∧ (D.runFrom (Cfg.init q V) T).output = [b] ∧
    (D.runFrom (Cfg.init q V) T).workTapes = (fun _ _ => none) ∧
    (D.runFrom (Cfg.init q V) T).workTapePos = (fun _ => 0) ∧
    ∀ t ≤ T, ∀ i, |(D.runFrom (Cfg.init q V) t).workTapePos i| ≤ B

/-- Properties of all configurations along two consecutive run segments. -/
lemma runFrom_forall_append {K : ℕ} {S : Type} {tm : MultiTapeTM K Bool S}
    {c : Cfg K Bool S x} {T₁ T₂ : ℕ} {Q : Cfg K Bool S x → Prop}
    (h₁ : ∀ t ≤ T₁, Q (tm.runFrom c t)) (h₂ : ∀ t ≤ T₂, Q (tm.runFrom (tm.runFrom c T₁) t)) :
    ∀ t ≤ T₁ + T₂, Q (tm.runFrom c t) := by
  intro t ht
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact h₁ t h.le
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [MultiTapeTM.runFrom_add]
    exact h₂ t' (by omega)

/-- The first segment of a virtual input starts at offset `0`. -/
@[simp] lemma off_zero (segs : List Seg) : off segs 0 = 0 := by cases segs <;> rfl

section Whole

variable {l : Λ} {cs : CallSpec m d Λ} {W : Fin m → List Bool} {c0 : Cfg m Bool Λ x}

/-- During a call the register positions stay in the call's range. -/
lemma regPos_box (_hnd : cs.args.Nodup) (s : ℕ) (tp : TPos)
    (hval : tp.Valid (callSegs cs x W) s) (_hs : s < cs.args.length + 1) :
    RegBox cs c0.workTapePos W (regPos c0 cs W s tp) := by
  intro r
  refine ⟨fun hr => by simp [regPos, hr], fun hr => ?_⟩
  have hidx := List.idxOf_lt_length_of_mem hr
  have hget : cs.args[cs.args.idxOf r] = r := List.getElem_idxOf hidx
  have hw : wlen (callSegs cs x W) (cs.args.idxOf r + 1) = (W r).length := by
    simp only [wlen]; rw [seg_callSegs_succ cs x W _ hidx, hget]
  simp only [regPos, hr, ↓reduceIte]
  split_ifs with h1 h2
  · rw [hw]; omega
  · omega
  · have hs' : s = cs.args.idxOf r + 1 := by omega
    have := trackPos_bounds _ s tp hval
    rw [hs'] at this ⊢
    rw [hw] at this
    exact this

/-- The side tests of the return phase agree with the register positions at the halt.

**Proof sketch.** A register head is at `-1` or at `|W r|` only when the track position sits at
the left or right blank of that register's segment. Consistency of the track position with the
segment parity and direction (`Consistent`) then fixes which side the return phase's test
`leftSide` reports. -/
lemma regPos_side (hnd : cs.args.Nodup) (s : Fin (m + 1)) (par dir : Bool) (tp : TPos)
    (hcons : Consistent (callSegs cs x W) s par dir tp)
    (hval : tp.Valid (callSegs cs x W) s) (a : ℕ) (ha : a < cs.args.length) (hm : a < m) :
    (regPos c0 cs W s tp cs.args[a] = -1 → leftSide s dir ⟨a, hm⟩ = true) ∧
      (regPos c0 cs W s tp cs.args[a] = (W cs.args[a]).length →
        leftSide s dir ⟨a, hm⟩ = false) := by
  have hidx : cs.args.idxOf cs.args[a] = a := List.idxOf_getElem hnd a ha
  have hw : wlen (callSegs cs x W) (a + 1) = (W cs.args[a]).length := by
    simp only [wlen]; rw [seg_callSegs_succ cs x W _ ha]
  simp only [regPos, List.getElem_mem, ↓reduceIte, hidx, leftSide]
  split_ifs with h1 h2
  · rw [hw]
    have e1 : ¬ (s : ℕ) < a + 1 := by omega
    have e2 : ¬ (s : ℕ) = a + 1 := by omega
    simp only [e1, e2, decide_false, Bool.false_and, Bool.or_false, Bool.false_eq_true]
    constructor <;> intro h <;> first | rfl | omega
  · simp only [h2, decide_true, Bool.true_or]
    exact ⟨fun _ => trivial, fun h => h.elim⟩
  · have hs' : (s : ℕ) = a + 1 := by omega
    cases tp with
    | left =>
      simp only [Consistent] at hcons
      subst hcons
      simp [trackPos, hs']
    | cell c p =>
      simp only [TPos.Valid, hs'] at hval
      simp only [trackPos]
      rw [hw] at hval
      constructor <;> intro h <;> omega
    | right =>
      simp only [Consistent] at hcons
      subst hcons
      simp only [trackPos, hs', hw]
      constructor <;> intro h <;> simp; omega

/-- **A whole call.** From a program configuration at a call node whose argument registers
hold `W` with their heads at the origin, input head on the first cell, and a decider that
answers `b` cleanly within head range `B`, the compiled machine reaches the compiled
configuration of the program configuration after the call — state `yes` or `no` by `b`,
input head on the first cell, everything else unchanged. Throughout, the registers stay in
the call's range and the decider block in `[-B, B]`.

**Proof sketch.** One setup step (`apply_moves`) establishes the simulation relation with
the decider's initial configuration; `sim_step` carries it to the decider's first halting
time; there the decider's tapes are clean, and the return phase (`ret2_run`, `regs_run`)
restores the input head and the argument heads (`regPos_side` checks the side tests). -/
theorem call_run (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (hl : c0.state = some l) (hcall : P.call l = some cs)
    (hW : ∀ r ∈ cs.args, c0.workTapes r = FinTM.bufferTape (W r))
    (hW0 : ∀ r ∈ cs.args, c0.workTapePos r = 0) (hnd : cs.args.Nodup)
    (hin : c0.inputPos.val = 1) (b : Bool) (B : ℕ)
    (hD : CleanRun D (q0 cs.dec) (vword (callSegs cs x W)) b B) :
    ∃ T, (∀ t ≤ T, RegBox cs c0.workTapePos W (fun r => ((compileTM P l₀ D q0).runFrom
          (seam c0) t).workTapePos (Fin.castAdd kD r)) ∧
        ∀ i, |((compileTM P l₀ D q0).runFrom (seam c0) t).workTapePos (Fin.natAdd m i)| ≤ B) ∧
      (compileTM P l₀ D q0).runFrom (seam c0) T =
        seam { c0 with state := some (if b then cs.yes else cs.no), inputPos := 1 } := by
  classical
  obtain ⟨T, hTh, hTo, hTt, hTp, hTb⟩ := hD
  set V := vword (callSegs cs x W) with hV
  set dc0 : Cfg kD Bool SD V := Cfg.init (q0 cs.dec) V with hdc0
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  -- the setup step
  have hsetup : (compileTM P l₀ D q0).step (seam c0) =
      mkCfg (some (.sim l (q0 cs.dec) 0 false true none)) c0.inputPos c0.workTapes
        (fun r => c0.workTapePos r + ((if r ∈ cs.args then -1 else 0 : SignType) : ℤ))
        (fun _ _ => none) (fun _ => 0) c0.output := by
    rw [seam_eq_mkCfg]
    unfold MultiTapeTM.step
    simp only [mkCfg_state, hl, Option.map_some]
    simp only [compileTM, ctr, hcall]
    rw [apply_moves, moveInputPos_zero]
  -- the first halting time of the decider
  have hex : ∃ t, (D.runFrom dc0 t).state = none := ⟨T, hTh⟩
  set T0 := Nat.find hex with hT0def
  have hT0 : (D.runFrom dc0 T0).state = none := Nat.find_spec hex
  have hT0le : T0 ≤ T := Nat.find_min' hex hTh
  have hlive : ∀ t < T0, (D.runFrom dc0 t).state ≠ none := fun t ht => Nat.find_min hex ht
  have hfin : D.runFrom dc0 T = D.runFrom dc0 T0 := by
    rw [show T = T0 + (T - T0) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hT0]
  have hT0pos : 0 < T0 := by
    rcases Nat.eq_zero_or_pos T0 with h | h
    · rw [h] at hT0; simp [dc0] at hT0
    · exact h
  -- the simulation relation at the start
  have hsim0 : SimRel c0 l cs W ((compileTM P l₀ D q0).step (seam c0)) dc0 := by
    have hw0 := wlen_zero_le cs x W
    let tp : TPos := if wlen (callSegs cs x W) 0 = 0 then .right else .cell 0 false
    refine ⟨q0 cs.dec, 0, false, true, tp, ?_, rfl, ?_⟩
    · rw [hsetup]; rfl
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [tp]; split_ifs with h <;> simp [TPos.Valid]; omega
    · simp only [tp]; split_ifs <;> simp [Consistent]
    · simp only [tp, dc0, Cfg.init]
      split_ifs with h
      · simp only [vpos, wlen, rlen] at h ⊢; split <;> simp_all
      · simp [vpos, off_zero, cellOff]
    · rw [hsetup]
      simp only [mkCfg, tp, inPos, Fin.val_zero, ↓reduceIte, hin]
      split_ifs with h <;> simp [trackPos, h]
    · intro r; rw [hsetup]; simp [mkCfg]
    · intro r
      rw [hsetup]
      simp only [mkCfg, Fin.append_left, regPos]
      by_cases hr : r ∈ cs.args
      · simp [hr, hW0 r hr]
      · simp [hr]
    · intro i; rw [hsetup]; simp [mkCfg, dc0, Cfg.init]
    · intro i; rw [hsetup]; simp [mkCfg, dc0, Cfg.init]
    · rw [hsetup]; rfl
  -- the simulation, up to the halt
  have hsim : ∀ t ≤ T0, (t < T0 → SimRel c0 l cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t)
        (D.runFrom dc0 t)) ∧
      (t = T0 → HaltRel c0 l cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t) (D.runFrom dc0 t)) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨fun _ => hsim0, fun h => absurd h (by omega)⟩
    | succ t ih =>
      intro ht
      have h := (ih (by omega)).1 (by omega)
      have hs := sim_step l P D q0 hcall hW hnd h (l₀ := l₀)
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step']
      constructor
      · intro hlt
        apply hs.1
        rw [← MultiTapeTM.runFrom_succ_eq_step']
        exact hlive _ hlt
      · intro heq
        apply hs.2
        rw [← MultiTapeTM.runFrom_succ_eq_step', heq]
        exact hT0
  -- the halt
  obtain ⟨s, par, dir, tp, hgst, -, R⟩ := (hsim T0 le_rfl).2 rfl
  have hout0 : (D.runFrom dc0 T0).output = [b] := by rw [← hfin]; exact hTo
  have hb : ((D.runFrom dc0 T0).output.head?.getD false) = b := by rw [hout0]; rfl
  set gH := (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0 with hgH
  have hgHeq : gH = mkCfg (some (.ret1 l s dir b)) gH.inputPos c0.workTapes
      (regPos c0 cs W s tp) (fun _ _ => none) (fun _ => 0) c0.output := by
    refine Cfg.ext (by rw [hgst, hb]; rfl) rfl ?_ ?_ R.out
    · funext i z
      refine Fin.addCases (fun r => ?_) (fun j => ?_) i
      · simp [mkCfg, R.regTape]
      · simp only [mkCfg, Fin.append_right, R.dTape]
        rw [← hfin, hTt]
    · funext i
      refine Fin.addCases (fun r => ?_) (fun j => ?_) i
      · simp [mkCfg, R.regPos]
      · simp only [mkCfg, Fin.append_right, R.dPos]
        rw [← hfin, hTp]
  -- the return: input rewind
  have hret1 : (compileTM P l₀ D q0).step gH =
      mkCfg (some (.ret2 l s dir b)) (moveInputPos gH.inputPos (-1)) c0.workTapes
        (regPos c0 cs W s tp) (fun _ _ => none) (fun _ => 0) c0.output := by
    conv_lhs => rw [hgHeq]
    unfold MultiTapeTM.step
    simp only [mkCfg_state]
    simp only [compileTM, ctr]
    rw [apply_inputOnly]
  have hj : (moveInputPos gH.inputPos (-1)).val ≤ x.length := by
    rw [show (-1 : SignType) = .neg from rfl, FinTM.moveInputPos_neg_val]
    have := gH.inputPos.isLt; omega
  obtain ⟨hb2, hr2⟩ := ret2_run P l₀ D q0 l cs hcall s dir b c0.workTapes (regPos c0 cs W s tp)
    (fun _ _ => none) (fun _ => 0) c0.output _ _ rfl hj
  -- the return: argument registers
  have hbox0 := regPos_box (c0 := c0) hnd s tp R.valid R.hs
  have hret0 : retPos cs (regPos c0 cs W s tp) 0 = regPos c0 cs W s tp := by
    funext r; simp [retPos]
  obtain ⟨T₃, hb3, hr3⟩ := regs_run P l₀ D q0 l cs hcall hnd s dir b W c0.workTapes hW
    (fun _ _ => none) (fun _ => 0) c0.output 1 c0.workTapePos (regPos c0 cs W s tp) hbox0
    (fun a ha hm => regPos_side hnd s par dir tp R.cons R.valid a ha hm)
    cs.args.length 0 (by omega)
  rw [hret0] at hb3 hr3
  have hretL : retPos cs (regPos c0 cs W s tp) cs.args.length = c0.workTapePos := by
    funext r
    unfold retPos
    by_cases hr : r ∈ cs.args
    · simp [hr, List.idxOf_lt_length_of_mem hr, hW0 r hr]
    · simp [hr, regPos]
  rw [hretL] at hr3
  -- assemble
  have hfinal : (mkCfg (some (CSt.prog (if b then cs.yes else cs.no))) 1 c0.workTapes
      c0.workTapePos (fun _ _ => none) (fun _ => 0) c0.output : Cfg (m + kD) Bool (CSt Λ SD m) x) =
      seam (kD := kD) (SD := SD)
        { c0 with state := some (if b then cs.yes else cs.no), inputPos := 1 } := by
    rw [seam_eq_mkCfg]; rfl
  refine ⟨1 + (T0 + (1 + ((moveInputPos gH.inputPos (-1)).val + 1 + T₃))), ?_, ?_⟩
  · -- the box along the whole call
    have hregBoxSeam : RegBox cs c0.workTapePos W c0.workTapePos := by
      intro r
      refine ⟨fun _ => rfl, fun hr => ?_⟩
      rw [hW0 r hr]; simp
    let Q : Cfg (m + kD) Bool (CSt Λ SD m) x → Prop := fun g =>
      RegBox cs c0.workTapePos W (fun r => g.workTapePos (Fin.castAdd kD r)) ∧
        ∀ i, |g.workTapePos (Fin.natAdd m i)| ≤ B
    show ∀ t ≤ _, Q ((compileTM P l₀ D q0).runFrom (seam c0) t)
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        refine ⟨by simpa [seam] using hregBoxSeam, fun i => by simp [seam]⟩
      · obtain rfl : t = 1 := by omega
        rw [show (compileTM P l₀ D q0).runFrom (seam c0) 1 = ((compileTM P l₀ D q0).step (seam c0)) from rfl]
        obtain ⟨_, _, _, _, _, _, _, R0⟩ := hsim0
        refine ⟨?_, fun i => ?_⟩
        · intro r; simp only [R0.regPos]; exact regPos_box hnd _ _ R0.valid R0.hs r
        · rw [R0.dPos]; simp [dc0, Cfg.init]
    rw [show (compileTM P l₀ D q0).runFrom (seam c0) 1 = (compileTM P l₀ D q0).step (seam c0)
      from rfl]
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      have hTR : ∃ s par dir tp, TrackRel c0 cs W ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) t)
          (D.runFrom dc0 t) s par dir tp := by
        rcases Nat.lt_or_ge t T0 with h | h
        · obtain ⟨_, s', par', dir', tp', -, -, R'⟩ := (hsim t ht).1 h
          exact ⟨s', par', dir', tp', R'⟩
        · obtain ⟨s', par', dir', tp', -, -, R'⟩ := (hsim t ht).2 (by omega)
          exact ⟨s', par', dir', tp', R'⟩
      obtain ⟨s', par', dir', tp', R'⟩ := hTR
      refine ⟨?_, fun i => ?_⟩
      · intro r; simp only [R'.regPos]; exact regPos_box hnd s' tp' R'.valid R'.hs r
      · rw [R'.dPos]; exact hTb t (by omega) i
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h
        rw [MultiTapeTM.runFrom_zero, ← hgH, hgHeq]
        exact ⟨fun r => by simpa [mkCfg] using hbox0 r, fun i => by simp [mkCfg]⟩
      · obtain rfl : t = 1 := by omega
        rw [show (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0) 1 =
          (compileTM P l₀ D q0).step gH from rfl, hret1]
        exact ⟨fun r => by simpa [mkCfg] using hbox0 r, fun i => by simp [mkCfg]⟩
    rw [show (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) T0) 1 =
      (compileTM P l₀ D q0).step gH from rfl, hret1]
    apply runFrom_forall_append (Q := Q)
    · intro t ht
      dsimp only [Q]
      rw [hb2 t ht]
      exact ⟨fun r => by simpa using hbox0 r, fun i => by simp⟩
    rw [hr2]
    intro t ht
    dsimp only [Q]
    obtain ⟨h1, h2⟩ := hb3 t ht
    refine ⟨h1, fun i => ?_⟩
    have := congrFun h2 i
    simp only [Function.comp_apply] at this
    rw [this]; simp
  · rw [MultiTapeTM.runFrom_add]
    change (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).step (seam c0)) _ = _
    rw [MultiTapeTM.runFrom_add, ← hgH, MultiTapeTM.runFrom_add]
    rw [show (compileTM P l₀ D q0).runFrom gH 1 = (compileTM P l₀ D q0).step gH from rfl, hret1,
      MultiTapeTM.runFrom_add, hr2, hr3, hfinal]


end Whole

end Complexity.LogProg
