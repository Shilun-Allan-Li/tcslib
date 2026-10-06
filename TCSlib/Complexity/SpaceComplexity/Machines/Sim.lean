/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Program

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulating a decider on a virtual input, step by step

The heart of the compiled machine of `TCSlib.Complexity.SpaceComplexity.Machines.Program`:
while a call is in progress, the compiled machine's configuration is related
(`Complexity.LogProg.SimRel`) to the decider's configuration on the virtual input, and one
compiled step simulates one decider step (`Complexity.LogProg.sim_step`).

The virtual input head is never stored: it is the head of the current segment's *track*
(the real input head for segment `0`, an argument register's head otherwise), read through
the track position bookkeeping of `TCSlib.Complexity.SpaceComplexity.Machines.Layout`.
Heads of segments before the current one rest on their right ends, heads of later segments
on their left ends.

## Main definitions

* `Complexity.LogProg.trackPos` — the real head position of a track position.
* `Complexity.LogProg.TrackRel` — the compiled configuration represents the decider's
  configuration with the virtual head at a given track position.
* `Complexity.LogProg.SimRel`, `Complexity.LogProg.HaltRel` — during the call, and right
  after the decider has halted.

## Main results

* `Complexity.LogProg.gstep_tmove` — the compiled machine's local bookkeeping `gstep`
  implements `tmove`.
* `Complexity.LogProg.sim_step` — one compiled step simulates one decider step.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

/-- The position of a track head, in register coordinates (word from cell `0`; the input
track is shifted by one). -/
def trackPos (segs : List Seg) (s : ℕ) : TPos → ℤ
  | .left => -1
  | .cell c _ => c
  | .right => wlen segs s

/-- Whether a track position is a cell. -/
def TPos.isCell : TPos → Bool
  | .cell _ _ => true
  | _ => false

/-- The consistency of the stored parity and direction with a track position. -/
def Consistent (segs : List Seg) (s : ℕ) (par dir : Bool) : TPos → Prop
  | .left => dir = false
  | .right => dir = true
  | .cell _ p => (seg segs s).2 = true → p = par

/-- **The local bookkeeping is `tmove`**: `gstep` computes the new segment of `tmove`, a
consistent parity and direction, and moves the current track's head to the new track
position; a change of segment happens only between the touching ends of two neighbouring
segments and moves no head.

**Proof sketch.** Case analysis on the move and the track position; `gstep` sees the track
position through `isCell` and the stored direction (which, by consistency, names the end
of the segment the head is on) and the parity (which, by consistency, is the copy in a
doubled segment). -/
lemma gstep_tmove (segs : List Seg) (s : ℕ) (hs : s < segs.length) (tp : TPos)
    (htp : tp.Valid segs s) (par dir : Bool) (hc : Consistent segs s par dir tp)
    (mv : SignType) :
    let G := gstep (seg segs s).2 (decide (s + 1 = segs.length)) (decide (s = 0)) s par dir
      tp.isCell mv
    let T := tmove segs s tp mv
    G.1 = T.1 ∧ Consistent segs T.1 G.2.1 G.2.2.1 T.2 ∧
      ((G.1 = s ∧ trackPos segs s T.2 = trackPos segs s tp + (G.2.2.2 : ℤ)) ∨
       (G.2.2.2 = 0 ∧ ((G.1 = s + 1 ∧ tp = .right ∧ T.2 = .left) ∨
          (G.1 + 1 = s ∧ tp = .left ∧ T.2 = .right)))) := by
  generalize hsg : seg segs s = sg at *
  obtain ⟨w, dd⟩ := sg
  simp only [TPos.Valid, wlen, hsg] at htp
  cases mv <;> cases tp
  case neg.right =>
    simp only [Consistent] at hc
    subst hc
    simp only [gstep, tmove, TPos.isCell, wlen, hsg, Bool.false_eq_true, ↓reduceIte]
    split_ifs with h
    · simp [trackPos, wlen, hsg, h, Consistent, SignType.neg_eq_neg_one]
    · simp only [trackPos, wlen, hsg, Consistent, SignType.neg_eq_neg_one,
        SignType.coe_neg_one, true_and, implies_true]
      left
      omega
  all_goals
    simp only [Consistent, hsg] at hc
    simp only [gstep, tmove, TPos.isCell, wlen, hsg]
    (try split_ifs) <;>
    first
    | omega
    | (simp [Consistent, trackPos, wlen, hsg, SignType.pos_eq_one,
        SignType.neg_eq_neg_one, SignType.coe_one] at * <;> omega)
    | simp_all

/-- The input symbol under the head, by position: the left blank at `0`, then the input. -/
lemma inputSymbol_eq {k : ℕ} {S : Type} {x : List Bool} (cfg : Cfg k Bool S x) :
    cfg.inputSymbol = if cfg.inputPos.val = 0 then none else x[cfg.inputPos.val - 1]? := by
  have hlt := cfg.inputPos.isLt
  split_ifs with h
  · have hz : cfg.inputPos = 0 := Fin.ext h
    simp [Cfg.inputSymbol, hz]
  · exact FinTM.inputSymbol_at cfg (cfg.inputPos.val - 1) (by omega) (by omega)

/-! ## The segments of a call -/

/-- Inside the leading run of `1`s, the input reads `1`. -/
lemma takeWhile_true_getElem? (x : List Bool) (c : ℕ)
    (hc : c < (x.takeWhile (· = true)).length) : x[c]? = some true := by
  induction x generalizing c with
  | nil => simp at hc
  | cons b x ih =>
    cases b with
    | false => simp at hc
    | true =>
      cases c with
      | zero => rfl
      | succ c =>
        simp only [List.takeWhile_cons, decide_true, ↓reduceIte, List.length_cons] at hc
        simpa using ih c (by omega)

/-- Right after the leading run of `1`s, the input does not read `1`. -/
lemma takeWhile_true_end (x : List Bool) : x[(x.takeWhile (· = true)).length]? ≠ some true := by
  induction x with
  | nil => simp
  | cons b x ih =>
    cases b with
    | false => simp
    | true => simpa using ih

/-- In `whole` mode the leading segment is the input, doubled. -/
lemma Mode.seg0_whole {md : Mode} (h : md = .whole) (x : List Bool) :
    md.seg0 x = (x, true) := by subst h; rfl

/-- In `unaryFst` mode the leading segment is the leading run of `1`s of the input, plain. -/
lemma Mode.seg0_unaryFst {md : Mode} (h : md = .unaryFst) (x : List Bool) :
    md.seg0 x = (x.takeWhile (· = true), false) := by subst h; rfl

section Segs

variable {m d : ℕ} {Λ : Type} (cs : CallSpec m d Λ) (x : List Bool) (W : Fin m → List Bool)

/-- Segment `0` of a call's virtual input is the mode's leading segment. -/
@[simp] lemma seg_callSegs_zero : seg (callSegs cs x W) 0 = cs.mode.seg0 x := rfl

/-- Segment `a + 1` of a call's virtual input is the word of argument register `a`, doubled
unless it is the last. -/
lemma seg_callSegs_succ (a : ℕ) (ha : a < cs.args.length) :
    seg (callSegs cs x W) (a + 1) = (W cs.args[a], decide (a + 1 < cs.args.length)) := by
  simp only [callSegs, seg_cons_succ]
  rw [seg_argSegs _ a (by simpa using ha)]
  simp

/-- `segDbl` tells whether segment `s` of a call's virtual input is doubled. -/
lemma segDbl_eq (s : ℕ) (hs : s < cs.args.length + 1) :
    segDbl cs s = (seg (callSegs cs x W) s).2 := by
  unfold segDbl
  split_ifs with h
  · subst h; simp only [seg_callSegs_zero]; cases cs.mode <;> rfl
  · obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
    rw [seg_callSegs_succ cs x W a (by omega)]

/-- The leading segment's word is no longer than the input. -/
lemma wlen_zero_le : wlen (callSegs cs x W) 0 ≤ x.length := by
  simp only [wlen, seg_callSegs_zero]
  cases cs.mode
  · simp [Mode.seg0]
  · simp only [Mode.seg0]; exact (List.takeWhile_prefix _).length_le

/-- `segReg` gives the argument register of segment `s ≥ 1`. -/
lemma segReg_eq (s : ℕ) (h : 0 < m) (h1 : 0 < s) (h2 : s ≤ cs.args.length) :
    segReg cs s h = cs.args[s - 1] := by
  simp [segReg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s - 1 < cs.args.length by omega)]

end Segs

/-! ## The simulation relation -/

section Rel

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool} (c0 : Cfg m Bool Λ x) (l : Λ)
  (cs : CallSpec m d Λ) (W : Fin m → List Bool)

/-- The position of register `r` while the virtual head is at segment `s`, track position
`tp`: argument registers before the current segment rest on their right ends, later ones on
their left ends; other registers keep their positions. -/
def regPos (s : ℕ) (tp : TPos) (r : Fin m) : ℤ :=
  if r ∈ cs.args then
    if cs.args.idxOf r + 1 < s then wlen (callSegs cs x W) (cs.args.idxOf r + 1)
    else if s < cs.args.idxOf r + 1 then -1 else trackPos (callSegs cs x W) s tp
  else c0.workTapePos r

/-- The real input head position while the virtual head is at segment `s`, track position
`tp` (the input track is shifted by one cell). -/
def inPos (cs : CallSpec m d Λ) (x : List Bool) (W : Fin m → List Bool) (s : ℕ) (tp : TPos) :
    ℕ :=
  if s = 0 then (trackPos (callSegs cs x W) 0 tp + 1).toNat else wlen (callSegs cs x W) 0 + 1

/-- The compiled configuration `g` represents the decider configuration `dc` with the
virtual head at segment `s`, track position `tp`; registers hold their call-time contents. -/
structure TrackRel (g : Cfg (m + kD) Bool (CSt Λ SD m) x)
    (dc : Cfg kD Bool SD (vword (callSegs cs x W))) (s : ℕ) (par dir : Bool) (tp : TPos) :
    Prop where
  hs : s < cs.args.length + 1
  valid : tp.Valid (callSegs cs x W) s
  cons : Consistent (callSegs cs x W) s par dir tp
  vpos : dc.inputPos.val = vpos (callSegs cs x W) s tp
  inp : g.inputPos.val = inPos cs x W s tp
  regTape : ∀ r, g.workTapes (Fin.castAdd kD r) = c0.workTapes r
  regPos : ∀ r, g.workTapePos (Fin.castAdd kD r) = regPos c0 cs W s tp r
  dTape : ∀ i, g.workTapes (Fin.natAdd m i) = dc.workTapes i
  dPos : ∀ i, g.workTapePos (Fin.natAdd m i) = dc.workTapePos i
  out : g.output = c0.output

/-- During a call: the compiled machine simulates the live decider configuration `dc`. -/
def SimRel (g : Cfg (m + kD) Bool (CSt Λ SD m) x)
    (dc : Cfg kD Bool SD (vword (callSegs cs x W))) : Prop :=
  ∃ (q : SD) (s : Fin (m + 1)) (par dir : Bool) (tp : TPos),
    g.state = some (.sim l q s par dir dc.output.head?) ∧ dc.state = some q ∧
    TrackRel c0 cs W g dc s par dir tp

/-- Right after the decider halted: the compiled machine enters its return phase. -/
def HaltRel (g : Cfg (m + kD) Bool (CSt Λ SD m) x)
    (dc : Cfg kD Bool SD (vword (callSegs cs x W))) : Prop :=
  ∃ (s : Fin (m + 1)) (par dir : Bool) (tp : TPos),
    g.state = some (.ret1 l s dir (dc.output.head?.getD false)) ∧ dc.state = none ∧
    TrackRel c0 cs W g dc s par dir tp

variable {c0 cs W}

/-- **The track reading**: the compiled machine's reading of the current track classifies
the track position correctly and yields the virtual input symbol there.

**Proof sketch.** Case on the track position. On a cell of a segment the compiled machine reads
the input letter (segment `0`) or the register letter under the register head, which `TrackRel`
ties to the virtual input. On a left or right blank the read symbol is blank, and `isCharRead`
and `virtSym` reconstruct the separator or end symbol from the segment index and direction
(`inputSymbol_vpos`). -/
lemma track_read (hW : ∀ r ∈ cs.args, c0.workTapes r = FinTM.bufferTape (W r))
    (hnd : cs.args.Nodup) {g : Cfg (m + kD) Bool (CSt Λ SD m) x}
    {dc : Cfg kD Bool SD (vword (callSegs cs x W))} {s : ℕ} {par dir : Bool} {tp : TPos}
    (R : TrackRel c0 cs W g dc s par dir tp) :
    let rd : Option Bool :=
      if s = 0 then g.inputSymbol
      else if hm : 0 < m then g.workTapeSymbols (Fin.castAdd kD (segReg cs s hm)) else none
    isCharRead cs.mode s rd = tp.isCell ∧
      virtSym cs.mode s (cs.args.length + 1) dir rd = vsym (callSegs cs x W) s tp := by
  have hval := R.valid
  have hcons := R.cons
  by_cases hs0 : s = 0
  · subst hs0
    have hin := R.inp
    simp only [inPos, ↓reduceIte] at hin
    have hrd : g.inputSymbol = if g.inputPos.val = 0 then none
        else x[g.inputPos.val - 1]? := inputSymbol_eq g
    simp only [↓reduceIte]
    rw [hrd, hin]
    have hw0 := wlen_zero_le cs x W
    cases tp with
    | left =>
      simp only [Consistent] at hcons
      subst hcons
      simp [trackPos, isCharRead, virtSym, vsym, TPos.isCell]
    | cell c p =>
      simp only [TPos.Valid, wlen, seg_callSegs_zero] at hval
      simp only [trackPos, vsym, seg_callSegs_zero, TPos.isCell]
      have hc : ((c : ℤ) + 1).toNat = c + 1 := by omega
      rw [hc]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      cases hm : cs.mode with
      | whole =>
        rw [Mode.seg0_whole hm] at hval
        simp only [Mode.seg0]
        simp [isCharRead, virtSym, hval]
      | unaryFst =>
        rw [Mode.seg0_unaryFst hm] at hval
        simp only [Mode.seg0]
        have hx := takeWhile_true_getElem? x c hval
        have hx' : (x.takeWhile (· = true))[c]? = some true := by
          rw [List.getElem?_eq_getElem hval]
          have := List.mem_takeWhile_imp (List.getElem_mem hval)
          simpa using this
        simp only [isCharRead, virtSym, and_self, ↓reduceIte, hx, decide_true]
        simpa using hx'.symm
    | right =>
      simp only [Consistent] at hcons
      subst hcons
      simp only [trackPos, vsym, TPos.isCell, wlen, seg_callSegs_zero]
      have hc : (((cs.mode.seg0 x).1.length : ℤ) + 1).toNat = (cs.mode.seg0 x).1.length + 1 := by
        omega
      rw [hc]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, length_callSegs]
      have hnot : isCharRead cs.mode 0 x[(cs.mode.seg0 x).1.length]? = false := by
        cases hm : cs.mode with
        | whole => simp [isCharRead, Mode.seg0]
        | unaryFst =>
          simp only [isCharRead, and_self, ↓reduceIte, decide_eq_false_iff_not, Mode.seg0]
          exact takeWhile_true_end x
      refine ⟨hnot, ?_⟩
      simp only [virtSym, hnot, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> first | rfl | omega
  · obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
    have ha : a < cs.args.length := by have := R.hs; omega
    have hm : 0 < m := Fin.pos cs.args[a]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, dif_pos hm]
    rw [segReg_eq cs (a + 1) hm (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    have hidx : cs.args.idxOf cs.args[a] = a := List.idxOf_getElem hnd a ha
    have hreg : g.workTapeSymbols (Fin.castAdd kD cs.args[a]) =
        FinTM.bufferTape (W cs.args[a]) (trackPos (callSegs cs x W) (a + 1) tp) := by
      simp only [Cfg.workTapeSymbols, R.regTape, R.regPos, regPos, List.getElem_mem,
        ↓reduceIte, hidx, lt_self_iff_false]
      rw [hW _ (List.getElem_mem ha)]
    rw [hreg]
    have hseg := seg_callSegs_succ cs x W a ha
    cases tp with
    | left =>
      simp only [Consistent] at hcons
      subst hcons
      simp [trackPos, isCharRead, virtSym, vsym, TPos.isCell, FinTM.bufferTape]
    | cell c p =>
      simp only [TPos.Valid, wlen, hseg] at hval
      simp [trackPos, isCharRead, virtSym, vsym, TPos.isCell, FinTM.bufferTape, hseg,
        List.getElem?_eq_getElem hval]
    | right =>
      simp only [Consistent] at hcons
      subst hcons
      simp only [trackPos, wlen, hseg, TPos.isCell]
      have hb : FinTM.bufferTape (W cs.args[a]) ((W cs.args[a]).length : ℤ) = none := by
        simp
      rw [hb]
      simp only [isCharRead, virtSym, vsym, Option.isSome_none,
        ↓reduceIte, length_callSegs]
      simp only [Nat.add_one_ne_zero, false_and, ↓reduceIte, Bool.false_eq_true, true_and]
      split_ifs <;> first | rfl | omega

/-- A valid track position lies between the two ends. -/
lemma trackPos_bounds (segs : List Seg) (s : ℕ) (tp : TPos) (h : tp.Valid segs s) :
    -1 ≤ trackPos segs s tp ∧ trackPos segs s tp ≤ wlen segs s := by
  cases tp <;> simp only [trackPos, TPos.Valid] at h ⊢ <;> omega

/-- The register positions after one simulated step.

**Proof sketch.** Case on the step. Within a segment, only the head of that segment's register
(if any) moves, by `mv`. Crossing between segments (`mv = 0`), the register positions are
unchanged and the track positions at the old and new segments agree. Unfold `regPos` in each
case. -/
lemma regPos_after (hnd : cs.args.Nodup) (s : ℕ) (tp : TPos) (G1 : ℕ) (T2 : TPos)
    (mv : SignType)
    (hcase : (G1 = s ∧ trackPos (callSegs cs x W) s T2 =
        trackPos (callSegs cs x W) s tp + (mv : ℤ)) ∨
      (mv = 0 ∧ ((G1 = s + 1 ∧ tp = .right ∧ T2 = .left) ∨
        (G1 + 1 = s ∧ tp = .left ∧ T2 = .right))))
    (r : Fin m) (hm : 0 < m) (hsl : s ≤ cs.args.length) :
    regPos c0 cs W s tp r + (if s ≠ 0 ∧ r = segReg cs s hm then (mv : ℤ) else 0) =
      regPos c0 cs W G1 T2 r := by
  have hseg : ∀ (h0 : s ≠ 0), segReg cs s hm = cs.args[s - 1]'(by omega) := fun h0 =>
    segReg_eq cs s hm (by omega) hsl
  by_cases hr : r ∈ cs.args
  · have hidx := List.idxOf_lt_length_of_mem hr
    have hget : cs.args[cs.args.idxOf r] = r := List.getElem_idxOf hidx
    -- `r` is the current register iff its index is `s - 1`
    have hcur : (s ≠ 0 ∧ r = segReg cs s hm) ↔ cs.args.idxOf r + 1 = s := by
      constructor
      · rintro ⟨h0, rfl⟩
        rw [hseg h0, List.idxOf_getElem hnd]; omega
      · intro h
        refine ⟨by omega, ?_⟩
        rw [hseg (by omega)]
        conv_lhs => rw [← hget]
        congr 1; omega
    simp only [regPos, hr, ↓reduceIte]
    rcases hcase with ⟨rfl, ht⟩ | ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩
    · by_cases hc : cs.args.idxOf r + 1 = G1
      · rw [if_pos (hcur.mpr hc)]
        simp only [show ¬ (cs.args.idxOf r + 1 < G1) by omega, ↓reduceIte,
          show ¬ (G1 < cs.args.idxOf r + 1) by omega, ht]
      · rw [if_neg (fun h => hc (hcur.mp h))]
        split_ifs <;> first | rfl | omega
    · simp only [SignType.coe_zero, ite_self, add_zero]
      split_ifs <;> (try simp only [trackPos]) <;>
        first | rfl | omega | (rw [show cs.args.idxOf r + 1 = s by omega])
    · simp only [SignType.coe_zero, ite_self, add_zero]
      split_ifs <;> (try simp only [trackPos]) <;>
        first | rfl | omega | (rw [show cs.args.idxOf r + 1 = G1 by omega])
  · have hne : ¬ (s ≠ 0 ∧ r = segReg cs s hm) := by
      rintro ⟨h0, rfl⟩
      rw [hseg h0] at hr
      exact hr (List.getElem_mem _)
    simp only [regPos, hr, ↓reduceIte, hne, add_zero]

/-- The input head position after one simulated step.

**Proof sketch.** Case on the step. Within segment `0` the input head moves by `mv`, and within
other segments it stays. Crossing between segments it stays, and the input positions of the two
adjacent track positions agree. Unfold `inPos` in each case. -/
lemma inPos_after (s : ℕ) (tp : TPos) (htp : tp.Valid (callSegs cs x W) s) (G1 : ℕ) (T2 : TPos)
    (hT2 : T2.Valid (callSegs cs x W) G1) (mv : SignType)
    (hcase : (G1 = s ∧ trackPos (callSegs cs x W) s T2 =
        trackPos (callSegs cs x W) s tp + (mv : ℤ)) ∨
      (mv = 0 ∧ ((G1 = s + 1 ∧ tp = .right ∧ T2 = .left) ∨
        (G1 + 1 = s ∧ tp = .left ∧ T2 = .right))))
    (p : Fin (x.length + 2)) (hp : p.val = inPos cs x W s tp) :
    (moveInputPos p (if s = 0 then mv else 0)).val = inPos cs x W G1 T2 := by
  have hw0 := wlen_zero_le cs x W
  rcases hcase with ⟨rfl, ht⟩ | ⟨rfl, hc⟩
  · by_cases hs0 : G1 = 0
    · subst hs0
      simp only [↓reduceIte, inPos] at hp ⊢
      have hb := trackPos_bounds _ 0 tp htp
      have hb' := trackPos_bounds _ 0 T2 hT2
      have hpv : p = ⟨p.val, p.isLt⟩ := rfl
      rw [hpv, moveInputPos_val]
      cases mv <;> simp only [SignType.zero_eq_zero, SignType.coe_zero, SignType.pos_eq_one,
        SignType.coe_one, SignType.neg_eq_neg_one, SignType.coe_neg_one] at ht ⊢ <;> omega
    · simp only [hs0, ↓reduceIte, inPos] at hp ⊢
      rw [moveInputPos_zero, hp]
  · rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩
    · simp only [ite_self, moveInputPos_zero, hp, inPos,
        Nat.add_one_ne_zero, ↓reduceIte]
      split_ifs with h
      · subst h; simp [trackPos]
      · rfl
    · simp only [moveInputPos_zero, hp, inPos,
        show s ≠ 0 by omega, ↓reduceIte]
      split_ifs with h
      · subst h; simp [trackPos]
      · rfl

/-- The head of an appended optional emission. -/
lemma head?_append_toList (l : List Bool) (o : Option Bool) :
    (l ++ o.toList).head? = (l.head? <|> o) := by
  cases l <;> cases o <;> rfl


/-- **One compiled step simulates one decider step.** If the compiled configuration `g`
simulates the live decider configuration `dc`, then after one step of each, `g` simulates
`dc` again, or — if the decider has just halted — `g` has entered its return phase.

**Proof sketch.** The track reading presents the decider's own input symbol
(`track_read`, `inputSymbol_vpos`) and the decider block holds the decider's tapes, so the
compiled machine applies exactly the decider's action to the decider block. The track
bookkeeping `gstep` is `tmove` (`gstep_tmove`), which moves the virtual head as the machine
model does (`vpos_tmove`); the real heads follow (`inPos_after`, `regPos_after`). The
emission is recorded, not written. -/
theorem sim_step {l₀ : Λ} (P : RProg m d Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (hcall : P.call l = some cs)
    (hW : ∀ r ∈ cs.args, c0.workTapes r = FinTM.bufferTape (W r)) (hnd : cs.args.Nodup)
    {g : Cfg (m + kD) Bool (CSt Λ SD m) x} {dc : Cfg kD Bool SD (vword (callSegs cs x W))}
    (h : SimRel c0 l cs W g dc) :
    ((D.step dc).state ≠ none →
        SimRel c0 l cs W ((compileTM P l₀ D q0).step g) (D.step dc)) ∧
      ((D.step dc).state = none →
        HaltRel c0 l cs W ((compileTM P l₀ D q0).step g) (D.step dc)) := by
  obtain ⟨q, s, par, dir, tp, hg, hdc, R⟩ := h
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  have hsl : s.val < (callSegs cs x W).length := by simpa using R.hs
  have hread := track_read hW hnd R
  have hvs : dc.inputSymbol = vsym (callSegs cs x W) s tp :=
    inputSymbol_vpos _ s hsl tp R.valid dc R.vpos
  have hdr : (fun i => g.workTapeSymbols (Fin.natAdd m i)) = dc.workTapeSymbols := by
    funext i; simp only [Cfg.workTapeSymbols, R.dTape, R.dPos]
  set a := D.tr q dc.inputSymbol dc.workTapeSymbols with ha
  have hDstep : D.step dc = a.apply dc := by
    unfold MultiTapeTM.step; rw [hdc]
  -- the compiled action
  have hdbl := segDbl_eq cs x W s R.hs
  have hgt := gstep_tmove (callSegs cs x W) s hsl tp R.valid par dir R.cons a.inputTape
  simp only [length_callSegs] at hgt
  obtain ⟨hT1, hT2⟩ := tmove_valid (callSegs cs x W) s hsl tp R.valid a.inputTape
  set G := gstep (seg (callSegs cs x W) s).2 (decide (s.val + 1 = cs.args.length + 1))
    (decide (s.val = 0)) s par dir tp.isCell a.inputTape with hGdef
  obtain ⟨hG1, hcons', hcase⟩ := hgt
  set T := tmove (callSegs cs x W) s tp a.inputTape with hTdef
  have hGs : G.1 ≤ m := by rw [hG1]; simp at hT1; omega
  have htoFin : (toFin m G.1).val = G.1 := by simp [toFin]; omega
  have hgstep : (compileTM P l₀ D q0).step g =
      (⟨if s.val = 0 then G.2.2.2 else 0,
        Fin.append (fun r => (none, if h : 0 < m then
            (if s.val ≠ 0 ∧ r = segReg cs s h then G.2.2.2 else 0) else 0)) a.workTapes,
        none,
        some (match a.state with
          | some q' => .sim l q' (toFin m G.1) G.2.1 G.2.2.1 (dc.output.head? <|> a.output)
          | none => .ret1 l (toFin m G.1) G.2.2.1
              ((dc.output.head? <|> a.output).getD false))⟩ :
        Action (m + kD) Bool (CSt Λ SD m)).apply g := by
    unfold MultiTapeTM.step
    rw [hg]
    simp only [compileTM, ctr, hcall]
    rw [hread.1, hread.2, ← hvs, hdr, ← ha, hdbl]
    rfl
  have hout : (D.step dc).output.head? = (dc.output.head? <|> a.output) := by
    rw [hDstep]; simp only [Action.apply]; exact head?_append_toList _ _
  -- the track relation after the step
  have hR' : TrackRel c0 cs W ((compileTM P l₀ D q0).step g) (D.step dc) (toFin m G.1)
      G.2.1 G.2.2.1 T.2 := by
    rw [htoFin]
    have hTv : T.2.Valid (callSegs cs x W) G.1 := by rw [hG1]; exact hT2
    refine ⟨by rw [hG1]; simpa using hT1, hTv, by rw [hG1]; exact hcons', ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · -- virtual input head
      rw [hDstep, hG1]
      simp only [Action.apply]
      have hlt : vpos (callSegs cs x W) s tp < (vword (callSegs cs x W)).length + 2 := by
        rw [← R.vpos]; exact dc.inputPos.isLt
      have hp : dc.inputPos = ⟨vpos (callSegs cs x W) s tp, hlt⟩ := Fin.ext R.vpos
      rw [hp, ← vpos_tmove _ s hsl tp R.valid a.inputTape hlt]
    · -- real input head
      rw [hgstep]
      simp only [Action.apply]
      exact inPos_after s tp R.valid G.1 T.2 hTv G.2.2.2 hcase g.inputPos R.inp
    · intro r
      rw [hgstep]
      simp only [Action.apply, Fin.append_left]
      exact R.regTape r
    · intro r
      rw [hgstep]
      simp only [Action.apply, Fin.append_left]
      have hm : 0 < m := Fin.pos r
      rw [dif_pos hm, R.regPos r]
      have key := regPos_after (c0 := c0) hnd s tp G.1 T.2 G.2.2.2 hcase r hm (by have := R.hs; omega)
      rw [← key]
      congr 1
      split_ifs <;> simp
    · intro i
      rw [hgstep, hDstep]
      simp only [Action.apply, Fin.append_right, R.dTape, R.dPos]
    · intro i
      rw [hgstep, hDstep]
      simp only [Action.apply, Fin.append_right, R.dPos]
    · rw [hgstep]
      simp only [Action.apply, Option.toList_none, List.append_nil]
      exact R.out
  constructor
  · intro hlive
    obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hlive
    have haq : a.state = some q' := by rw [hDstep] at hq'; simpa [Action.apply] using hq'
    refine ⟨q', toFin m G.1, G.2.1, G.2.2.1, T.2, ?_, hq', hR'⟩
    rw [hgstep]
    simp only [Action.apply, haq, hout]
  · intro hhalt
    have haq : a.state = none := by rw [hDstep] at hhalt; simpa [Action.apply] using hhalt
    refine ⟨toFin m G.1, G.2.1, G.2.2.1, T.2, ?_, hhalt, hR'⟩
    rw [hgstep]
    simp only [Action.apply, haq, hout]

end Rel

end Complexity.LogProg
