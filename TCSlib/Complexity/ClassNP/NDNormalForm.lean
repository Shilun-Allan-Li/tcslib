/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.Build.StepBlock

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The linear-overhead coded normal form of an NDTM

[AB09, §3.2] ([BGW70]-style guess-then-verify): every bundled binary nondeterministic machine has a
coded two-work-tape equivalent (`Turing.CodeNDTM`) whose acceptance tracks the original's at linear
time overhead, forward with an explicit constant and backward in unbounded form. The
nondeterministic time hierarchy (`TCSlib.Complexity.Diagonalization.NTimeHierarchy`) diagonalizes
over these codes. This module isolates the normal-form statement and its supporting construction.

## Main definitions

No new definitions: the normal form is an existential contract.

## Main results

* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded normal form
  (statement; proof incomplete).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; no external text is required.)
-/

namespace Turing

namespace FinNDTM

/-- A finite-state machine with two binary work tapes has a code with identical acceptance.

**Proof sketch.** Relabel the finite state type by its equivalence with a finite ordinal.
Read the initial configuration and the relabeled run through their field equations, and
transfer halting and the exact output word in both directions. -/
private theorem nf_pack {S : Type} [Fintype S] (H : NDTM 2 Bool S) :
    ∃ M : CodeNDTM, ∀ (x : List Bool) (t : ℕ), M.toFinNDTM.AcceptsWithin x t ↔
      ∃ w : List Bool, w.length = t ∧ (H.runWith w (H.initCfg x)).state = none ∧
        (H.runWith w (H.initCfg x)).output = [true] := by
  have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨H.q₀⟩
  let e : S ≃ Fin (Fintype.card S - 1 + 1) :=
    (Fintype.equivFin S).trans (finCongr (by omega))
  refine ⟨⟨Fintype.card S - 1, H.relabelState e⟩, fun x t => ?_⟩
  rw [FinNDTM.acceptsWithin_iff]
  simp only [CodeNDTM.toFinNDTM_tm, CodeNDTM.toFinNDTM_k, CodeNDTM.toFinNDTM_State]
  have hinit : (H.relabelState e).initCfg x = (H.initCfg x).mapState e := by
    rw [NDTM.initCfg_eq, NDTM.initCfg_eq, NDTM.relabelState_q₀]
    apply Cfg.ext
    · rw [Cfg.init_state, Cfg.mapState_state, Cfg.init_state]; rfl
    · rw [Cfg.init_inputPos, Cfg.mapState_inputPos, Cfg.init_inputPos]
    · funext i p; rw [Cfg.mapState_workTapes, Cfg.init_workTapes, Cfg.init_workTapes]
    · funext i; rw [Cfg.mapState_workTapePos, Cfg.init_workTapePos, Cfg.init_workTapePos]
    · rw [Cfg.mapState_output, Cfg.init_output, Cfg.init_output]
  rw [hinit]
  constructor
  · rintro ⟨w, hw, hh, ho⟩
    refine ⟨w, hw, ?_, ?_⟩
    · rw [NDTM.relabelState_runWith, Cfg.mapState_state] at hh
      exact Option.map_eq_none_iff.mp hh
    · rwa [NDTM.relabelState_runWith, Cfg.mapState_output] at ho
  · rintro ⟨w, hw, hh, ho⟩
    refine ⟨w, hw, ?_, ?_⟩
    · rw [NDTM.relabelState_runWith, Cfg.mapState_state, hh]; rfl
    · rwa [NDTM.relabelState_runWith, Cfg.mapState_output]

/-- The trivial setup: a machine started at its exit meets `Turing.guessCtlRunTM`'s setup
hypotheses at time `0`, on every tape. -/
private theorem nf_setup {SP : Type} (P : MultiTapeTM 2 Bool SP) (z : List Bool) (j : Fin 2) :
    P.runFrom (P.initCfg z) 0 = P.initCfg z ∧ (P.initCfg z).state = some P.q₀ ∧
      (∀ u < 0, (P.runFrom (P.initCfg z) u).state ≠ some P.q₀) ∧
      (∀ p : ℕ, (P.initCfg z).workTapes j ((P.initCfg z).workTapePos j + p) = none) ∧
      (P.initCfg z).workTapes j ((P.initCfg z).workTapePos j - 1) = none := by
  refine ⟨MultiTapeTM.runFrom_zero, ?_, fun u hu => absurd hu (Nat.not_lt_zero u), fun p => ?_, ?_⟩
  · rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
  · rw [MultiTapeTM.initCfg_eq, Cfg.init_workTapes]
  · rw [MultiTapeTM.initCfg_eq, Cfg.init_workTapes]

/-- The display controller records the next position and the last completed record's flag. -/
private def nf_ctlStep (k : ℕ) (q : Fin (2 * k + 4) × Bool) (b : Bool) :
    Fin (2 * k + 4) × Bool :=
  if h : q.1.val = 2 * k + 3 then (0, b)
  else (⟨q.1.val + 1, by have := q.1.isLt; omega⟩, q.2)

/-- The controller stops precisely at a record boundary carrying a true end flag. -/
private def nf_ctlStop (k : ℕ) (q : Fin (2 * k + 4) × Bool) : Bool :=
  decide (q.1.val = 0) && q.2

/-- Starting at a record boundary, the position is the length read modulo the record width.

**Proof sketch.** Induct by appending one bit. At the last position the controller resets;
otherwise it advances by one. These are exactly the two cases of addition modulo the width. -/
private theorem nf_ctl_position (k : ℕ) (s : List Bool) (f : Bool) :
    (s.foldl (nf_ctlStep k) (0, f)).1.val = s.length % (2 * k + 4) := by
  induction s using List.reverseRecOn with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.zero_mod]
    rfl
  | append_singleton s b ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    rw [nf_ctlStep]
    split_ifs with h
    · have hm : s.length % (2 * k + 4) = 2 * k + 3 := by omega
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < 2 * k + 4 by omega), hm]
      have he : 2 * k + 3 + 1 = 2 * k + 4 := by omega
      simp only [he, Nat.mod_self, Fin.val_zero]
    · have hp := (s.foldl (nf_ctlStep k) (0, f)).1.isLt
      have hm : s.length % (2 * k + 4) + 1 < 2 * k + 4 := by omega
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < 2 * k + 4 by omega),
        Nat.mod_eq_of_lt hm]
      exact congrArg (fun n => n + 1) ih

/-- A nonempty prefix stops exactly when its length is a whole number of records and its
last bit is true.

**Proof sketch.** Separate the empty prefix and a prefix obtained by appending one bit.
The last position resets to zero and records that bit; every other position is nonzero. -/
private theorem nf_ctl_stop_iff (k : ℕ) (s : List Bool) :
    nf_ctlStop k (s.foldl (nf_ctlStep k) (0, false)) = true ↔
      s ≠ [] ∧ s.length % (2 * k + 4) = 0 ∧ s.getLastD false = true := by
  induction s using List.reverseRecOn with
  | nil => simp [nf_ctlStop]
  | append_singleton s b _ =>
    have hp := nf_ctl_position k (s ++ [b]) false
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, nf_ctlStep] at hp ⊢
    split_ifs at hp ⊢ with h
    · have hz : (s ++ [b]).length % (2 * k + 4) = 0 := hp.symm
      have hz' : (s.length + 1) % (2 * k + 4) = 0 := by
        simpa only [List.length_append, List.length_singleton] using hz
      simp [nf_ctlStop, hz']
    · have hn : (s ++ [b]).length % (2 * k + 4) ≠ 0 := by
        intro hz
        have hp' : (s.foldl (nf_ctlStep k) (0, false)).1.val + 1 =
            (s ++ [b]).length % (2 * k + 4) := hp
        omega
      have hn' : (s.length + 1) % (2 * k + 4) ≠ 0 := by
        simpa only [List.length_append, List.length_singleton] using hn
      simp [nf_ctlStop, hn']

/-- A record consists of its choice bit, two bits for each claimed read (input first), and
its end flag. A blank is encoded by `00`, false by `10`, and true by `11`. -/
private def nf_record (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool) (last : Bool)
    (p : Fin (2 * k + 4)) : Bool :=
  if p.val = 0 then b
  else if h : p.val = 2 * k + 3 then last
  else
    let i : Fin (k + 1) := ⟨(p.val - 1) / 2, by have := p.isLt; omega⟩
    if (p.val - 1) % 2 = 0 then (reads i).isSome else (reads i).getD false

/-- The last position of a record is its end flag. -/
private theorem nf_record_last (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool)
    (last : Bool) : nf_record k b reads last ⟨2 * k + 3, by omega⟩ = last := by
  rw [nf_record, if_neg (show 2 * k + 3 ≠ 0 by omega), dif_pos rfl]

/-- The first position of a record is its choice bit. -/
private theorem nf_record_choice (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool)
    (last : Bool) : nf_record k b reads last 0 = b := by
  rw [nf_record, if_pos (show (0 : Fin (2 * k + 4)).val = 0 from rfl)]

/-- Each claimed read occupies its designated presence bit and value bit.

**Proof sketch.** At the two designated offsets the quotient is the claimed-read index.
The remainder distinguishes its presence bit from its value bit. -/
private theorem nf_record_read (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool)
    (last : Bool) (i : Fin (k + 1)) :
    nf_record k b reads last ⟨2 * i.val + 1, by omega⟩ = (reads i).isSome ∧
      nf_record k b reads last ⟨2 * i.val + 2, by omega⟩ = (reads i).getD false := by
  have hi := i.isLt
  constructor
  · have hq : (2 * i.val + 1 - 1) / 2 = i.val := by omega
    have hr : (2 * i.val + 1 - 1) % 2 = 0 := by omega
    rw [nf_record, if_neg (show 2 * i.val + 1 ≠ 0 by omega),
      dif_neg (show 2 * i.val + 1 ≠ 2 * k + 3 by omega), if_pos hr]
    exact congrArg (fun j => (reads j).isSome) (Fin.ext hq)
  · have hq : (2 * i.val + 2 - 1) / 2 = i.val := by omega
    have hr : (2 * i.val + 2 - 1) % 2 ≠ 0 := by omega
    rw [nf_record, if_neg (show 2 * i.val + 2 ≠ 0 by omega),
      dif_neg (show 2 * i.val + 2 ≠ 2 * k + 3 by omega), if_neg hr]
    exact congrArg (fun j => (reads j).getD false) (Fin.ext hq)

/-- The display of a branch records the reads before each step, the step's choice bit, and
an end flag only on the last record. Actions and machine states are not guessed. -/
private def nf_display (N : FinNDTM Bool) (x w : List Bool) : List Bool :=
  List.ofFn fun i : Fin ((2 * N.k + 4) * w.length) =>
    let r : Fin w.length := ⟨i.val / (2 * N.k + 4),
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa only [Nat.mul_comm] using i.isLt)⟩
    let p : Fin (2 * N.k + 4) := ⟨i.val % (2 * N.k + 4), Nat.mod_lt _ (by omega)⟩
    let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
    nf_record N.k w[r.val] (Fin.cases c.inputSymbol c.workTapeSymbols)
      (decide (r.val + 1 = w.length)) p

/-- A display has exactly `2k + 4` bits per step. -/
private theorem nf_display_length (N : FinNDTM Bool) (x w : List Bool) :
    (nf_display N x w).length = (2 * N.k + 4) * w.length := by
  simp only [nf_display, List.length_ofFn]

/-- The end bit of the `r`th record of a display is true exactly on its last record.

**Proof sketch.** With the width `W = 2k + 4`, the final cell of record `r` has index
`W(r+1)-1`. Its quotient by `W` is `r` and its remainder is `W-1`, so the record encoder returns
the prescribed end flag. -/
private theorem nf_display_flag (N : FinNDTM Bool) (x w : List Bool) (r : Fin w.length) :
    (nf_display N x w)[(2 * N.k + 4) * (r.val + 1) - 1]? =
      some (decide (r.val + 1 = w.length)) := by
  let W := 2 * N.k + 4
  have hW : 0 < W := by omega
  have hprod : 0 < W * (r.val + 1) := Nat.mul_pos hW (by omega)
  have hi : W * (r.val + 1) - 1 < (nf_display N x w).length := by
    rw [nf_display_length]
    have hle := Nat.mul_le_mul_left W (show r.val + 1 ≤ w.length by omega)
    show W * (r.val + 1) - 1 < W * w.length
    omega
  have hd : (W * (r.val + 1) - 1) / W = r.val := by
    simpa only [Nat.zero_add, Nat.zero_div, Nat.add_sub_cancel] using
      Nat.mul_sub_div 0 W (r.val + 1) hprod
  have hm : (W * (r.val + 1) - 1) % W = 2 * N.k + 3 := by
    have he := Nat.mod_add_div (W * (r.val + 1) - 1) W
    rw [hd] at he
    have hdecomp : W * (r.val + 1) = W * r.val + W := by ring
    rw [hdecomp] at he ⊢
    have he' : W = 2 * N.k + 4 := rfl
    omega
  rw [List.getElem?_eq_getElem hi]
  simp only [nf_display, List.getElem_ofFn]
  have hp : (⟨(W * (r.val + 1) - 1) % W, Nat.mod_lt _ hW⟩ : Fin W) =
      ⟨2 * N.k + 3, by omega⟩ := Fin.ext hm
  rw [hp, nf_record_last]
  exact congrArg (fun a : ℕ => some (decide (a + 1 = w.length))) hd

/-- Every nonempty branch display first stops the controller exactly at its end.

**Proof sketch.** A stopping prefix must end on a record boundary. Its last bit is therefore
one of the display's end flags, which is false before the last record and true there. -/
private theorem nf_display_firstStop (N : FinNDTM Bool) (x w : List Bool) (hw : w ≠ []) :
    (∀ i < (nf_display N x w).length,
      nf_ctlStop N.k (((nf_display N x w).take i).foldl (nf_ctlStep N.k) (0, false)) = false) ∧
      nf_ctlStop N.k ((nf_display N x w).foldl (nf_ctlStep N.k) (0, false)) = true := by
  have hwpos : 0 < w.length := List.length_pos_iff.mpr hw
  have hW : 0 < 2 * N.k + 4 := by omega
  constructor
  · intro i hi
    apply Bool.eq_false_iff.mpr
    intro hs
    obtain ⟨hne, hm, hb⟩ := (nf_ctl_stop_iff N.k _).mp hs
    have hipos : 0 < i := by
      have hp := List.length_pos_iff.mpr hne
      rw [List.length_take, Nat.min_eq_left hi.le] at hp
      exact hp
    rw [List.length_take, Nat.min_eq_left hi.le] at hm
    have he := Nat.mod_add_div i (2 * N.k + 4)
    rw [hm, Nat.zero_add] at he
    have hn : 0 < i / (2 * N.k + 4) := by
      by_contra h
      have hnonneg : 0 ≤ i / (2 * N.k + 4) := Nat.zero_le _
      have hz : i / (2 * N.k + 4) = 0 := by omega
      rw [hz, Nat.mul_zero] at he
      omega
    have hlt : i / (2 * N.k + 4) < w.length := by
      apply (Nat.mul_lt_mul_left hW).mp
      rw [he, ← nf_display_length N x w]
      exact hi
    let r : Fin w.length := ⟨i / (2 * N.k + 4) - 1, by omega⟩
    have hr : r.val + 1 = i / (2 * N.k + 4) := by
      show i / (2 * N.k + 4) - 1 + 1 = i / (2 * N.k + 4)
      omega
    have hflag := nf_display_flag N x w r
    rw [hr, he, decide_eq_false (show ¬i / (2 * N.k + 4) = w.length by omega)] at hflag
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_take,
      Nat.min_eq_left hi.le, List.getElem?_take_of_lt (by omega), hflag,
      Option.getD_some] at hb
    exact Bool.noConfusion hb
  · apply (nf_ctl_stop_iff N.k _).mpr
    have hspos : 0 < (nf_display N x w).length := by
      rw [nf_display_length]
      exact Nat.mul_pos hW hwpos
    refine ⟨List.ne_nil_of_length_pos hspos, ?_, ?_⟩
    · rw [nf_display_length, Nat.mul_mod_right]
    · let r : Fin w.length := ⟨w.length - 1, by omega⟩
      have hr : r.val + 1 = w.length := by
        show w.length - 1 + 1 = w.length
        omega
      have hf := nf_display_flag N x w r
      rw [hr, decide_eq_true rfl] at hf
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, nf_display_length,
        hf, Option.getD_some]

/-- A stream that first stops the controller consists of a positive number of complete
records, with false end flags on all but the final record, whose end flag is true.

**Proof sketch.** The stopping criterion makes the total length a positive multiple of the
width. Apply the same criterion to each shorter record boundary: its flag must be false,
since a true flag there would contradict the first-stop hypothesis. -/
private theorem nf_firstStop_records (k : ℕ) (s : List Bool)
    (hlive : ∀ i < s.length, nf_ctlStop k ((s.take i).foldl (nf_ctlStep k) (0, false)) = false)
    (hstop : nf_ctlStop k (s.foldl (nf_ctlStep k) (0, false)) = true) :
    ∃ n : ℕ, 0 < n ∧ s.length = (2 * k + 4) * n ∧
      ∀ r < n, s[(2 * k + 4) * (r + 1) - 1]? = some (decide (r + 1 = n)) := by
  obtain ⟨hsne, hmod, hlast⟩ := (nf_ctl_stop_iff k s).mp hstop
  have hspos := List.length_pos_iff.mpr hsne
  have hW : 0 < 2 * k + 4 := by omega
  let n := s.length / (2 * k + 4)
  have hlen : s.length = (2 * k + 4) * n := by
    have h := Nat.mod_add_div s.length (2 * k + 4)
    rw [hmod, Nat.zero_add] at h
    exact h.symm
  have hn : 0 < n := by
    by_contra h
    have hnonneg : 0 ≤ n := Nat.zero_le _
    have hz : n = 0 := by omega
    rw [hz, Nat.mul_zero] at hlen
    omega
  refine ⟨n, hn, hlen, ?_⟩
  intro r hr
  let m := (2 * k + 4) * (r + 1)
  have hmpos : 0 < m := Nat.mul_pos hW (by omega)
  have hmle : m ≤ s.length := by
    rw [hlen]
    exact Nat.mul_le_mul_left _ (by omega)
  have hib : m - 1 < s.length := by omega
  have hlasttake : (s.take m).getLastD false = s[m - 1] := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_take,
      Nat.min_eq_left hmle, List.getElem?_take_of_lt (by omega),
      List.getElem?_eq_getElem hib, Option.getD_some]
  rw [List.getElem?_eq_getElem hib]
  by_cases he : r + 1 = n
  · have hm : m = s.length := by
      show (2 * k + 4) * (r + 1) = s.length
      rw [he, ← hlen]
    have htake : s.take m = s := by rw [hm, List.take_length]
    rw [htake] at hlasttake
    have hb : s[m - 1] = true := hlasttake.symm.trans hlast
    rw [hb, decide_eq_true he]
  · have hmlt : m < s.length := by
      rw [hlen]
      exact Nat.mul_lt_mul_of_pos_left (by omega) hW
    have hb : s[m - 1] = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hniltake : s.take m ≠ [] := by
        apply List.ne_nil_of_length_pos
        rw [List.length_take, Nat.min_eq_left hmle]
        exact hmpos
      have hz : (s.take m).length % (2 * k + 4) = 0 := by
        rw [List.length_take, Nat.min_eq_left hmle]
        exact Nat.mul_mod_right _ _
      have hf := (nf_ctl_stop_iff k (s.take m)).mpr
        ⟨hniltake, hz, hlasttake.trans htrue⟩
      rw [hlive m hmlt] at hf
      exact Bool.noConfusion hf
    rw [hb, decide_eq_false he]

/-- Displaying the first `t` steps of a long enough branch uses exactly `(2k + 4)t` bits. -/
private theorem nf_display_prefix_length (N : FinNDTM Bool) (x w : List Bool) (t : ℕ)
    (ht : t ≤ w.length) : (nf_display N x (w.take t)).length = (2 * N.k + 4) * t := by
  rw [nf_display_length, List.length_take, Nat.min_eq_left ht]

/-- A record's claimed reads; an absent presence bit decodes to blank regardless of its
value bit. Thus the unused code `01` also decodes to blank. -/
private def nf_decode (k : ℕ) (r : Fin (2 * k + 4) → Option Bool)
    (i : Fin (k + 1)) : Option Bool :=
  if (r ⟨2 * i.val + 1, by omega⟩).getD false then
    some ((r ⟨2 * i.val + 2, by omega⟩).getD false)
  else none

/-- Decoding a displayed record recovers each claimed read. -/
private theorem nf_decode_record (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool)
    (last : Bool) (i : Fin (k + 1)) :
    nf_decode k (fun p => some (nf_record k b reads last p)) i = reads i := by
  rw [nf_decode, Option.getD_some, Option.getD_some,
    (nf_record_read k b reads last i).1, (nf_record_read k b reads last i).2]
  cases reads i <;> rfl

/-- A false presence bit decodes to blank, including the unused fourth two-bit code. -/
private theorem nf_decode_absent (k : ℕ) (r : Fin (2 * k + 4) → Option Bool)
    (i : Fin (k + 1)) (h : (r ⟨2 * i.val + 1, by omega⟩).getD false = false) :
    nf_decode k r i = none := by
  rw [nf_decode, h]
  rfl

/-- The control check retains the simulated state, output summary, and an irreversible
failure flag. -/
private abbrev nf_Control (N : FinNDTM Bool) := Option N.State × Option Bool × Bool

/-- The sweep's finite control retains a position, a partially filled record, and its
control-check data. The record is a function on a finite type, never an unbounded list. -/
private abbrev nf_SweepState (N : FinNDTM Bool) :=
  (Fin (2 * N.k + 4) × (Fin (2 * N.k + 4) → Option Bool)) × nf_Control N

/-- Completing a record recomputes its action and checks its end flag. A record after
halting sets the failure flag. The summary includes emissions of halting transitions. -/
private def nf_complete (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Option Bool)
    (c : nf_Control N) : nf_Control N :=
  match c.1 with
  | none => (none, c.2.1, true)
  | some q =>
    let reads := nf_decode N.k r
    let a := N.tm.tr ((r 0).getD false) q (reads 0) (fun j => reads j.succ)
    (a.state, StepBlock.summaryEmit c.2.1 a.output,
      c.2.2 || decide ((r ⟨2 * N.k + 3, by omega⟩).getD false ≠ a.state.isNone))

/-- The bit fold stores one bit, completing the record exactly at its last position. -/
private def nf_sweepStep (N : FinNDTM Bool) (c : nf_SweepState N) (b : Bool) :
    nf_SweepState N :=
  let r := Function.update c.1.2 c.1.1 (some b)
  if h : c.1.1.val = 2 * N.k + 3 then
    ((0, fun _ => none), nf_complete N r c.2)
  else ((⟨c.1.1.val + 1, by have := c.1.1.isLt; omega⟩, r), c.2)

/-- The control sweep begins at the start state with an empty record and output summary. -/
private def nf_sweepInit (N : FinNDTM Bool) : nf_SweepState N :=
  ((0, fun _ => none), (some N.tm.q₀, none, false))

/-- The control check passes only at a complete record boundary, after halting, with an
accepting output summary and no failure. -/
private def nf_sweepPass (N : FinNDTM Bool) (c : nf_SweepState N) : Bool :=
  decide (c.1.1.val = 0) && c.2.1.isNone && decide (c.2.2.1 = some true) && !c.2.2.2

/-- On an encoded record, the completion rule is precisely the recomputed action and its
summary update; it marks an error exactly when the end flag disagrees with halting. -/
private theorem nf_complete_record (N : FinNDTM Bool) (b : Bool)
    (reads : Fin (N.k + 1) → Option Bool) (last : Bool) (q : N.State)
    (o : Option Bool) (failed : Bool) :
    let a := N.tm.tr b q (reads 0) (fun j => reads j.succ)
    nf_complete N (fun p => some (nf_record N.k b reads last p)) (some q, o, failed) =
      (a.state, StepBlock.summaryEmit o a.output, failed || decide (last ≠ a.state.isNone)) := by
  intro a
  have hd : nf_decode N.k (fun p => some (nf_record N.k b reads last p)) = reads := by
    funext i
    exact nf_decode_record N.k b reads last i
  rw [nf_complete, hd, nf_record_choice, nf_record_last, Option.getD_some, Option.getD_some]

/-- A failed control check remains failed after every subsequent completed record. -/
private theorem nf_complete_failed (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Option Bool)
    (q : Option N.State) (o : Option Bool) :
    (nf_complete N r (q, o, true)).2.2 = true := by
  cases q <;> simp only [nf_complete, Bool.true_or]

/-- Once the output summary is rejecting, later completed records cannot repair it. -/
private theorem nf_complete_other (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Option Bool)
    (q : Option N.State) (failed : Bool) :
    (nf_complete N r (q, some false, failed)).2.1 = some false := by
  cases q <;> simp only [nf_complete, StepBlock.summaryEmit_other]

/-- Before the last bit, scanning a record stores exactly its prefix and leaves the
simulated state, summary, and failure flag unchanged.

**Proof sketch.** Induct on the prefix length. Before the last position the fold performs
only one array update. At its index the newly stored bit extends the prefix; at other
indices the old prefix description remains valid. -/
private theorem nf_sweep_prefix (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Bool)
    (c : nf_Control N) (n : ℕ) (hn : n < 2 * N.k + 4) :
    (List.ofFn fun i : Fin n => r ⟨i.val, by omega⟩).foldl (nf_sweepStep N)
        ((0, fun _ => none), c) =
      ((⟨n, hn⟩, fun j => if j.val < n then some (r j) else none), c) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.foldl_nil]
    congr 2
  | succ n ih =>
    rw [List.ofFn_succ_last, List.foldl_append]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, nf_sweepStep]
    rw [dif_neg (show n ≠ 2 * N.k + 3 by omega)]
    congr 2
    funext j
    by_cases he : j = (⟨n, by omega⟩ : Fin (2 * N.k + 4))
    · subst j
      rw [Function.update_self, if_pos (show n < n + 1 by omega)]
    · rw [Function.update_of_ne he]
      have hne : j.val ≠ n := fun h => he (Fin.ext h)
      by_cases hlt : j.val < n
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- Scanning one whole record resets the parser and applies exactly one completion rule.

**Proof sketch.** Apply the prefix law to all but the last bit. The final array update
fills the only missing entry; the last-position branch resets the parser and checks the
completed record. -/
private theorem nf_sweep_record (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Bool)
    (c : nf_Control N) :
    (List.ofFn r).foldl (nf_sweepStep N) ((0, fun _ => none), c) =
      ((0, fun _ => none), nf_complete N (fun p => some (r p)) c) := by
  rw [List.ofFn_succ_last, List.foldl_append]
  have hf : (fun i : Fin (2 * N.k + 3) => r i.castSucc) =
      fun i => r ⟨i.val, by omega⟩ := by
    funext i
    rfl
  rw [hf, nf_sweep_prefix N r c (2 * N.k + 3) (by omega)]
  simp only [List.foldl_cons, List.foldl_nil, nf_sweepStep]
  rw [dite_true]
  have harray : Function.update
      (fun j : Fin (2 * N.k + 4) => if j.val < 2 * N.k + 3 then some (r j) else none)
      ⟨2 * N.k + 3, by omega⟩ (some (r ⟨2 * N.k + 3, by omega⟩)) =
        fun j => some (r j) := by
    funext j
    by_cases he : j = (⟨2 * N.k + 3, by omega⟩ : Fin (2 * N.k + 4))
    · subst j
      rw [Function.update_self]
    · rw [Function.update_of_ne he, if_pos (by
        have hj := j.isLt
        have hne : j.val ≠ 2 * N.k + 3 := fun h => he (Fin.ext h)
        omega)]
  rw [show (Fin.last (2 * N.k + 3) : Fin (2 * N.k + 4)) =
    ⟨2 * N.k + 3, by omega⟩ from rfl, harray]

/-- A completed live record updates the output summary exactly as its optional emission
updates the output word, including an emission on a halting transition. -/
private theorem nf_complete_output (N : FinNDTM Bool) (b : Bool)
    (reads : Fin (N.k + 1) → Option Bool) (last : Bool) (q : N.State)
    (o : List Bool) (failed : Bool) :
    let a := N.tm.tr b q (reads 0) (fun j => reads j.succ)
    (nf_complete N (fun p => some (nf_record N.k b reads last p))
      (some q, StepBlock.outputSummary o, failed)).2.1 =
        StepBlock.outputSummary (o ++ a.output.toList) := by
  intro a
  rw [nf_complete_record, StepBlock.outputSummary_append]

/-- The sweep's accepting summary means that the simulated output is exactly `[true]`. -/
private theorem nf_sweepPass_output (N : FinNDTM Bool) (c : nf_SweepState N) (o : List Bool)
    (ho : c.2.2.1 = StepBlock.outputSummary o) (hp : nf_sweepPass N c = true) :
    o = [true] := by
  rw [nf_sweepPass, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hp
  exact (StepBlock.outputSummary_true o).mp (ho.symm.trans (of_decide_eq_true hp.1.2))

/-- **The control sweep is the fold instance of `Turing.scanTM`.** From the stream start with
the scan's forward state, the scan on tape `0` reaches the completed bit fold at exactly
`2|s| + 2`, not at any `done` before, with every tape, head, the input head and the output as at
the start: the head of tape `0` is back at cell `0` with no separate rewind.

**Proof sketch.** Apply the framed scan contract with the fold and identity backward pass.
The scan-result equation identifies the final fold and unchanged word; the configuration
field equations show that every other tape, position and output field is preserved. -/
private theorem nf_sweep_run (N : FinNDTM Bool) (x s : List Bool) :
    (scanTM 2 0 (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N)).runFrom
        (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s)
        (2 * s.length + 2) =
      streamStartCfg x 0 (ScanPhase.done (s.foldl (nf_sweepStep N) (nf_sweepInit N))) s ∧
      ∀ t < 2 * s.length + 2, ∀ a,
        ((scanTM 2 0 (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N)).runFrom
          (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s) t).state ≠
            some (ScanPhase.done a) := by
  have hw : ∀ p : ℤ, -1 ≤ p → p ≤ (s.length : ℤ) →
      (streamStartCfg x (0 : Fin 2) (ScanPhase.fwd (nf_sweepInit N)) s).workTapes 0
        ((streamStartCfg x (0 : Fin 2) (ScanPhase.fwd (nf_sweepInit N)) s).workTapePos 0 + p) =
          FinTM.bufferTape s p := by
    intro p _ _
    rw [streamStartCfg_workTapes, streamStartCfg_workTapePos, if_pos rfl, zero_add]
  obtain ⟨h1, h2, -⟩ := scanTM_run_ofCfg (k := 2) (0 : Fin 2)
    (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N) s
    (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s) (streamStartCfg_state _ _ _ _) hw
  refine ⟨?_, h2⟩
  rw [h1, scanResult_fold]
  apply Cfg.ext
  · rw [streamStartCfg_state]
  · rw [streamStartCfg_inputPos, streamStartCfg_inputPos]
  · funext j q
    show (if j = 0 ∧ (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s).workTapePos j ≤ q ∧
        q < (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s).workTapePos j + (s.length : ℤ)
        then FinTM.bufferTape s
          (q - (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s).workTapePos j)
        else (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s).workTapes j q) = _
    rw [streamStartCfg_workTapes, streamStartCfg_workTapes, streamStartCfg_workTapePos]
    split_ifs with h hj <;> simp_all
  · funext j
    rw [streamStartCfg_workTapePos, streamStartCfg_workTapePos]
  · rw [streamStartCfg_output, streamStartCfg_output]

/-- A sequence of whole records is checked by folding their completion rules, with the
bit parser reset between records. -/
private theorem nf_sweep_records (N : FinNDTM Bool)
    (rs : List (Fin (2 * N.k + 4) → Bool)) (c : nf_Control N) :
    (rs.flatMap (fun r => List.ofFn r)).foldl (nf_sweepStep N) ((0, fun _ => none), c) =
      ((0, fun _ => none), rs.foldl (fun d r => nf_complete N (fun p => some (r p)) d) c) := by
  induction rs generalizing c with
  | nil => simp only [List.flatMap_nil, List.foldl_nil]
  | cons r rs ih =>
    rw [List.flatMap_cons, List.foldl_append, nf_sweep_record, ih, List.foldl_cons]

/-- A displayed branch is the concatenation of its fixed-width records.

**Proof sketch.** Split the finite index into its record index and offset by the product
formula for `List.ofFn`. Division and remainder by the width recover those two indices. -/
private theorem nf_display_records (N : FinNDTM Bool) (x w : List Bool) :
    nf_display N x w = (List.ofFn fun r : Fin w.length =>
      let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
      nf_record N.k w[r.val] (Fin.cases c.inputSymbol c.workTapeSymbols)
        (decide (r.val + 1 = w.length))).flatMap (fun r => List.ofFn r) := by
  rw [nf_display, List.ofFn_mul', List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext r
  apply congrArg List.ofFn
  funext p
  simp only [Nat.mul_add_div (show 0 < 2 * N.k + 4 by omega),
    Nat.div_eq_of_lt p.isLt, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]

/-- The sweep's final control on a display is the fold of that display's recomputed
records, starting at the original machine's start state and empty output. -/
private theorem nf_sweep_display (N : FinNDTM Bool) (x w : List Bool) :
    (nf_display N x w).foldl (nf_sweepStep N) (nf_sweepInit N) =
      ((0, fun _ => none), (List.ofFn fun r : Fin w.length =>
        let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
        nf_record N.k w[r.val] (Fin.cases c.inputSymbol c.workTapeSymbols)
          (decide (r.val + 1 = w.length))).foldl
            (fun d r => nf_complete N (fun p => some (r p)) d)
            (some N.tm.q₀, none, false)) := by
  rw [nf_display_records, nf_sweepInit, nf_sweep_records]

/-- For a live configuration, completing its genuine record gives the next state and
output summary, and compares the flag with the actual next configuration's halting status. -/
private theorem nf_complete_step (N : FinNDTM Bool) (x : List Bool)
    (c : Cfg N.k Bool N.State x) (b last failed : Bool) (hlive : c.state ≠ none) :
    nf_complete N
        (fun p => some (nf_record N.k b (Fin.cases c.inputSymbol c.workTapeSymbols) last p))
        (c.state, StepBlock.outputSummary c.output, failed) =
      ((N.tm.stepWith b c).state, StepBlock.outputSummary (N.tm.stepWith b c).output,
        failed || decide (last ≠ (N.tm.stepWith b c).state.isNone)) := by
  cases hq : c.state with
  | none => exact False.elim (hlive hq)
  | some q =>
    rw [nf_complete_record, NDTM.stepWith_of_some hq, Action.apply_state,
      Action.apply_output, StepBlock.outputSummary_append]
    simp only [Fin.cases_zero, Fin.cases_succ]

/-- On every prefix of a first-halting display, the control fold agrees with the genuine
state and output and has no failed end-flag check.

**Proof sketch.** Induct on the record count. The empty prefix is the initial configuration.
For a further record, the old configuration is live by hypothesis. Its genuine record
therefore gives exactly the next configuration's state and output summary. The next state
is halted exactly at the full word, which is exactly when the displayed end flag is set. -/
private theorem nf_sweep_control_prefix (N : FinNDTM Bool) (x w : List Bool)
    (hlive : ∀ r < w.length, (N.tm.runWith (w.take r) (N.tm.initCfg x)).state ≠ none)
    (hhalt : (N.tm.runWith w (N.tm.initCfg x)).state = none) (n : ℕ) (hn : n ≤ w.length) :
    (List.ofFn fun r : Fin n =>
      let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
      nf_record N.k (w[r.val]'(by omega)) (Fin.cases c.inputSymbol c.workTapeSymbols)
        (decide (r.val + 1 = w.length))).foldl
          (fun d r => nf_complete N (fun p => some (r p)) d) (some N.tm.q₀, none, false) =
      ((N.tm.runWith (w.take n) (N.tm.initCfg x)).state,
        StepBlock.outputSummary (N.tm.runWith (w.take n) (N.tm.initCfg x)).output, false) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.foldl_nil, List.take_zero, NDTM.runWith_nil,
      NDTM.initCfg_eq, Cfg.init_state, Cfg.init_output, StepBlock.outputSummary_nil]
  | succ n ih =>
    have hlt : n < w.length := by omega
    have hnext : N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x) =
        N.tm.stepWith w[n] (N.tm.runWith (w.take n) (N.tm.initCfg x)) := by
      rw [List.take_succ_eq_append_getElem hlt, NDTM.runWith_append,
        NDTM.runWith_cons, NDTM.runWith_nil]
    have hflag : decide (n + 1 = w.length) =
        (N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x)).state.isNone := by
      by_cases he : n + 1 = w.length
      · rw [he, decide_eq_true rfl, List.take_length, hhalt]
        rfl
      · rw [decide_eq_false he]
        have hnot := hlive (n + 1) (by omega)
        cases hs : (N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x)).state with
        | none => exact False.elim (hnot hs)
        | some q => rfl
    rw [List.ofFn_succ_last, List.foldl_append]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih (by omega), List.foldl_cons, List.foldl_nil,
      nf_complete_step N x _ _ _ _ (hlive n hlt), ← hnext, hflag]
    have hfalse : (decide ((N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x)).state.isNone ≠
        (N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x)).state.isNone) : Bool) = false :=
      decide_eq_false (fun h => h rfl)
    rw [hfalse, Bool.false_or]

/-- The control sweep passes the display of a branch that first halts at its end with output
exactly `[true]`.

**Proof sketch.** The display decomposition and record-fold law identify the bit fold with
the control fold. The prefix theorem at the whole word gives a halted state, the genuine
output summary, and no failure. The output-summary characterization then gives the pass bit. -/
private theorem nf_sweep_display_pass (N : FinNDTM Bool) (x w : List Bool)
    (hlive : ∀ r < w.length, (N.tm.runWith (w.take r) (N.tm.initCfg x)).state ≠ none)
    (hhalt : (N.tm.runWith w (N.tm.initCfg x)).state = none)
    (hout : (N.tm.runWith w (N.tm.initCfg x)).output = [true]) :
    nf_sweepPass N ((nf_display N x w).foldl (nf_sweepStep N) (nf_sweepInit N)) = true := by
  rw [nf_sweep_display]
  have hc := nf_sweep_control_prefix N x w hlive hhalt w.length (Nat.le_refl _)
  simp only [List.take_length] at hc
  rw [hc, nf_sweepPass, hhalt]
  have ho := (StepBlock.outputSummary_true _).mpr hout
  rw [ho]
  rfl

/-! ### The verifier's layout

The verifier is a deterministic two-tape machine composed by `Turing.phaseHostTM`. It runs the
control sweep (a fold by `Turing.scanTM` over the stream on tape `0`), then one replay per
replayed tape (the input first, then each work tape on tape `1`), each followed by the return of
tape `0` (`Turing.skipTM`, `Turing.skipBackTM`) and, for a work tape, the clear of tape `1`
(`Turing.skipTM`, `Turing.skipBackTM`, `Turing.clearTM`), and ends in a stationary verdict
park. It is silent: no phase emits output. -/

/-- The verifier's phases for `k` work tapes. -/
private inductive nf_Ph (k : ℕ) where
  /-- the control sweep, a scan fold over the stream on tape `0` -/
  | ctl
  /-- the replay of tape `j` (`none`: the input; `some j`: work tape `j`, on tape `1`) -/
  | rep (j : Option (Fin k))
  /-- the return of tape `0`, first step: from the blank after the stream, one cell right -/
  | aFwd (j : Option (Fin k))
  /-- the return of tape `0`, second step: back to cell `0` -/
  | aBack (j : Option (Fin k))
  /-- the clear of tape `1`, first step: to one past the visited region's right blank -/
  | bFwd (j : Fin k)
  /-- the clear of tape `1`, second step: back to the visited region's first cell -/
  | bBack (j : Fin k)
  /-- the clear of tape `1`, third step: blank the visited region -/
  | bClr (j : Fin k)
  /-- the verdict park -/
  | park
  deriving DecidableEq, Fintype

/-- The states of each phase, over the replay leaf's state type `SL`. -/
private def nf_St (N : FinNDTM Bool) (SL : Type) : nf_Ph N.k → Type
  | .ctl => ScanPhase (nf_SweepState N)
  | .rep _ => SL
  | .aFwd _ => SeekPhase
  | .aBack _ => SeekPhase
  | .bFwd _ => SeekPhase
  | .bBack _ => SeekPhase
  | .bClr _ => SweepPhase
  | .park => Bool

/-- Decidable equality of each phase's states, named: default synthesis does not reach
`ScanPhase (nf_SweepState N)` at the default instance size. -/
private instance nf_stDecEq (N : FinNDTM Bool) (SL : Type) [DecidableEq SL] :
    (i : nf_Ph N.k) → DecidableEq (nf_St N SL i)
  | .ctl => @instDecidableEqScanPhase _ inferInstance
  | .rep _ => (inferInstance : DecidableEq SL)
  | .aFwd _ => (inferInstance : DecidableEq SeekPhase)
  | .aBack _ => (inferInstance : DecidableEq SeekPhase)
  | .bFwd _ => (inferInstance : DecidableEq SeekPhase)
  | .bBack _ => (inferInstance : DecidableEq SeekPhase)
  | .bClr _ => (inferInstance : DecidableEq SweepPhase)
  | .park => (inferInstance : DecidableEq Bool)

/-- Finiteness of each phase's states, named as `nf_stDecEq` is. -/
private instance nf_stFintype (N : FinNDTM Bool) (SL : Type) [Fintype SL] :
    (i : nf_Ph N.k) → Fintype (nf_St N SL i)
  | .ctl => @instFintypeScanPhase _ inferInstance
  | .rep _ => (inferInstance : Fintype SL)
  | .aFwd _ => (inferInstance : Fintype SeekPhase)
  | .aBack _ => (inferInstance : Fintype SeekPhase)
  | .bFwd _ => (inferInstance : Fintype SeekPhase)
  | .bBack _ => (inferInstance : Fintype SeekPhase)
  | .bClr _ => (inferInstance : Fintype SweepPhase)
  | .park => (inferInstance : Fintype Bool)

/-- The verdict park: it stays at its state and moves nothing. -/
private def nf_park : MultiTapeTM 2 Bool Bool :=
  ⟨true, fun q _ _ => ⟨0, fun _ => (none, 0), none, some q⟩⟩

/-- The phase machines, over a replay leaf `L` per replayed tape. -/
private def nf_M (N : FinNDTM Bool) {SL : Type} (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) :
    (i : nf_Ph N.k) → MultiTapeTM 2 Bool (nf_St N SL i)
  | .ctl => scanTM 2 0 (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N)
  | .rep j => L j
  | .aFwd _ => skipTM 2 0
  | .aBack _ => skipBackTM 2 0
  | .bFwd _ => skipTM 2 1
  | .bBack _ => skipBackTM 2 1
  | .bClr _ => clearTM 2 1
  | .park => nf_park

/-- After tape `j`'s phases: the next work tape's replay, or the passing verdict. -/
private def nf_after (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) : Option (Fin N.k) → Σ i, nf_St N SL i
  | none => if h : 0 < N.k then ⟨.rep (some ⟨0, h⟩), (L (some ⟨0, h⟩)).q₀⟩ else ⟨.park, true⟩
  | some j =>
    if h : j.val + 1 < N.k then ⟨.rep (some ⟨j.val + 1, h⟩), (L (some ⟨j.val + 1, h⟩)).q₀⟩
    else ⟨.park, true⟩

/-- The redirect table: each phase's exit to the next phase's start, a failure to the rejecting
park. `exit` reads the replay leaf's verdict states (`some true` passed, `some false` failed). -/
private def nf_red (N : FinNDTM Bool) {SL : Type} (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL)
    (exit : SL → Option Bool) : (i : nf_Ph N.k) → nf_St N SL i → Option (Σ i, nf_St N SL i)
  | .ctl, .done a =>
    some (if nf_sweepPass N a then ⟨.rep none, (L none).q₀⟩ else ⟨.park, false⟩)
  | .ctl, .fwd _ => none
  | .ctl, .bwd _ => none
  | .rep j, q =>
    match exit q with
    | some true => some ⟨.aFwd j, .run⟩
    | some false => some ⟨.park, false⟩
    | none => none
  | .aFwd j, .done => some ⟨.aBack j, .run⟩
  | .aFwd _, .run => none
  | .aFwd _, .gap => none
  | .aFwd _, .back => none
  | .aBack none, .done => some (nf_after N L none)
  | .aBack (some j), .done => some ⟨.bFwd j, .run⟩
  | .aBack _, .run => none
  | .aBack _, .gap => none
  | .aBack _, .back => none
  | .bFwd j, .done => some ⟨.bBack j, .run⟩
  | .bFwd _, .run => none
  | .bFwd _, .gap => none
  | .bFwd _, .back => none
  | .bBack j, .done => some ⟨.bClr j, .sweep⟩
  | .bBack _, .run => none
  | .bBack _, .gap => none
  | .bBack _, .back => none
  | .bClr j, .done => some (nf_after N L (some j))
  | .bClr _, .sweep => none
  | .bClr _, .rewind => none
  | .park, _ => none

/-- The verifier: the phase host over the phases, entered at the control sweep. -/
private def nf_V (N : FinNDTM Bool) {SL : Type} (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL)
    (exit : SL → Option Bool) : MultiTapeTM 2 Bool (Σ i, nf_St N SL i) :=
  phaseHostTM (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ (nf_red N L exit)

/-! ### The replay leaf

One two-tape machine, parameterized by the replayed tape (`none` the input, `some j` work tape
`j`). It reads tape `0` one cell per step with the control sweep's own record parser and control
(`nf_sweepStep`), so its simulated state is the control sweep's, and at each completed record
recomputes the action of `N`'s table on the record's decoded claims (`nf_decode`). The input
instance compares the decoded input claim with the cell under the native input head and performs
the recomputed input move. A work-tape instance keeps the replayed tape on tape `1` as two-bit
blocks, two nonblank bits per visited cell (`nf_record`'s code) and two blanks per unvisited
cell: at each record it checks the decoded claim against the block under its head, rewrites the
block with the cell's new content, and moves two cells per simulated move, except after the
end-flagged record. -/

/-- The replay leaf's states. -/
private inductive nf_LeafSt (N : FinNDTM Bool) : Type
  /-- reading the stream on tape `0`, with the control sweep's parser and control -/
  | read (σ : nf_SweepState N)
  /-- at the first cell of the replayed cell's block on tape `1`, with the record's claim, the
  cell's new content, the simulated move and the end flag -/
  | blk₁ (σ : nf_SweepState N) (claim new : Option Bool) (mv : SignType) (last : Bool)
  /-- at the block's second cell, with its first cell's old content `β` -/
  | blk₂ (σ : nf_SweepState N) (claim new : Option Bool) (mv : SignType) (last : Bool)
      (β : Option Bool)
  /-- the first of the two head adjustments on tape `1` after a block -/
  | adj₁ (σ : nf_SweepState N) (mv : SignType)
  /-- the second head adjustment -/
  | adj₂ (σ : nf_SweepState N) (mv : SignType)
  /-- the passing exit -/
  | pass
  /-- the rejecting exit -/
  | rej

/-- The replay leaf's states as a sum of finite types, for its instances. -/
private def nf_leafEquiv (N : FinNDTM Bool) : nf_LeafSt N ≃
    nf_SweepState N ⊕ (nf_SweepState N × Option Bool × Option Bool × SignType × Bool) ⊕
      (nf_SweepState N × Option Bool × Option Bool × SignType × Bool × Option Bool) ⊕
      (nf_SweepState N × SignType) ⊕ (nf_SweepState N × SignType) ⊕ Bool where
  toFun
    | .read σ => .inl σ
    | .blk₁ σ c n m l => .inr (.inl (σ, c, n, m, l))
    | .blk₂ σ c n m l β => .inr (.inr (.inl (σ, c, n, m, l, β)))
    | .adj₁ σ m => .inr (.inr (.inr (.inl (σ, m))))
    | .adj₂ σ m => .inr (.inr (.inr (.inr (.inl (σ, m)))))
    | .pass => .inr (.inr (.inr (.inr (.inr true))))
    | .rej => .inr (.inr (.inr (.inr (.inr false))))
  invFun
    | .inl σ => .read σ
    | .inr (.inl (σ, c, n, m, l)) => .blk₁ σ c n m l
    | .inr (.inr (.inl (σ, c, n, m, l, β))) => .blk₂ σ c n m l β
    | .inr (.inr (.inr (.inl (σ, m)))) => .adj₁ σ m
    | .inr (.inr (.inr (.inr (.inl (σ, m))))) => .adj₂ σ m
    | .inr (.inr (.inr (.inr (.inr b)))) => if b then .pass else .rej
  left_inv s := by cases s <;> rfl
  right_inv s := by
    rcases s with σ | ⟨σ, c, n, m, l⟩ | ⟨σ, c, n, m, l, β⟩ | ⟨σ, m⟩ | ⟨σ, m⟩ | b
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · cases b <;> rfl

/-- Decidable equality of the replay leaf's states. -/
private instance nf_leafStDecEq (N : FinNDTM Bool) : DecidableEq (nf_LeafSt N) :=
  letI : DecidableEq (nf_SweepState N) := inferInstance
  letI : DecidableEq (Option Bool × Option Bool × SignType × Bool × Option Bool) :=
    inferInstance
  letI : DecidableEq (nf_SweepState N × Option Bool × Option Bool × SignType × Bool) :=
    inferInstance
  letI : DecidableEq
      (nf_SweepState N × Option Bool × Option Bool × SignType × Bool × Option Bool) :=
    inferInstance
  letI : DecidableEq (nf_SweepState N × SignType) := inferInstance
  (nf_leafEquiv N).decidableEq

/-- Finiteness of the replay leaf's states. -/
private instance nf_leafStFintype (N : FinNDTM Bool) : Fintype (nf_LeafSt N) :=
  letI : Fintype (nf_SweepState N) := inferInstance
  letI : Fintype (Option Bool × Option Bool × SignType × Bool × Option Bool) :=
    inferInstance
  letI : Fintype (nf_SweepState N × Option Bool × Option Bool × SignType × Bool) :=
    inferInstance
  letI : Fintype
      (nf_SweepState N × Option Bool × Option Bool × SignType × Bool × Option Bool) :=
    inferInstance
  letI : Fintype (nf_SweepState N × SignType) := inferInstance
  Fintype.ofEquiv _ (nf_leafEquiv N).symm

/-- The action of `N`'s table on a completed record at a live simulated state, read through the
record's decoded claims: the action `nf_complete` recomputes. -/
private def nf_act (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Option Bool) (q : N.State) :
    Action N.k Bool N.State :=
  N.tm.tr ((r 0).getD false) q (nf_decode N.k r 0) (fun j => nf_decode N.k r j.succ)

/-- A block of tape `1` decodes as `nf_decode` reads a claim: a false or blank first cell is a
blank cell. -/
private def nf_blockDecode (β₁ β₂ : Option Bool) : Option Bool :=
  if β₁.getD false then some (β₂.getD false) else none

/-- **The replay leaf** for the replayed tape `j` (`none` the input, `some j` work tape `j`).
It is a hand-built machine because no public row reads fixed-width records off one tape while
checking them against another: `Turing.scanTM` reads one tape, and the record reader of
`Turing.StepBlock` reads records on `k + 2` tapes. -/
private def nf_leaf (N : FinNDTM Bool) (j : Option (Fin N.k)) :
    MultiTapeTM 2 Bool (nf_LeafSt N) where
  q₀ := .read (nf_sweepInit N)
  tr := fun st inp w =>
    match st with
    | .read σ =>
      if σ.1.1.val = 2 * N.k + 3 then
        match σ.2.1, j with
        | none, _ => tapeAction 0 0 none 0 .rej
        | some q, none =>
          if nf_decode N.k (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) 0 = inp then
            tapeAction 0
              (nf_act N (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) q).inputTape none 1
              (if (w 0).getD false then .pass else .read (nf_sweepStep N σ ((w 0).getD false)))
          else tapeAction 0 0 none 0 .rej
        | some q, some t =>
          tapeAction 0 0 none 1 (.blk₁ (nf_sweepStep N σ ((w 0).getD false))
            (nf_decode N.k (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) t.succ)
            (((nf_act N (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) q).workTapes
              t).1.getD
              (nf_decode N.k (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) t.succ))
            ((nf_act N (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) q).workTapes t).2
            ((w 0).getD false))
      else tapeAction 0 0 none 1 (.read (nf_sweepStep N σ ((w 0).getD false)))
    | .blk₁ σ c n m l => tapeAction 1 0 (some (some n.isSome)) 1 (.blk₂ σ c n m l (w 1))
    | .blk₂ σ c n m l β =>
      if nf_blockDecode β (w 1) = c then
        tapeAction 1 0 (some (some (n.getD false))) (if l then 0 else if m = 1 then 1 else -1)
          (if l then .pass else .adj₁ σ m)
      else tapeAction 1 0 none 0 .rej
    | .adj₁ σ m => tapeAction 1 0 none (if m = -1 then -1 else 0) (.adj₂ σ m)
    | .adj₂ σ m => tapeAction 1 0 none (if m = -1 then -1 else 0) (.read σ)
    | .pass => tapeAction 0 0 none 0 .pass
    | .rej => tapeAction 0 0 none 0 .rej

/-- The replay leaf's verdict states: `pass` passed, `rej` failed, every other state live. -/
private def nf_leafExit (N : FinNDTM Bool) : nf_LeafSt N → Option Bool
  | .pass => some true
  | .rej => some false
  | _ => none

-- the verifier's state type is finite with decidable equality, by the named instances
example (N : FinNDTM Bool) : DecidableEq (Σ i, nf_St N (nf_LeafSt N) i) := inferInstance
example (N : FinNDTM Bool) : Fintype (Σ i, nf_St N (nf_LeafSt N) i) := inferInstance

/-! ### Chaining the verifier's phases -/

/-- A configuration whose state is redirected to `⟨i, q⟩` is the tagged configuration of phase
`i` at `q`. -/
private theorem nf_retag {N : FinNDTM Bool} {SL S : Type} {x : List Bool}
    (c : Cfg 2 Bool S x) (i : nf_Ph N.k) (q : nf_St N SL i) (hc : c.state.isSome) :
    c.mapState (fun _ => (⟨i, q⟩ : Σ i, nf_St N SL i)) =
      ({ state := some q, inputPos := c.inputPos, workTapes := c.workTapes,
          workTapePos := c.workTapePos, output := c.output } : Cfg 2 Bool (nf_St N SL i) x).mapState
        (Sigma.mk i) := by
  apply Cfg.ext
  · rw [Cfg.mapState_state, Cfg.mapState_state]
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hc
    rw [hs]; rfl
  · rw [Cfg.mapState_inputPos, Cfg.mapState_inputPos]
  · funext j p; rw [Cfg.mapState_workTapes, Cfg.mapState_workTapes]
  · funext j; rw [Cfg.mapState_workTapePos, Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output, Cfg.mapState_output]

/-- A configuration tagged by a phase other than the park is at no verdict. -/
private theorem nf_tagged_ne_park {N : FinNDTM Bool} {SL : Type} {x : List Bool}
    {i : nf_Ph N.k} (hi : i ≠ .park) (c : Cfg 2 Bool (nf_St N SL i) x) (b : Bool) :
    (c.mapState (Sigma.mk i)).state ≠ some ⟨.park, b⟩ := by
  rw [Cfg.mapState_state]
  cases hs : c.state with
  | none => exact Option.noConfusion
  | some q =>
    intro h
    exact hi (Sigma.mk.inj_iff.mp (Option.some.inj h)).1

/-- The redirect after the return of tape `0`: the next tape's replay or the verdict after the
input, the clear of tape `1` after a work tape. -/
private def nf_aNext (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) : Option (Fin N.k) → Σ i, nf_St N SL i
  | none => nf_after N L none
  | some j => ⟨.bFwd j, .run⟩

section Chain

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg

/-- **The return of tape `0` after a replay.** From the head of tape `0` on the blank after the
stream `s` (tape `0` holding `s` from cell `0`), the verifier's phases `aFwd j` (`Turing.skipTM`
at `w := []`) and `aBack j` (`Turing.skipBackTM` at `u := s`) bring that head to cell `0` and
redirect to `nf_aNext N L j`, in `|s| + 6` steps, with the tapes, the head of tape `1`, the input
head and the output unchanged, and at no verdict on the way.

**Proof sketch.** Chain the two framed seek runs through the phase lemma of the phase host,
reading the redirected configuration as the second phase's start. Inside each phase the host's
run is the phase's run tagged by that phase, which is not the park. -/
private theorem nf_aReturn (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) (exit : SL → Option Bool) {x : List Bool}
    (j : Option (Fin N.k)) (s : List Bool) (c : Cfg 2 Bool SeekPhase x)
    (hst : c.state = some .run) (hpos : c.workTapePos 0 = s.length)
    (htape : ∀ p, c.workTapes 0 p = FinTM.bufferTape s p) :
    ∃ c₃ : Cfg 2 Bool SeekPhase x,
      (nf_V N L exit).runFrom
          ((c : Cfg 2 Bool (nf_St N SL (nf_Ph.aFwd j)) x).mapState (Sigma.mk (nf_Ph.aFwd j)))
          (s.length + 6) = c₃.mapState (fun _ => nf_aNext N L j) ∧
        c₃.state.isSome ∧
        c₃.workTapePos 0 = 0 ∧ c₃.workTapePos 1 = c.workTapePos 1 ∧ c₃.workTapes = c.workTapes ∧
        c₃.inputPos = c.inputPos ∧ c₃.output = c.output ∧
        ∀ u < s.length + 6, ∀ b, ((nf_V N L exit).runFrom
          ((c : Cfg 2 Bool (nf_St N SL (nf_Ph.aFwd j)) x).mapState (Sigma.mk (nf_Ph.aFwd j)))
            u).state ≠ some ⟨.park, b⟩ := by
  -- phase `aFwd j`: one step right, over the blank
  have hw : ∀ p : ℤ, 0 ≤ p → p ≤ (([] : List Bool).length : ℤ) →
      c.workTapes 0 (c.workTapePos 0 + p) = FinTM.bufferTape [] p := by
    intro p h0 h1
    simp only [List.length_nil, Nat.cast_zero] at h1
    obtain rfl : p = 0 := le_antisymm h1 h0
    rw [htape, hpos, add_zero, FinTM.bufferTape_nat, FinTM.bufferTape_nil, List.getElem?_eq_none
      (le_refl _)]
  obtain ⟨h1, h2, -⟩ := skipTM_run_ofCfg (k := 2) (0 : Fin 2) [] c hst hw
  set c₁ : Cfg 2 Bool SeekPhase x := { c with
      state := some .done
      workTapePos :=
        Function.update c.workTapePos 0 (c.workTapePos 0 + ([] : List Bool).length + 1) }
    with hc₁
  obtain ⟨hpA, hA⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.aFwd j) (c := c) (c' := c₁) (([] : List Bool).length + 1) h1
    SeekPhase.done rfl ⟨.aBack j, .run⟩ rfl (by
      intro u hu q hq
      obtain rfl : u = 0 := by simp at hu; omega
      rw [MultiTapeTM.runFrom_zero, hst] at hq
      cases hq
      rfl)
  -- the redirected configuration is phase `aBack j`'s start
  have hre := nf_retag (N := N) (SL := SL) (S := nf_St N SL (nf_Ph.aFwd j)) c₁ (nf_Ph.aBack j)
    SeekPhase.run (by simp [hc₁])
  set c₂ : Cfg 2 Bool SeekPhase x := { c₁ with state := some .run } with hc₂
  -- phase `aBack j`: back over the stream to cell `0`
  have hu : ∀ p : ℤ, -1 ≤ p → p ≤ (s.length : ℤ) →
      c₂.workTapes 0 (c₂.workTapePos 0 - s.length - 1 + p) = FinTM.bufferTape s p := by
    intro p _ _
    simp only [hc₂, hc₁, Function.update_self, List.length_nil, Nat.cast_zero, hpos]
    rw [htape]
    congr 1
    ring
  obtain ⟨h3, h4, -⟩ := skipBackTM_run_ofCfg (k := 2) (0 : Fin 2) s c₂ rfl hu
  set c₃ : Cfg 2 Bool SeekPhase x := { c₂ with
      state := some .done
      workTapePos := Function.update c₂.workTapePos 0 (c₂.workTapePos 0 - s.length - 1) }
    with hc₃
  have hred : nf_red N L exit (nf_Ph.aBack j) SeekPhase.done = some (nf_aNext N L j) := by
    cases j <;> rfl
  obtain ⟨hpB, hB⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.aBack j) (c := c₂) (c' := c₃) (s.length + 3) h3
    SeekPhase.done rfl (nf_aNext N L j) hred (by
      intro u hu q hq
      cases q with
      | done => exact absurd hq (h4 u hu)
      | run => cases j <;> rfl
      | gap => cases j <;> rfl
      | back => cases j <;> rfl)
  have e : s.length + 6 = (([] : List Bool).length + 1 + 1) + (s.length + 3 + 1) := by simp; omega
  refine ⟨c₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, MultiTapeTM.runFrom_add]
    unfold nf_V
    rw [hA, hre]
    exact hB
  · simp [hc₃]
  · simp only [hc₃, hc₂, hc₁, Function.update_self, List.length_nil, Nat.cast_zero, hpos]
    ring
  · simp only [hc₃, hc₂, hc₁]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · simp only [hc₃, hc₂, hc₁]
  · simp only [hc₃, hc₂, hc₁]
  · simp only [hc₃, hc₂, hc₁]
  · intro u hu b
    unfold nf_V
    by_cases hu1 : u ≤ ([] : List Bool).length + 1
    · rw [hpA u hu1]
      exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
    · obtain ⟨v, rfl⟩ : ∃ v, u = (([] : List Bool).length + 1 + 1) + v :=
        ⟨u - (([] : List Bool).length + 1 + 1), by omega⟩
      rw [MultiTapeTM.runFrom_add, hA, hre, hpB v (by simp at hu ⊢; omega)]
      exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b

/-- **The clear of tape `1` after a work tape's replay.** From the head of tape `1` at any offset
`i ≤ |R|` into a region `R` delimited by blanks (so `i = |R|`, the right delimiter, is allowed),
the phases `bFwd j` (`Turing.skipTM` over `R.drop i`), `bBack j` (`Turing.skipBackTM` at
`u := R`) and `bClr j` (`Turing.clearTM` over `R`) reach `nf_after N L (some j)` with tape `1`
blank on the region and its head on the region's first cell, everything else unchanged, and at no
verdict on the way.

**Proof sketch.** Chain the three framed runs through the phase lemma of the phase host,
reading each redirected configuration as the next phase's start. The region's suffix from the
head, the whole region from one past its right delimiter, and the region from its first cell are
read off the buffer of `R`. Inside each phase the host's run is tagged by that phase, which is
not the park. -/
private theorem nf_bClear (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) (exit : SL → Option Bool) {x : List Bool}
    (j : Fin N.k) (R : List Bool) (i : ℕ) (hi : i ≤ R.length)
    (c : Cfg 2 Bool SeekPhase x) (hst : c.state = some .run)
    (htape : ∀ p : ℤ, -1 ≤ p → p ≤ (R.length : ℤ) →
      c.workTapes 1 (c.workTapePos 1 - i + p) = FinTM.bufferTape R p) :
    ∃ c₅ : Cfg 2 Bool SweepPhase x,
      (nf_V N L exit).runFrom
          ((c : Cfg 2 Bool (nf_St N SL (nf_Ph.bFwd j)) x).mapState (Sigma.mk (nf_Ph.bFwd j)))
          ((R.length - i + 1 + 1) + (R.length + 3 + 1) + (2 * R.length + 2 + 1)) =
        c₅.mapState (fun _ => nf_after N L (some j)) ∧
      c₅.state.isSome ∧
      c₅.workTapePos 1 = c.workTapePos 1 - i ∧ c₅.workTapePos 0 = c.workTapePos 0 ∧
      c₅.workTapes 0 = c.workTapes 0 ∧ c₅.inputPos = c.inputPos ∧ c₅.output = c.output ∧
      (∀ q, c₅.workTapes 1 q = if c.workTapePos 1 - i ≤ q ∧ q < c.workTapePos 1 - i + R.length
        then none else c.workTapes 1 q) ∧
      ∀ u < (R.length - i + 1 + 1) + (R.length + 3 + 1) + (2 * R.length + 2 + 1), ∀ b,
        ((nf_V N L exit).runFrom
          ((c : Cfg 2 Bool (nf_St N SL (nf_Ph.bFwd j)) x).mapState (Sigma.mk (nf_Ph.bFwd j)))
            u).state ≠ some ⟨.park, b⟩ := by
  have hdl : ((R.drop i).length : ℤ) = (R.length : ℤ) - i := by
    rw [List.length_drop]; push_cast [Nat.cast_sub hi]; ring
  -- phase `bFwd j`: over the region's suffix from the head
  have hw : ∀ p : ℤ, 0 ≤ p → p ≤ ((R.drop i).length : ℤ) →
      c.workTapes 1 (c.workTapePos 1 + p) = FinTM.bufferTape (R.drop i) p := by
    intro p h0 h1
    have h := htape (p + i) (by omega) (by omega)
    rw [show c.workTapePos 1 - i + (p + i) = c.workTapePos 1 + p by ring] at h
    rw [h]
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [show ((n : ℤ) + (i : ℤ)) = ((n + i : ℕ) : ℤ) by push_cast; ring, FinTM.bufferTape_nat,
      FinTM.bufferTape_nat, List.getElem?_drop]
    congr 1
    omega
  obtain ⟨h1, h2, -⟩ := skipTM_run_ofCfg (k := 2) (1 : Fin 2) (R.drop i) c hst hw
  set c₁ : Cfg 2 Bool SeekPhase x := { c with
      state := some .done
      workTapePos := Function.update c.workTapePos 1 (c.workTapePos 1 + (R.drop i).length + 1) }
    with hc₁
  obtain ⟨hpA, hA⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.bFwd j) (c := c) (c' := c₁) ((R.drop i).length + 1) h1
    SeekPhase.done rfl ⟨.bBack j, .run⟩ rfl (by
      intro u hu q hq
      cases q with
      | done => exact absurd hq (h2 u hu)
      | run => rfl
      | gap => rfl
      | back => rfl)
  have hre := nf_retag (N := N) (SL := SL) (S := nf_St N SL (nf_Ph.bFwd j)) c₁ (nf_Ph.bBack j)
    SeekPhase.run (by simp [hc₁])
  set c₂ : Cfg 2 Bool SeekPhase x := { c₁ with state := some .run } with hc₂
  -- phase `bBack j`: back over the whole region to its first cell
  have hu : ∀ p : ℤ, -1 ≤ p → p ≤ (R.length : ℤ) →
      c₂.workTapes 1 (c₂.workTapePos 1 - R.length - 1 + p) = FinTM.bufferTape R p := by
    intro p h0 h1
    simp only [hc₂, hc₁, Function.update_self]
    rw [← htape p h0 h1]
    congr 1
    rw [hdl]
    ring
  obtain ⟨h3, h4, -⟩ := skipBackTM_run_ofCfg (k := 2) (1 : Fin 2) R c₂ rfl hu
  set c₃ : Cfg 2 Bool SeekPhase x := { c₂ with
      state := some .done
      workTapePos := Function.update c₂.workTapePos 1 (c₂.workTapePos 1 - R.length - 1) }
    with hc₃
  obtain ⟨hpB, hB⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.bBack j) (c := c₂) (c' := c₃) (R.length + 3) h3
    SeekPhase.done rfl ⟨.bClr j, .sweep⟩ rfl (by
      intro u hu q hq
      cases q with
      | done => exact absurd hq (h4 u hu)
      | run => rfl
      | gap => rfl
      | back => rfl)
  have hpos3 : c₃.workTapePos 1 = c.workTapePos 1 - i := by
    simp only [hc₃, hc₂, hc₁, Function.update_self]
    rw [hdl]
    ring
  -- the redirected configuration is phase `bClr j`'s start
  have hre2 := nf_retag (N := N) (SL := SL) (S := nf_St N SL (nf_Ph.bBack j)) c₃ (nf_Ph.bClr j)
    SweepPhase.sweep (by simp [hc₃])
  set c₄ : Cfg 2 Bool SweepPhase x :=
    { state := some SweepPhase.sweep, inputPos := c₃.inputPos, workTapes := c₃.workTapes,
      workTapePos := c₃.workTapePos, output := c₃.output } with hc₄
  -- phase `bClr j`: blank the region
  have hcw : ∀ p : ℤ, -1 ≤ p → p ≤ (R.length : ℤ) →
      c₄.workTapes 1 (c₄.workTapePos 1 + p) = FinTM.bufferTape R p := by
    intro p h0 h1
    have e : c₄.workTapePos 1 = c.workTapePos 1 - i := by simp only [hc₄]; exact hpos3
    rw [e]
    simp only [hc₄, hc₃, hc₂, hc₁]
    exact htape p h0 h1
  obtain ⟨h5, h6, -⟩ := clearTM_run_ofCfg (k := 2) (1 : Fin 2) R c₄ rfl hcw
  set c₅ : Cfg 2 Bool SweepPhase x := { c₄ with
      state := some SweepPhase.done
      workTapes := fun j q =>
        if j = 1 ∧ c₄.workTapePos j ≤ q ∧ q < c₄.workTapePos j + (R.length : ℤ)
          then none
        else c₄.workTapes j q } with hc₅
  obtain ⟨hpC, hC⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.bClr j) (c := c₄) (c' := c₅) (2 * R.length + 2) h5
    SweepPhase.done rfl (nf_after N L (some j)) rfl (by
      intro u hu q hq
      cases q with
      | done => exact absurd hq (h6 u hu)
      | sweep => rfl
      | rewind => rfl)
  have e : (R.length - i + 1 + 1) + (R.length + 3 + 1) + (2 * R.length + 2 + 1) =
      ((R.drop i).length + 1 + 1) + ((R.length + 3 + 1) + (2 * R.length + 2 + 1)) := by
    rw [List.length_drop]; omega
  refine ⟨c₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, MultiTapeTM.runFrom_add]
    unfold nf_V
    rw [hA, hre, MultiTapeTM.runFrom_add, hB, hre2]
    exact hC
  · simp [hc₅]
  · simp only [hc₅, hc₄]
    exact hpos3
  · simp only [hc₅, hc₄, hc₃, hc₂, hc₁]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · simp only [hc₅, hc₄, hc₃, hc₂, hc₁]
    funext q
    rw [if_neg (fun h => absurd h.1 (by decide))]
  · simp only [hc₅, hc₄, hc₃, hc₂, hc₁]
  · simp only [hc₅, hc₄, hc₃, hc₂, hc₁]
  · intro q
    have e4 : c₄.workTapePos 1 = c.workTapePos 1 - i := by simp only [hc₄]; exact hpos3
    have ew : c₄.workTapes 1 q = c.workTapes 1 q := by simp only [hc₄, hc₃, hc₂, hc₁]
    have hq : c₅.workTapes 1 q = if (1 : Fin 2) = 1 ∧ c₄.workTapePos 1 ≤ q ∧
        q < c₄.workTapePos 1 + (R.length : ℤ) then none else c₄.workTapes 1 q := rfl
    rw [hq, e4, ew]
    by_cases h : c.workTapePos 1 - i ≤ q ∧ q < c.workTapePos 1 - i + R.length
    · rw [if_pos ⟨rfl, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  · intro u hu b
    unfold nf_V
    by_cases hu1 : u ≤ (R.drop i).length + 1
    · rw [hpA u hu1]
      exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
    · obtain ⟨v, rfl⟩ : ∃ v, u = ((R.drop i).length + 1 + 1) + v :=
        ⟨u - ((R.drop i).length + 1 + 1), by omega⟩
      rw [MultiTapeTM.runFrom_add, hA, hre]
      by_cases hv1 : v ≤ R.length + 3
      · rw [hpB v hv1]
        exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
      · obtain ⟨w, rfl⟩ : ∃ w, v = (R.length + 3 + 1) + w := ⟨v - (R.length + 3 + 1), by omega⟩
        rw [MultiTapeTM.runFrom_add, hB, hre2, hpC w (by rw [List.length_drop] at hu; omega)]
        exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b

end Chain

/-- **The verifier's entry is the stream start.** After the trivial setup, the run's entry
configuration is `streamStartCfg x 0 q s`: state `q`, the input head at `1`, `s` on tape `0`
from cell `0` (blank elsewhere), tape `1` blank, both heads at `0`, empty output.

**Proof sketch.** Compare the two configurations field by field through their field equations.
On tape `0` the guessed block over the blank initial tape is the buffer of `s`: inside the block
by definition, and outside it both are blank (left of cell `0`, and past the end of `s`). -/
private theorem nf_entry {SP S : Type} (P : MultiTapeTM 2 Bool SP) (x s : List Bool) (q : S) :
    guessRunCfg (P.initCfg x) 0 s q = streamStartCfg x 0 q s := by
  rw [MultiTapeTM.initCfg_eq]
  apply Cfg.ext
  · rw [guessRunCfg_state, streamStartCfg_state]
  · rw [guessRunCfg_inputPos, streamStartCfg_inputPos, Cfg.init_inputPos]
  · funext i p
    rw [guessRunCfg_workTapes, streamStartCfg_workTapes, Cfg.init_workTapePos]
    by_cases hi : i = 0
    · subst hi
      rw [Function.update_self, if_pos rfl]
      by_cases hp : (0 : ℤ) ≤ p ∧ p < 0 + (s.length : ℤ)
      · rw [if_pos hp, sub_zero]
      · rw [if_neg hp, Cfg.init_workTapes]
        by_cases hneg : p < 0
        · rw [FinTM.bufferTape_of_neg s hneg]
        · rw [FinTM.bufferTape_eq, if_pos (by omega)]
          exact (List.getElem?_eq_none (by omega)).symm
    · rw [Function.update_of_ne hi, if_neg hi, Cfg.init_workTapes]
  · funext i
    rw [guessRunCfg_workTapePos, streamStartCfg_workTapePos, Cfg.init_workTapePos]
  · rw [guessRunCfg_output, streamStartCfg_output, Cfg.init_output]

/-- A stream-start configuration with a tagged state is the tagged stream start. -/
private theorem nf_tag {N : FinNDTM Bool} {SL : Type} (x s : List Bool) (i : nf_Ph N.k)
    (q : nf_St N SL i) :
    streamStartCfg x (0 : Fin 2) (⟨i, q⟩ : Σ i, nf_St N SL i) s =
      (streamStartCfg x (0 : Fin 2) q s).mapState (Sigma.mk i) := by
  apply Cfg.ext
  · rw [Cfg.mapState_state, streamStartCfg_state, streamStartCfg_state]; rfl
  · rw [Cfg.mapState_inputPos, streamStartCfg_inputPos, streamStartCfg_inputPos]
  · funext i p; rw [Cfg.mapState_workTapes, streamStartCfg_workTapes, streamStartCfg_workTapes]
  · funext i; rw [Cfg.mapState_workTapePos, streamStartCfg_workTapePos, streamStartCfg_workTapePos]
  · rw [Cfg.mapState_output, streamStartCfg_output, streamStartCfg_output]

/-- **The input read depends on the input head only**, across machines with any work tapes and
states: a claim checked against the verifier's input head transfers to `N`'s configuration. -/
private theorem nf_inputSymbol_congr {k k' : ℕ} {S S' : Type} {x : List Bool}
    (c : Cfg k Bool S x) (c' : Cfg k' Bool S' x) (h : c.inputPos.val = c'.inputPos.val) :
    c.inputSymbol = c'.inputSymbol := by
  by_cases h0 : c.inputPos.val = 0
  · have h0' : c'.inputPos = 0 := Fin.ext (by rw [← h]; exact h0)
    rw [Cfg.inputSymbol_of_zero (Fin.ext h0), Cfg.inputSymbol_of_zero h0']
  · by_cases he : c.inputPos.val = x.length + 1
    · rw [Cfg.inputSymbol_of_end he, Cfg.inputSymbol_of_end (by omega)]
    · have hlt := c.inputPos.isLt
      rw [inputSymbolInner (c.inputPos.val - 1) (by omega) (by omega),
        inputSymbolInner (cfg := c') (c.inputPos.val - 1) (by omega) (by omega)]

section Leaf

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg

/-- After a record's first `2k + 3` bits the parser is at the last position with the control
unchanged; the record's last bit completes the full record array, and the parser's step there
resets the parser and applies the completion rule to that record.

**Proof sketch.** The prefix law of the parser gives the position and the stored prefix. Storing
the last bit fills the only missing entry, and the whole-record law, split at its last bit, is
the parser's last step. -/
private theorem nf_prefix_last (N : FinNDTM Bool) (rec : Fin (2 * N.k + 4) → Bool)
    (ctl : nf_Control N) (σ : nf_SweepState N)
    (hσ : σ = (List.ofFn fun i : Fin (2 * N.k + 3) => rec ⟨i.val, by omega⟩).foldl
      (nf_sweepStep N) ((0, fun _ => none), ctl)) :
    σ.1.1.val = 2 * N.k + 3 ∧ σ.2 = ctl ∧
      Function.update σ.1.2 σ.1.1 (some (rec ⟨2 * N.k + 3, by omega⟩)) =
        (fun p => some (rec p)) ∧
      nf_sweepStep N σ (rec ⟨2 * N.k + 3, by omega⟩) =
        ((0, fun _ => none), nf_complete N (fun p => some (rec p)) ctl) := by
  have hp := nf_sweep_prefix N rec ctl (2 * N.k + 3) (by omega)
  rw [← hσ] at hp
  refine ⟨by rw [hp], by rw [hp], ?_, ?_⟩
  · rw [hp]
    funext p
    by_cases he : p = ⟨2 * N.k + 3, by omega⟩
    · subst he
      rw [Function.update_self]
    · have hne : p.val ≠ 2 * N.k + 3 := fun h => he (Fin.ext h)
      have hlt := p.isLt
      rw [Function.update_of_ne he]
      show (if p.val < 2 * N.k + 3 then some (rec p) else none) = some (rec p)
      rw [if_pos (by omega)]
  · have h := nf_sweep_record N rec ctl
    rw [List.ofFn_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    rw [hσ]
    exact h

/-- **The replay leaf reads a record's bits.** From a record boundary, with the record's bits on
tape `0` from its head, the leaf takes one step per bit, moving that head right and storing the
bit in the control sweep's parser, and changes nothing else, for every instance.

**Proof sketch.** Induct on the number of bits read. Before the record's last bit the parser's
position is not the last one, so the leaf's table is a one-tape right move on tape `0` that
stores the scanned bit; the stored prefix grows by that bit, and the head of tape `0` by one
cell. -/
private theorem nf_leaf_prefix (N : FinNDTM Bool) (j : Option (Fin N.k)) {x : List Bool}
    (d : Cfg 2 Bool (nf_LeafSt N) x) (rec : Fin (2 * N.k + 4) → Bool) (ctl : nf_Control N)
    (hst : d.state = some (.read ((0, fun _ => none), ctl)))
    (hA : ∀ p : Fin (2 * N.k + 4), d.workTapes 0 (d.workTapePos 0 + (p.val : ℤ)) = some (rec p)) :
    ∀ (m : ℕ) (hm : m < 2 * N.k + 4), (nf_leaf N j).runFrom d m = { d with
      state := some (.read ((List.ofFn fun i : Fin m => rec ⟨i.val, by omega⟩).foldl
        (nf_sweepStep N) ((0, fun _ => none), ctl)))
      workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + m) }
  | 0, _ => by
    rw [MultiTapeTM.runFrom_zero]
    apply Cfg.ext
    · rw [hst]
      rfl
    · rfl
    · rfl
    · funext i
      show d.workTapePos i = Function.update d.workTapePos 0 (d.workTapePos 0 + ((0 : ℕ) : ℤ)) i
      rw [Nat.cast_zero, add_zero, Function.update_eq_self]
    · rfl
  | m + 1, hm => by
    rw [MultiTapeTM.runFrom_succ_eq_step', nf_leaf_prefix N j d rec ctl hst hA m (by omega)]
    have hp := nf_sweep_prefix N rec ctl m (by omega)
    have hm1 : ((List.ofFn fun i : Fin m => rec ⟨i.val, by omega⟩).foldl
        (nf_sweepStep N) ((0, fun _ => none), ctl)).1.1.val = m := by rw [hp]
    have hsym : ({ d with
        state := some (.read ((List.ofFn fun i : Fin m => rec ⟨i.val, by omega⟩).foldl
          (nf_sweepStep N) ((0, fun _ => none), ctl)))
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + m) } :
          Cfg 2 Bool (nf_LeafSt N) x).workTapeSymbols 0 = some (rec ⟨m, by omega⟩) := by
      rw [Cfg.workTapeSymbols_eq]
      show d.workTapes 0 (Function.update d.workTapePos 0 (d.workTapePos 0 + m) 0) = _
      rw [Function.update_self]
      exact hA ⟨m, by omega⟩
    rw [step_of_tapeAction_move (nf_leaf N j) _ (q := .read _) 0 0 1 rfl (by
      simp only [nf_leaf]
      rw [if_neg (by rw [hm1]; omega), hsym, Option.getD_some])]
    apply Cfg.ext
    · show some (nf_LeafSt.read (nf_sweepStep N _ _)) = some (nf_LeafSt.read
        ((List.ofFn fun i : Fin (m + 1) => rec ⟨i.val, by omega⟩).foldl
          (nf_sweepStep N) ((0, fun _ => none), ctl)))
      rw [List.ofFn_succ_last, List.foldl_append]
      simp only [Fin.coe_castSucc, Fin.val_last, List.foldl_cons, List.foldl_nil, hp]
    · exact moveInputPos_zero _
    · rfl
    · funext i
      dsimp only
      by_cases hi : i = 0
      · subst hi
        rw [Function.update_self, Function.update_self, Function.update_self, SignType.coe_one]
        push_cast
        ring
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, Function.update_of_ne hi]
    · rfl

end Leaf

section LeafRecord

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg

/-- **One record of the input's replay.** From a record boundary, with the record on tape `0`
from its head, the input instance reads the record in `2k + 4` steps, at no exit before. At a
live control whose decoded input claim is the cell under the native input head, it performs the
recomputed input move, its head on tape `0` is one cell past the record, and it is at the next
record boundary, or passes if the record is end-flagged; otherwise it rejects.

**Proof sketch.** The first `2k + 3` steps read the record's first bits. At the last bit the
parser completes the record, and the leaf's table, read at the control's state and at the native
input cell (which depends on the input head only), is a one-tape action: a move of the input head
and of the head of tape `0`, or a stationary rejection. -/
private theorem nf_leaf_record_in (N : FinNDTM Bool) {x : List Bool}
    (d : Cfg 2 Bool (nf_LeafSt N) x) (rec : Fin (2 * N.k + 4) → Bool) (ctl : nf_Control N)
    (hst : d.state = some (.read ((0, fun _ => none), ctl)))
    (hA : ∀ p : Fin (2 * N.k + 4), d.workTapes 0 (d.workTapePos 0 + (p.val : ℤ)) = some (rec p)) :
    (∀ u < 2 * N.k + 4, ∀ s, ((nf_leaf N none).runFrom d u).state = some s →
      nf_leafExit N s = none) ∧
    (∀ q, ctl.1 = some q → nf_decode N.k (fun p => some (rec p)) 0 = d.inputSymbol →
      (nf_leaf N none).runFrom d (2 * N.k + 4) = { d with
        state := some (if rec ⟨2 * N.k + 3, by omega⟩ then .pass
          else .read ((0, fun _ => none), nf_complete N (fun p => some (rec p)) ctl))
        inputPos := moveInputPos d.inputPos (nf_act N (fun p => some (rec p)) q).inputTape
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 4 : ℕ)) }) ∧
    ((ctl.1 = none ∨ nf_decode N.k (fun p => some (rec p)) 0 ≠ d.inputSymbol) →
      ((nf_leaf N none).runFrom d (2 * N.k + 4)).state = some .rej) := by
  have hpre := nf_leaf_prefix N none d rec ctl hst hA
  refine ⟨fun u hu s hs => ?_, ?_⟩
  · rw [hpre u hu] at hs
    cases hs
    rfl
  set σ := (List.ofFn fun i : Fin (2 * N.k + 3) => rec ⟨i.val, by omega⟩).foldl
    (nf_sweepStep N) ((0, fun _ => none), ctl) with hσ
  obtain ⟨h1, h2, h3, h4⟩ := nf_prefix_last N rec ctl σ hσ
  set c : Cfg 2 Bool (nf_LeafSt N) x := { d with
      state := some (.read σ)
      workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 3 : ℕ)) }
    with hc
  have hrun : (nf_leaf N none).runFrom d (2 * N.k + 4) = (nf_leaf N none).step c := by
    rw [show 2 * N.k + 4 = (2 * N.k + 3) + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step',
      hpre (2 * N.k + 3) (by omega)]
  have hsym : c.workTapeSymbols 0 = some (rec ⟨2 * N.k + 3, by omega⟩) := by
    rw [Cfg.workTapeSymbols_eq]
    show d.workTapes 0 (Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 3 : ℕ)) 0) = _
    rw [Function.update_self]
    exact hA ⟨2 * N.k + 3, by omega⟩
  have hinp : c.inputSymbol = d.inputSymbol := nf_inputSymbol_congr c d rfl
  refine ⟨fun q hq hdec => ?_, fun hbad => ?_⟩
  · rw [hrun, step_of_tapeAction_move (nf_leaf N none) c (q := .read σ) 0 _ 1 rfl (by
      simp only [nf_leaf]
      rw [if_pos h1, h2, hq]
      dsimp only
      rw [hsym, Option.getD_some, h3, hinp, if_pos hdec])]
    apply Cfg.ext
    · show some (if rec ⟨2 * N.k + 3, by omega⟩ then nf_LeafSt.pass
        else nf_LeafSt.read (nf_sweepStep N σ (rec ⟨2 * N.k + 3, by omega⟩))) = _
      rw [h4]
    · rfl
    · rfl
    · funext i
      by_cases hi : i = 0
      · subst hi
        simp only [hc, Function.update_self, SignType.coe_one]
        push_cast
        ring
      · simp only [hc, Function.update_of_ne hi]
    · rfl
  · rw [hrun]
    rcases hbad with hn | hdec
    · rw [step_of_tapeAction_move (nf_leaf N none) c (q := .read σ) (q' := .rej) 0 0 0 rfl (by
        simp only [nf_leaf]
        rw [if_pos h1, h2, hn])]
    · cases hq : ctl.1 with
      | none =>
        rw [step_of_tapeAction_move (nf_leaf N none) c (q := .read σ) (q' := .rej) 0 0 0 rfl (by
          simp only [nf_leaf]
          rw [if_pos h1, h2, hq])]
      | some q =>
        rw [step_of_tapeAction_move (nf_leaf N none) c (q := .read σ) (q' := .rej) 0 0 0 rfl (by
          simp only [nf_leaf]
          rw [if_pos h1, h2, hq]
          dsimp only
          rw [hsym, Option.getD_some, h3, hinp, if_neg hdec])]

end LeafRecord

/-- **The decoded virtual step of `N`.** At a live state, apply the action recomputed from a
record's decoded claims (`nf_act`); a halted configuration stays. When every claim is the
configuration's read, it is `N`'s step under the record's choice bit (`nf_vstep_genuine`). -/
private def nf_vstep (N : FinNDTM Bool) {x : List Bool} (c : Cfg N.k Bool N.State x)
    (rec : Fin (2 * N.k + 4) → Bool) : Cfg N.k Bool N.State x :=
  match c.state with
  | none => c
  | some q => (nf_act N (fun p => some (rec p)) q).apply c

/-- A record's claim on replayed tape `i` (`0` the input, `j.succ` work tape `j`) is checked: the
virtual configuration is live and the decoded claim is its read on that tape. -/
private def nf_ok (N : FinNDTM Bool) {x : List Bool} (c : Cfg N.k Bool N.State x)
    (rec : Fin (2 * N.k + 4) → Bool) (i : Fin (N.k + 1)) : Prop :=
  c.state ≠ none ∧
    nf_decode N.k (fun p => some (rec p)) i =
      (Fin.cases c.inputSymbol c.workTapeSymbols : Fin (N.k + 1) → Option Bool) i

/-- The control fold's state and output summary follow the decoded virtual run.

**Proof sketch.** Case on the virtual state. Halted, both stay. Live, the completion rule and
the virtual step apply the same recomputed action, and appending the action's emission updates
the output summary as the completion rule does. -/
private theorem nf_vstep_ctl (N : FinNDTM Bool) {x : List Bool} (c : Cfg N.k Bool N.State x)
    (ctl : nf_Control N) (rec : Fin (2 * N.k + 4) → Bool) (h1 : ctl.1 = c.state)
    (h2 : ctl.2.1 = StepBlock.outputSummary c.output) :
    (nf_complete N (fun p => some (rec p)) ctl).1 = (nf_vstep N c rec).state ∧
      (nf_complete N (fun p => some (rec p)) ctl).2.1 =
        StepBlock.outputSummary (nf_vstep N c rec).output := by
  obtain ⟨cs, o, f⟩ := ctl
  simp only at h1 h2
  subst h1 h2
  cases hc : c.state with
  | none =>
    simp only [nf_complete, nf_vstep, hc, and_self]
  | some q =>
    simp only [nf_complete, nf_vstep, hc]
    refine ⟨(Action.apply_state _ _).symm, ?_⟩
    rw [Action.apply_output, StepBlock.outputSummary_append]
    rfl

/-- The control fold's state follows the decoded virtual run, over a list of records. -/
private theorem nf_vrun_ctl (N : FinNDTM Bool) {x : List Bool} :
    ∀ (rs : List (Fin (2 * N.k + 4) → Bool)) (c : Cfg N.k Bool N.State x) (ctl : nf_Control N),
      ctl.1 = c.state → ctl.2.1 = StepBlock.outputSummary c.output →
      (rs.foldl (fun d r => nf_complete N (fun p => some (r p)) d) ctl).1 =
          (rs.foldl (nf_vstep N) c).state ∧
        (rs.foldl (fun d r => nf_complete N (fun p => some (r p)) d) ctl).2.1 =
          StepBlock.outputSummary (rs.foldl (nf_vstep N) c).output
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | rec :: rs, c, ctl, h1, h2 => by
    obtain ⟨e1, e2⟩ := nf_vstep_ctl N c ctl rec h1 h2
    exact nf_vrun_ctl N rs _ _ e1 e2

/-- A stream of records, one record and the rest: its cells from a head are the record's bits
and then the rest's cells one record further.

**Proof sketch.** The stream is the record's bits followed by the rest's stream; read a cell
before the record's end in the first part and a later cell in the second, shifted by the record
width. -/
private theorem nf_stream_cons (k : ℕ) (rec : Fin (2 * k + 4) → Bool)
    (rs : List (Fin (2 * k + 4) → Bool)) (T : ℤ → Option Bool) (h : ℤ)
    (hT : ∀ p : ℕ, p < ((rec :: rs).flatMap List.ofFn).length →
      T (h + p) = ((rec :: rs).flatMap List.ofFn)[p]?) :
    (∀ p : Fin (2 * k + 4), T (h + (p.val : ℤ)) = some (rec p)) ∧
      ∀ p : ℕ, p < (rs.flatMap List.ofFn).length →
        T (h + ((2 * k + 4 : ℕ) : ℤ) + p) = (rs.flatMap List.ofFn)[p]? := by
  rw [List.flatMap_cons] at hT
  refine ⟨fun p => ?_, fun p hp => ?_⟩
  · have hlt : p.val < (List.ofFn rec ++ rs.flatMap List.ofFn).length := by
      rw [List.length_append, List.length_ofFn]; omega
    rw [hT p.val hlt, List.getElem?_append_left (by rw [List.length_ofFn]; exact p.isLt),
      List.getElem?_ofFn]
    simp
  · have hlt : (2 * k + 4) + p < (List.ofFn rec ++ rs.flatMap List.ofFn).length := by
      rw [List.length_append, List.length_ofFn]; omega
    have e := hT ((2 * k + 4) + p) hlt
    rw [List.getElem?_append_right (by rw [List.length_ofFn]; omega), List.length_ofFn,
      Nat.add_sub_cancel_left] at e
    rw [← e]
    congr 1
    push_cast
    ring

section LeafRun

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg

/-- **The input's replay.** From a record boundary with a stream of `n ≥ 1` records on tape `0`
from its head, only the last end-flagged, at a control that follows the virtual configuration
`c` whose input head is the native one, the input instance reaches an exit at some time `T`, at
no exit before. It passes exactly when every record's input claim is checked along the decoded
virtual run; then `T = (2k + 4)n`, its head on tape `0` is one cell past the stream, and only
that head, the input head and the state have changed. Otherwise it rejects.

**Proof sketch.** Induct over the records, one record at a time: a failed check rejects at the
record's end; a passed check of the end-flagged record passes; a passed check of an unflagged
record moves the input head as the virtual step does, keeps the control equal to the virtual
run's state, and leaves the rest of the stream one record further on, where the induction
hypothesis applies. -/
private theorem nf_leaf_run_in (N : FinNDTM Bool) {x : List Bool} :
    ∀ (rs : List (Fin (2 * N.k + 4) → Bool)) (d : Cfg 2 Bool (nf_LeafSt N) x)
      (ctl : nf_Control N) (c : Cfg N.k Bool N.State x),
    rs ≠ [] →
    (∀ r (h : r < rs.length), rs[r] ⟨2 * N.k + 3, by omega⟩ = decide (r + 1 = rs.length)) →
    d.state = some (.read ((0, fun _ => none), ctl)) → ctl.1 = c.state →
    d.inputPos = c.inputPos →
    (∀ p : ℕ, p < (rs.flatMap List.ofFn).length →
      d.workTapes 0 (d.workTapePos 0 + p) = (rs.flatMap List.ofFn)[p]?) →
    ∃ T, (∀ u < T, ∀ s, ((nf_leaf N none).runFrom d u).state = some s →
        nf_leafExit N s = none) ∧
      ((∀ r (h : r < rs.length), nf_ok N ((rs.take r).foldl (nf_vstep N) c) rs[r] 0) →
        T = (2 * N.k + 4) * rs.length ∧ ∃ ip, (nf_leaf N none).runFrom d T = { d with
          state := some .pass
          inputPos := ip
          workTapePos := Function.update d.workTapePos 0
            (d.workTapePos 0 + ((2 * N.k + 4) * rs.length : ℕ)) }) ∧
      (¬ (∀ r (h : r < rs.length), nf_ok N ((rs.take r).foldl (nf_vstep N) c) rs[r] 0) →
        ((nf_leaf N none).runFrom d T).state = some .rej)
  | [], _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | rec :: rs, d, ctl, c, _, hflag, hst, hc, hip, hA => by
    obtain ⟨hA0, hA1⟩ := nf_stream_cons N.k rec rs (d.workTapes 0) (d.workTapePos 0) hA
    obtain ⟨hpre, hpass, hrej⟩ := nf_leaf_record_in N d rec ctl hst hA0
    have hinp : d.inputSymbol = c.inputSymbol := nf_inputSymbol_congr d c (by rw [hip])
    have hall : (∀ r (h : r < (rec :: rs).length),
        nf_ok N (((rec :: rs).take r).foldl (nf_vstep N) c) (rec :: rs)[r] 0) ↔
        nf_ok N c rec 0 ∧ ∀ r (h : r < rs.length),
          nf_ok N ((rs.take r).foldl (nf_vstep N) (nf_vstep N c rec)) rs[r] 0 := by
      constructor
      · intro h
        exact ⟨h 0 (by simp), fun r hr => h (r + 1) (by simp; omega)⟩
      · rintro ⟨h0, h⟩ r hr
        cases r with
        | zero => exact h0
        | succ r => exact h r (by simp at hr; omega)
    by_cases hok : nf_ok N c rec 0
    · obtain ⟨hlive, hdec⟩ := hok
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlive
      have hdec' : nf_decode N.k (fun p => some (rec p)) 0 = d.inputSymbol := by
        rw [hinp, hdec]; rfl
      have hrun := hpass q (hc.trans hq) hdec'
      cases rs with
      | nil =>
        have hl : rec ⟨2 * N.k + 3, by omega⟩ = true := by
          have := hflag 0 (by simp)
          simpa using this
        refine ⟨2 * N.k + 4, hpre, fun _ => ⟨by simp,
          moveInputPos d.inputPos (nf_act N (fun p => some (rec p)) q).inputTape, ?_⟩,
          fun hn => absurd ?_ hn⟩
        · rw [hrun, if_pos hl]
          simp
        · intro r hr
          simp at hr
          subst hr
          exact ⟨hlive, hdec⟩
      | cons rec' rs' =>
        have hl : rec ⟨2 * N.k + 3, by omega⟩ = false := by
          have := hflag 0 (by simp)
          simpa using this
        rw [if_neg (by simp [hl])] at hrun
        set d' : Cfg 2 Bool (nf_LeafSt N) x := { d with
          state := some (.read ((0, fun _ => none),
            nf_complete N (fun p => some (rec p)) ctl))
          inputPos := moveInputPos d.inputPos (nf_act N (fun p => some (rec p)) q).inputTape
          workTapePos := Function.update d.workTapePos 0
            (d.workTapePos 0 + (2 * N.k + 4 : ℕ)) } with hd'
        have hvc : (nf_complete N (fun p => some (rec p)) ctl).1 = (nf_vstep N c rec).state := by
          obtain ⟨cs, o, f⟩ := ctl
          simp only at hc
          subst hc
          simp only [nf_complete, nf_vstep, hq]
          exact (Action.apply_state _ _).symm
        have hvip : d'.inputPos = (nf_vstep N c rec).inputPos := by
          show moveInputPos d.inputPos _ = _
          simp only [nf_vstep, hq]
          rw [Action.apply_inputPos, hip]
        have hA' : ∀ p : ℕ, p < ((rec' :: rs').flatMap List.ofFn).length →
            d'.workTapes 0 (d'.workTapePos 0 + p) = ((rec' :: rs').flatMap List.ofFn)[p]? := by
          intro p hp
          show d.workTapes 0 (Function.update d.workTapePos 0
            (d.workTapePos 0 + (2 * N.k + 4 : ℕ)) 0 + p) = _
          rw [Function.update_self]
          exact hA1 p hp
        have hflag' : ∀ r (h : r < (rec' :: rs').length),
            (rec' :: rs')[r] ⟨2 * N.k + 3, by omega⟩ = decide (r + 1 = (rec' :: rs').length) := by
          intro r hr
          have := hflag (r + 1) (by simp at hr ⊢; omega)
          simpa using this
        obtain ⟨T', hpre', hpass', hrej'⟩ := nf_leaf_run_in N (rec' :: rs') d'
          (nf_complete N (fun p => some (rec p)) ctl) (nf_vstep N c rec) (by simp) hflag' rfl hvc
          hvip hA'
        refine ⟨(2 * N.k + 4) + T', fun u hu s hs => ?_, fun h => ?_, fun h => ?_⟩
        · by_cases hu1 : u < 2 * N.k + 4
          · exact hpre u hu1 s hs
          · obtain ⟨v, rfl⟩ : ∃ v, u = (2 * N.k + 4) + v := ⟨u - (2 * N.k + 4), by omega⟩
            rw [MultiTapeTM.runFrom_add, hrun] at hs
            exact hpre' v (by omega) s hs
        · obtain ⟨hT, ip, hcfg⟩ := hpass' ((hall.mp h).2)
          refine ⟨by rw [hT]; simp; ring, ip, ?_⟩
          rw [MultiTapeTM.runFrom_add, hrun, hcfg]
          apply Cfg.ext
          · rfl
          · rfl
          · rfl
          · funext i
            by_cases hi : i = 0
            · subst hi
              simp only [hd', Function.update_self, List.length_cons]
              push_cast
              ring
            · simp only [hd', Function.update_of_ne hi]
          · rfl
        · have hn : ¬ ∀ r (h : r < (rec' :: rs').length),
              nf_ok N (((rec' :: rs').take r).foldl (nf_vstep N) (nf_vstep N c rec))
                (rec' :: rs')[r] 0 := fun h' => h (hall.mpr ⟨⟨hlive, hdec⟩, h'⟩)
          rw [MultiTapeTM.runFrom_add, hrun]
          exact hrej' hn
    · refine ⟨2 * N.k + 4, hpre, fun h => absurd ((hall.mp h).1) hok, fun _ => hrej ?_⟩
      by_cases hl : c.state = none
      · exact Or.inl (hc.trans hl)
      · refine Or.inr fun hdec => hok ⟨hl, ?_⟩
        rw [hdec, hinp]
        rfl

end LeafRun

/-- **The linear-overhead coded normal form** ([BGW70]-style guess-then-verify,
cited through [AB09, §3.2]; statement; proof incomplete): every
nondeterministic machine has a coded (two-work-tape) equivalent whose
acceptance tracks the original's at linear time overhead — forward with the
explicit constant, backward in unbounded form (the consumer recovers the
budgeted form from the original's all-branch halting by the truncation
argument, `Turing.NDTM.runWith_of_halt`).

**Proof sketch.** Guess-then-verify, the reason codes carry **two** work
tapes: on tape A the simulator guesses, left to right and one choice bit per
guessed bit, the full display sequence of a `k`-tape run of `N` — per step
the choice bit, the state, the `k + 1` scanned symbols, and the action record
(`O_N(1)` cells per step) — checking the **control-local** part on the fly
(each record must follow from its predecessor by `N`'s table, hardwired in
the simulator's finite control). Then the non-local reads are verified in
`k + 1` sweeps: the input claims by replaying the claimed input-head moves
against the real input tape, and each work tape `j` by replaying tape `j` on
tape B — B's head tracks tape `j`'s claimed head, so each step checks the
claimed read against B's cell and applies the claimed write at unit cost —
rewinding A and clearing B between sweeps. Total `O_N((k+1)·(t+1)) =
C·(t+1)` — the `k+1` covers the zero-work-tape case, where the display
guess and the input sweep remain.
Forward transfer: a genuine accepting run of length `t` yields the accepting
display, guessed and verified within `C·(t+1)`. Backward: a verified display
**is** a genuine run (the sweeps force consistency), so an accepting branch
of the simulator exhibits an accepting branch of `N` at some length —
unbounded on purpose: runaway guessing branches never accept, and no
all-branch-halting claim is made for the simulator. State-space finiteness
packages as `Fin` by the relabeling `Turing.NDTM.relabelState` (the
nondeterministic mirror of `Turing.MultiTapeTM.relabelState`, as in the
`exists_codeTM` precedent). Fill obligations, named: the display format and
its on-the-fly control check; the `k + 1` verification sweeps; the two
transfer directions; the relabeling packaging.

**Implementation.** The display refines the sketch: one record of `2k + 4`
bits per step of `N`, holding the step's choice bit, the claimed input and
work-tape reads (two bits each: `00` blank, `10` false, `11` true) and an end
flag, set on the last record only. States and actions are not guessed: the
verifier recomputes them from `N`'s table in its finite control. The guess
runs under the controller-stopped host `Turing.guessCtlRunTM` with a trivial
setup; its controller stops at the first record boundary after a set end
flag. The verifier is deterministic and silent: a control sweep (a fold by
`Turing.scanTM`) checks the recomputed states, the end flags and the output,
and replay sweeps check the claimed reads against the input and, on the
second work tape, against each replayed work tape, which `Turing.skipTM`,
`Turing.skipBackTM` and `Turing.clearTM` then erase. -/
theorem exists_codeNDTM_accepts_linear (N : FinNDTM Bool) :
    ∃ (M : CodeNDTM) (C : ℕ),
      (∀ (x : List Bool) (t : ℕ),
        N.AcceptsWithin x t → M.toFinNDTM.AcceptsWithin x (C * (t + 1))) ∧
      (∀ (x : List Bool) (t : ℕ),
        M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t') := by
  sorry

end FinNDTM

end Turing
