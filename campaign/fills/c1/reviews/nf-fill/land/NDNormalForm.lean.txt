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
