/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.Light.Renumber
import TCSlib.Programs.Light.Calls
import TCSlib.Programs.Light.Regions
import TCSlib.Programs.Light.Lib.Pass
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Running a Turing machine inside a Light program

For every finite binary Turing machine `M` there is a Light procedure that runs `M` on a bit string
held in memory and writes `M`'s output to memory, within a time linear in `M`'s running time plus
the input length (`Light.exists_tmProc`). The procedure is part of a program `Q` that depends on
`M` only. Placed behind any program with `Program.behind` (`Light/Renumber`), and followed by any
procedures, it keeps its specification, so other programs can call it as a subroutine.

This is the reverse of stage 2 (`WordRAM.exists_simulation`, a word-RAM program run by a Turing
machine). It lets a program call any polynomial-time function given only by a machine, for
instance an abstract operation known to be `PolyTimeComputable`.

## Main results

* `Light.exists_tmProc`: the procedure and its specification.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.6: Turing machines and their simulation; Exercise
  1.9.)
* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the language Light and its logic (`TCSlib/Programs/Light`).
-/

namespace Light

/-! ## Private encoding and placement lemmas -/

/-- A signed work-tape position has an even code on the nonnegative side and an odd code on
its negative side. This is the direct-address layout used for the work tapes. -/
private def tmCell (z : ℤ) : ℕ :=
  if z < 0 then 2 * (-z).toNat + 1 else 2 * z.toNat

/-- Distinct signed positions have distinct cell codes. -/
private theorem tmCell_injective : Function.Injective tmCell := by
  intro z w h
  unfold tmCell at h
  split_ifs at h <;> omega

/-- Positions within radius `n` use cell codes at most `2 * n + 1`. -/
private theorem tmCell_le {z : ℤ} {n : ℕ} (h : |z| ≤ (n : ℤ)) :
    tmCell z ≤ 2 * n + 1 := by
  rw [abs_le] at h
  unfold tmCell
  split_ifs <;> omega

/-- The first `2 * i` cell codes are exactly the signed positions of absolute value below `i`. -/
private theorem tmCell_lt_iff (z : ℤ) (i : ℕ) :
    tmCell z < 2 * i ↔ |z| < (i : ℤ) := by
  rw [abs_lt]
  unfold tmCell
  split_ifs <;> omega

/-- Tape `j` uses the corresponding residue class in an interleaved scratch array. -/
private def tmAddr (sc tapes : ℕ) (j : Fin tapes) (z : ℤ) : ℕ :=
  sc + tmCell z * tapes + j.val

/-- Quotient and remainder uniquely identify a bank number and its finite index. -/
private theorem tmIndex_injective {k q r : ℕ} {j l : Fin k}
    (h : q * k + j.val = r * k + l.val) : q = r ∧ j = l := by
  have hk : 0 < k := by have := j.isLt; omega
  have hq := (Nat.div_mod_unique (a := q * k + j.val) (b := k) (d := q) (c := j.val) hk).mpr
    ⟨by rw [Nat.mul_comm k q, Nat.add_comm], j.isLt⟩
  have hr := (Nat.div_mod_unique (a := r * k + l.val) (b := k) (d := r) (c := l.val) hk).mpr
    ⟨by rw [Nat.mul_comm k r, Nat.add_comm], l.isLt⟩
  exact ⟨hq.1.symm.trans ((congrArg (fun n => n / k) h).trans hr.1),
    Fin.ext (hq.2.symm.trans ((congrArg (fun n => n % k) h).trans hr.2))⟩

/-- Two static local-bank indices differ if their banks or finite indices differ. -/
private theorem tmLocal_ne {k r s : ℕ} {j l : Fin k} (h : r ≠ s ∨ j ≠ l) :
    10 + r * k + j.val ≠ 10 + s * k + l.val := by
  intro he
  have he' : r * k + j.val = s * k + l.val := by omega
  obtain ⟨hrs, hjl⟩ := tmIndex_injective he'
  rcases h with h | h
  · exact h hrs
  · exact h hjl

/-- The interleaved address identifies both the tape and its signed position.

**Proof sketch.** Cancel the scratch base. `tmIndex_injective`, through `Nat.div_mod_unique`,
identifies the cell code and the finite tape index. `tmCell_injective` identifies the signed
positions. -/
private theorem tmAddr_injective {sc tapes : ℕ} {j l : Fin tapes} {z w : ℤ}
    (h : tmAddr sc tapes j z = tmAddr sc tapes l w) : j = l ∧ z = w := by
  unfold tmAddr at h
  obtain ⟨hc, hj⟩ := tmIndex_injective (show tmCell z * tapes + j.val = tmCell w * tapes + l.val by omega)
  exact ⟨hj, tmCell_injective hc⟩

/-- A cell in radius `n` lies in the first `tapes * (2 * n + 2)` scratch cells. -/
private theorem tmAddr_lt {sc tapes n : ℕ} (j : Fin tapes) {z : ℤ}
    (hz : |z| ≤ (n : ℤ)) : tmAddr sc tapes j z < sc + tapes * (2 * n + 2) := by
  have hc := tmCell_le hz
  have hm := Nat.mul_le_mul_right tapes hc
  have hj := j.isLt
  unfold tmAddr
  nlinarith

/-- Before step `i`, every work head is within radius `i` of the origin. -/
private theorem tmHead_abs_le (M : Turing.FinTM Bool) (x : List Bool) (i : ℕ)
    (j : Fin M.k) :
    |(M.tm.runFrom (M.tm.initCfg x) i).workTapePos j| ≤ (i : ℤ) := by
  have h := M.tm.workTapePos_runFrom_mem_Icc (M.tm.initCfg x) i j
  rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_workTapePos] at h
  rw [Turing.MultiTapeTM.initCfg_eq, abs_le]
  simpa only [Finset.mem_Icc, zero_sub, zero_add] using h

/-- At time `i`, cells at distance at least `i` are still blank. A simulator may initialize
these cells as it expands its scratch region, without a time bound supplied to the program.

**Proof sketch.** Induct on `i`. The initial tapes are blank by `Cfg.init_workTapes`. A live
step writes only at its current head (`Action.apply_workTapes`), which has distance at most
`i` by `tmHead_abs_le`; a cell at distance at least `i + 1` is different. A halted step is
stationary (`MultiTapeTM.step_of_halt`). -/
private theorem tmTape_blank (M : Turing.FinTM Bool) (x : List Bool) (i : ℕ)
    (j : Fin M.k) (z : ℤ) (hz : (i : ℤ) ≤ |z|) :
    (M.tm.runFrom (M.tm.initCfg x) i).workTapes j z = none := by
  induction i with
  | zero =>
    rw [Turing.MultiTapeTM.runFrom_zero, Turing.MultiTapeTM.initCfg_eq,
      Turing.Cfg.init_workTapes]
  | succ i ih =>
    have hi : (i : ℤ) ≤ |z| := by omega
    have hb := tmHead_abs_le M x i j
    have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) i).workTapePos j := by
      intro he
      rw [he] at hz
      omega
    rw [Turing.MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (M.tm.runFrom (M.tm.initCfg x) i).state with
    | none =>
      rw [Turing.MultiTapeTM.step_of_halt hs]
      exact ih hi
    | some q =>
      rw [Turing.MultiTapeTM.step_of_some hs, Turing.Action.apply_workTapes,
        Function.update_of_ne hne]
      exact ih hi

/-- A completed computation has a positive first halting time no greater than its deadline,
with the prescribed output and live states at every earlier time. -/
private theorem tmFirstHalt (M : Turing.FinTM Bool) {x out : List Bool} {t : ℕ}
    (h : M.ComputesInTime x out t) :
    ∃ u ≤ t, 0 < u ∧
      (M.tm.runFrom (M.tm.initCfg x) u).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) u).output = out ∧
      ∀ i < u, (M.tm.runFrom (M.tm.initCfg x) i).state ≠ none := by
  obtain ⟨hh, ho⟩ := (Turing.FinTM.computesInTime_iff M x out t).mp h
  obtain ⟨u, hu, hlive, he⟩ := M.tm.exists_first_halt (M.tm.initCfg x) hh
  have hhalt : (M.tm.runFrom (M.tm.initCfg x) u).state = none := by rw [he]; exact hh
  have hpos : 0 < u := by
    by_contra hn
    have hz : u = 0 := by omega
    rw [hz, Turing.MultiTapeTM.runFrom_zero, Turing.MultiTapeTM.initCfg_eq,
      Turing.Cfg.init_state] at hhalt
    cases hhalt
  exact ⟨u, hu, hpos, hhalt, by rw [he]; exact ho, hlive⟩

/-- Relocating a procedure and appending other procedures preserves its specification. -/
private theorem tmMeets_behind {lim : Limits} {Q : Program} {p d T : ℕ}
    {args : List ℤ} {μ : ℕ → ℤ} {R : ℤ → (ℕ → ℤ) → Prop}
    (h : Meets lim Q p d args μ T R) (Pre Post : Program) :
    Meets lim (Program.behind Pre Q ++ Post) (p + Pre.length) d args μ T R := by
  obtain ⟨body, hp, he⟩ := (meets_iff ..).mp h
  exact Meets.of_body (getElem?_append_of_eq_some (Program.getElem?_behind_right Pre hp) Post)
    (he.shift_append Pre Post)

/-! ## Private primitive block rules -/

/-- A safe assignment with a known expression value has the displayed exact local update. -/
private theorem tmSet_runs {lim : Limits} {σ : State} {dst : ℕ} {e : Expr} {z : ℤ}
    (hs : e.Safe lim σ) (hv : e.val σ = z) :
    (Stmt.set dst e).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc dst z } := by
  refine ⟨(Stmt.blockSafe_set_iff _ _ _ _).mpr hs, ?_⟩
  rw [Stmt.after_set, hv]

/-- A safe store with a known in-range natural address and value has the displayed exact
memory update and preserves the local variables. -/
private theorem tmStore_runs {lim : Limits} {σ : State} {addr value : Expr} {b : ℕ} {z : ℤ}
    (ha : addr.Safe lim σ) (he : value.Safe lim σ) (haddr : addr.val σ = (b : ℤ))
    (hv : value.val σ = z) (hb : b < lim.space) :
    (Stmt.store addr value).Runs lim σ fun τ =>
      τ = { σ with mem := Function.update σ.mem b z } := by
  refine ⟨(Stmt.blockSafe_store_iff _ _ _ _).mpr ⟨ha, he, ?_⟩, ?_⟩
  · rw [haddr, Limits.addr_iff]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hb⟩
  · rw [Stmt.after_store, haddr, hv, Int.toNat_natCast]

/-! ## Private finite branch selection -/

/-- The listed locals have the listed natural values. -/
private def tmMatches (tests : List (ℕ × ℕ)) (σ : State) : Prop :=
  ∀ pair ∈ tests, σ.loc pair.1 = (pair.2 : ℤ)

/-- Test a fixed finite list of local values, choosing `yes` only when all agree. -/
private def tmSelect : List (ℕ × ℕ) → Stmt → Stmt → Stmt
  | [], yes, _ => yes
  | pair :: rest, yes, no =>
      .ite (.eq (.var pair.1) (.const pair.2)) (tmSelect rest yes no) no

/-- Finite branch selection preserves any common postcondition of its two alternatives.

**Proof sketch.** Induct on the tests. `Stmt.Runs.ite_pos` removes a matching head test,
and `Stmt.Runs.ite_neg` selects the failure alternative as soon as a local differs. The
constructor readers of `Expr` and `Cond` discharge the safe comparison and its value. -/
private theorem tmSelect_runs {lim : Limits} {σ : State} {tests : List (ℕ × ℕ)}
    {yes no : Stmt} {R : State → Prop}
    (hs : ∀ pair ∈ tests, (pair.2 : ℤ) ≤ lim.word)
    (hy : tmMatches tests σ → yes.Runs lim σ R)
    (hn : ¬tmMatches tests σ → no.Runs lim σ R) :
    (tmSelect tests yes no).Runs lim σ R := by
  induction tests with
  | nil => exact hy (by simp only [tmMatches, List.not_mem_nil, false_implies, implies_true])
  | cons pair rest ih =>
    have hsafe : (Cond.eq (.var pair.1) (.const pair.2)).Safe lim σ := by
      rw [Cond.safe_eq_iff, Expr.safe_var_iff, Expr.safe_const_iff]
      exact ⟨trivial, hs pair (List.mem_cons_self ..)⟩
    have hholds : (Cond.eq (.var pair.1) (.const pair.2)).Holds σ ↔
        σ.loc pair.1 = (pair.2 : ℤ) := by
      rw [Cond.holds_eq_iff, Expr.val_var, Expr.val_const]
    by_cases hp : σ.loc pair.1 = (pair.2 : ℤ)
    · apply Stmt.Runs.ite_pos (c := .eq (.var pair.1) (.const pair.2))
        (ih (fun p h => hs p (List.mem_cons_of_mem _ h)) ?_ ?_) (hholds.mpr hp) hsafe
      · intro hr
        apply hy
        intro p h
        rcases List.mem_cons.mp h with he | he
        · subst p; exact hp
        · exact hr p he
      · intro hr
        apply hn
        intro hall
        exact hr fun p h => hall p (List.mem_cons_of_mem _ h)
    · apply Stmt.Runs.ite_neg (c := .eq (.var pair.1) (.const pair.2))
        (hn ?_) (fun hh => hp (hholds.mp hh)) hsafe
      intro hall
      exact hp (hall pair (List.mem_cons_self ..))

/-- A finite table compiled as code branches, with no transition table stored in memory. -/
private def tmDispatch {α : Type} (tests : α → List (ℕ × ℕ)) (body : α → Stmt) : List α → Stmt
  | [] => .skip
  | row :: rest => tmSelect (tests row) (body row) (tmDispatch tests body rest)

/-- A compiled finite table executes the selected row whenever that row occurs in the table.

**Proof sketch.** Induct on the rows and use `tmSelect_runs` for the first row. A successful
test identifies that row with `actual`. A failed test excludes it, so the occurrence of
`actual` is in the tail, where the induction hypothesis applies. -/
private theorem tmDispatch_runs {α : Type} {lim : Limits} {σ : State}
    {tests : α → List (ℕ × ℕ)} {body : α → Stmt} {rows : List α} {actual : α}
    {R : State → Prop} (ha : actual ∈ rows)
    (hs : ∀ row ∈ rows, ∀ pair ∈ tests row, (pair.2 : ℤ) ≤ lim.word)
    (hm : ∀ row ∈ rows, tmMatches (tests row) σ ↔ row = actual)
    (hr : (body actual).Runs lim σ R) :
    (tmDispatch tests body rows).Runs lim σ R := by
  induction rows with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons row rest ih =>
    apply tmSelect_runs (hs row (List.mem_cons_self ..))
    · intro ht
      have he := (hm row (List.mem_cons_self ..)).mp ht
      subst row
      exact hr
    · intro hn
      have hat : actual ∈ rest := by
        rcases List.mem_cons.mp ha with he | he
        · exact False.elim (hn ((hm row (List.mem_cons_self ..)).mpr he.symm))
        · exact he
      exact ih hat (fun r hh => hs r (List.mem_cons_of_mem _ hh))
        (fun r hh => hm r (List.mem_cons_of_mem _ hh))

/-! ## Private simulator program -/

/-- Blank, false, and true have codes zero, one, and two. -/
private def tmSym : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The nonblank symbol code is the bit value plus one. -/
private theorem tmSym_some_eq (bit : Bool) : tmSym (some bit) = bit.toNat + 1 := by
  cases bit <;> rfl

/-- Every encoded work symbol is at most two. -/
private theorem tmSym_le_two (sym : Option Bool) : tmSym sym ≤ 2 := by
  cases sym with
  | none => decide
  | some bit =>
    rw [tmSym_some_eq]
    exact Nat.add_le_add_right (Bool.toNat_le bit) 1

/-- A bit string represented as one integer word per bit in memory. -/
private def tmBits (bits : List Bool) : List ℤ := bits.map fun bit => (bit.toNat : ℤ)

/-- Zero the next pair of cell-code rows, leaving all previously initialized rows alone. -/
private def tmRingMemory (sc tapes i : ℕ) (μ : ℕ → ℤ) : ℕ → ℤ :=
  wrote μ (sc + 2 * i * tapes) (fun _ => 0) (2 * tapes)

/-- Initializing the next ring preserves every earlier represented cell. -/
private theorem tmRingMemory_old {sc tapes i : ℕ} (μ : ℕ → ℤ) (j : Fin tapes) (z : ℤ)
    (hz : tmCell z < 2 * i) :
    tmRingMemory sc tapes i μ (tmAddr sc tapes j z) = μ (tmAddr sc tapes j z) := by
  have hm := Nat.mul_le_mul_right tapes (show tmCell z + 1 ≤ 2 * i by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  have hj := j.isLt
  apply wrote_rest
  left
  unfold tmAddr
  omega

/-- Every cell in the new pair of cell-code rows is initialized to blank. -/
private theorem tmRingMemory_new {sc tapes i : ℕ} (μ : ℕ → ℤ) (j : Fin tapes) (z : ℤ)
    (hlo : 2 * i ≤ tmCell z) (hhi : tmCell z < 2 * i + 2) :
    tmRingMemory sc tapes i μ (tmAddr sc tapes j z) = 0 := by
  have hj := j.isLt
  have hlow : sc + 2 * i * tapes ≤ tmAddr sc tapes j z := by
    unfold tmAddr
    nlinarith
  have hhigh : tmAddr sc tapes j z < sc + 2 * i * tapes + 2 * tapes := by
    unfold tmAddr
    nlinarith
  have hoff : tmAddr sc tapes j z - (sc + 2 * i * tapes) < 2 * tapes := by omega
  have he : sc + 2 * i * tapes + (tmAddr sc tapes j z - (sc + 2 * i * tapes)) =
      tmAddr sc tapes j z := Nat.add_sub_of_le hlow
  exact he ▸ (wrote_done (μ := μ) (f := fun _ => (0 : ℤ)) hoff)

/-- The three symbol codes distinguish blank and the two bits. -/
private theorem tmSym_injective : Function.Injective tmSym := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b <;> simp only [tmSym, Nat.reduceEqDiff] at h
  | some a => cases b with
    | none => cases a <;> simp only [tmSym, Nat.reduceEqDiff] at h
    | some b => cases a <;> cases b <;> simp_all only [tmSym, Nat.reduceEqDiff]

/-- Clearing the next ring extends a correct tape encoding from strict radius `i` to radius `i`. -/
private theorem tmRingMemory_tapes (M : Turing.FinTM Bool) (x : List Bool) (i sc : ℕ)
    (μ : ℕ → ℤ)
    (hμ : ∀ (j : Fin M.k) (z : ℤ), |z| < (i : ℤ) →
      μ (tmAddr sc M.k j z) = (tmSym ((M.tm.runFrom (M.tm.initCfg x) i).workTapes j z) : ℤ)) :
    ∀ (j : Fin M.k) (z : ℤ), |z| ≤ (i : ℤ) →
      tmRingMemory sc M.k i μ (tmAddr sc M.k j z) =
        (tmSym ((M.tm.runFrom (M.tm.initCfg x) i).workTapes j z) : ℤ) := by
  intro j z hz
  by_cases hc : tmCell z < 2 * i
  · rw [tmRingMemory_old μ j z hc]
    exact hμ j z ((tmCell_lt_iff z i).mp hc)
  · have hlarge : (i : ℤ) ≤ |z| := by
      have hn : ¬ |z| < (i : ℤ) := fun hh => hc ((tmCell_lt_iff z i).mpr hh)
      omega
    have hhi : tmCell z < 2 * i + 2 := by have := tmCell_le hz; omega
    rw [tmRingMemory_new μ j z (by omega) hhi, tmTape_blank M x i j z hlarge]
    rfl

/-- The live states have positive indices in a fixed enumeration; zero denotes halt. -/
private noncomputable def tmStateCode (M : Turing.FinTM Bool) : Option M.State → ℕ
  | none => 0
  | some q => 1 + (Finset.univ.toList : List M.State).idxOf q

/-- Distinct optional machine states have distinct control-state codes. -/
private theorem tmStateCode_injective (M : Turing.FinTM Bool) :
    Function.Injective (tmStateCode M) := by
  classical
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => simp only [tmStateCode] at h; omega
  | some a => cases b with
    | none => simp only [tmStateCode] at h; omega
    | some b =>
      have ha : a ∈ (Finset.univ.toList : List M.State) :=
        Finset.mem_toList.mpr (Finset.mem_univ a)
      have hb : b ∈ (Finset.univ.toList : List M.State) :=
        Finset.mem_toList.mpr (Finset.mem_univ b)
      simp only [tmStateCode] at h
      exact congrArg some ((List.idxOf_inj ha hb).mp (by omega))

/-- All control-state codes are bounded by the size of the fixed state enumeration plus one. -/
private theorem tmStateCode_le (M : Turing.FinTM Bool) (q : Option M.State) :
    tmStateCode M q ≤ (Finset.univ.toList : List M.State).length + 1 := by
  classical
  cases q with
  | none => exact Nat.zero_le _
  | some q =>
    simpa only [tmStateCode, Nat.add_comm] using
      Nat.add_le_add_left (List.idxOf_le_length (a := q)
        (l := (Finset.univ.toList : List M.State))) 1

/-- A transition row specifies a live state and the input and work symbols it scans. -/
private abbrev TMRow (M : Turing.FinTM Bool) :=
  M.State × (Option Bool × (Fin M.k → Option Bool))

/-- All transition rows of a finite binary machine, enumerated once when generating the code. -/
private noncomputable def tmRows (M : Turing.FinTM Bool) : List (TMRow M) :=
  Finset.univ.toList

/-- Sequential composition of a fixed list of statements. -/
private def tmSeq : List Stmt → Stmt
  | [] => .skip
  | s :: rest => .seq s (tmSeq rest)

/-- A static bank preserves its invariant, establishes the property of every visited index,
and preserves that property at any index where it already held.

**Proof sketch.** Induct over the statically generated statement list and compose with
`Stmt.Runs.seq`. Each single block preserves the invariant and all previously established
index properties; the tail therefore preserves the head's property as well as its own. -/
private theorem tmSeq_accumulate {α : Type} {lim : Limits} {body : α → Stmt}
    {I : State → Prop} {F : α → State → Prop} {rows : List α} {σ : State}
    (hi : I σ)
    (hr : ∀ j ∈ rows, ∀ τ, I τ → (body j).Runs lim τ fun τ' =>
      I τ' ∧ F j τ' ∧ ∀ l, F l τ → F l τ') :
    (tmSeq (rows.map body)).Runs lim σ fun τ =>
      I τ ∧ (∀ j ∈ rows, F j τ) ∧ ∀ j, F j σ → F j τ := by
  induction rows generalizing σ with
  | nil =>
    constructor
    · exact (Stmt.blockSafe_skip_iff lim σ).mpr trivial
    · simp only [List.map_nil, tmSeq, Stmt.after_skip]
      exact ⟨hi, fun _ hh => False.elim (List.not_mem_nil hh), fun _ hh => hh⟩
  | cons j rest ih =>
    apply Stmt.Runs.seq
    apply (hr j (List.mem_cons_self ..) σ hi).mono
    intro τ hτ
    apply (ih hτ.1 (fun l hl => hr l (List.mem_cons_of_mem _ hl))).mono
    intro τ' hτ'
    refine ⟨hτ'.1, ?_, fun l hl => hτ'.2.2 l (hτ.2.2 l hl)⟩
    intro l hl
    rcases List.mem_cons.mp hl with he | he
    · subst l
      exact hτ'.2.2 j hτ.2.1
    · exact hτ'.2.1 l he

/-- One statically generated block per work tape. -/
private def tmBank (M : Turing.FinTM Bool) (body : Fin M.k → Stmt) : Stmt :=
  tmSeq ((List.finRange M.k).map body)

/-- Local numbers for work heads, scanned work symbols, and computed tape addresses. The first
ten locals hold the arguments, input position, control state, output length, and round number. -/
private def tmHead (j : ℕ) : ℕ := 10 + j
private def tmScan (tapes j : ℕ) : ℕ := 10 + tapes + j
private def tmAddress (tapes j : ℕ) : ℕ := 10 + 2 * tapes + j
private def tmOldHead (tapes j : ℕ) : ℕ := 10 + 3 * tapes + j

/-! ## Private representation invariant -/

/-- The stable locals describing one simulated configuration. The temporary locals for
addresses, frozen heads, scans, and scratch initialization are deliberately unconstrained. -/
private structure TMFrame (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (a b sc i : ℕ) (σ : State) : Prop where
  src : σ.loc 0 = (a : ℤ)
  len : σ.loc 1 = (x.length : ℤ)
  dst : σ.loc 2 = (b : ℤ)
  scratch : σ.loc 3 = (sc : ℤ)
  inputPos : σ.loc 4 = (c.inputPos.val : ℤ)
  control : σ.loc 5 = (tmStateCode M c.state : ℤ)
  outputLen : σ.loc 6 = (c.output.length : ℤ)
  round : σ.loc 7 = (i : ℤ)
  heads : ∀ j : Fin M.k, σ.loc (tmHead j.val) = c.workTapePos j

/-- The frozen work heads and their direct addresses for one simulated configuration. -/
private structure TMLocated (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (sc : ℕ) (σ : State) : Prop where
  oldHeads : ∀ j : Fin M.k, σ.loc (tmOldHead M.k j.val) = c.workTapePos j
  addresses : ∀ j : Fin M.k,
    σ.loc (tmAddress M.k j.val) = (tmAddr sc M.k j (c.workTapePos j) : ℤ)

/-- The scanned input and work symbols captured before the transition writes any tape. -/
private structure TMScanned (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (σ : State) : Prop where
  input : σ.loc 9 = (tmSym c.inputSymbol : ℤ)
  work : ∀ j : Fin M.k, σ.loc (tmScan M.k j.val) = (tmSym (c.workTapeSymbols j) : ℤ)

/-- The represented cells of all work tapes within a strict radius. -/
private def TMTapes (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (sc radius : ℕ) (μ : ℕ → ℤ) : Prop :=
  ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) →
    μ (tmAddr sc M.k j z) = (tmSym (c.workTapes j z) : ℤ)

/-- The represented work cells away from the old head on each tape; old head cells may be
rewritten while a transition's static tape bank is executing. -/
private def TMTapesAway (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (sc radius : ℕ) (μ : ℕ → ℤ) : Prop :=
  ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) → z ≠ c.workTapePos j →
    μ (tmAddr sc M.k j z) = (tmSym (c.workTapes j z) : ℤ)

/-- Writing at an old work head preserves every represented cell away from all old heads.
The address injectivity theorem separates both different tapes and different signed cells. -/
private theorem tmTapesAway_write {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {sc radius : ℕ} {μ : ℕ → ℤ} (j : Fin M.k)
    (h : TMTapesAway M c sc radius μ) (value : ℤ) :
    TMTapesAway M c sc radius
      (Function.update μ (tmAddr sc M.k j (c.workTapePos j)) value) := by
  intro l z hz hne
  have haddr : tmAddr sc M.k l z ≠ tmAddr sc M.k j (c.workTapePos j) := by
    intro he
    obtain ⟨hjl, hp⟩ := tmAddr_injective he
    subst l
    exact hne hp
  rw [Function.update_of_ne haddr]
  exact h l z hz hne

/-- The locals constrained by `TMFrame`: the eight scalar locals and the current work heads. -/
private def tmKeyLocal (M : Turing.FinTM Bool) (v : ℕ) : Prop :=
  v < 8 ∨ ∃ j : Fin M.k, v = tmHead j.val

/-- Preserving the stable locals other than the round counter, and assigning a new counter,
preserves the configuration frame at that new round. -/
private theorem tmFrame_transfer {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {a b sc i i' : ℕ} {σ τ : State}
    (hf : TMFrame M c a b sc i σ)
    (he : ∀ v, tmKeyLocal M v → v ≠ 7 → τ.loc v = σ.loc v)
    (hround : τ.loc 7 = (i' : ℤ)) : TMFrame M c a b sc i' τ := by
  constructor
  · exact (he 0 (Or.inl (by decide)) (by decide)).trans hf.src
  · exact (he 1 (Or.inl (by decide)) (by decide)).trans hf.len
  · exact (he 2 (Or.inl (by decide)) (by decide)).trans hf.dst
  · exact (he 3 (Or.inl (by decide)) (by decide)).trans hf.scratch
  · exact (he 4 (Or.inl (by decide)) (by decide)).trans hf.inputPos
  · exact (he 5 (Or.inl (by decide)) (by decide)).trans hf.control
  · exact (he 6 (Or.inl (by decide)) (by decide)).trans hf.outputLen
  · exact hround
  · intro j
    exact (he (tmHead j.val) (Or.inr ⟨j, rfl⟩) (by unfold tmHead; omega)).trans (hf.heads j)

/-- Assigning the round local changes only the round index of the represented frame. -/
private theorem tmFrame_round {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {a b sc i : ℕ} {σ : State}
    (hf : TMFrame M c a b sc i σ) (i' : ℕ) :
    TMFrame M c a b sc i' ⟨Function.update σ.loc 7 (i' : ℤ), σ.mem⟩ := by
  apply tmFrame_transfer hf
  · intro v _ hv
    exact Function.update_of_ne hv (i' : ℤ) σ.loc
  · change Function.update σ.loc 7 (i' : ℤ) 7 = (i' : ℤ)
    exact Function.update_self ..

/-- Changing a temporary local outside the scalar and head banks preserves the frame,
with no restriction on the replacement memory. -/
private theorem tmFrame_tmp {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {a b sc i r : ℕ} {σ : State} {z : ℤ}
    (hf : TMFrame M c a b sc i σ) (hr : 8 ≤ r) (hgap : r < 10 ∨ 10 + M.k ≤ r)
    (ν : ℕ → ℤ) : TMFrame M c a b sc i ⟨Function.update σ.loc r z, ν⟩ := by
  apply tmFrame_transfer hf
  · intro v hv _
    change Function.update σ.loc r z v = σ.loc v
    apply Function.update_of_ne
    intro he
    rcases hv with hv | ⟨j, hj⟩
    · omega
    · have hjlt := j.isLt
      unfold tmHead at hj
      rcases hgap with hgap | hgap <;> omega
  · change Function.update σ.loc r z 7 = (i : ℤ)
    rw [Function.update_of_ne (by omega)]
    exact hf.round

/-- A local update outside the frozen-head/address interval preserves the located data,
independently of the replacement memory. -/
private theorem tmLocated_tmp {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {sc r : ℕ} {σ : State} {z : ℤ}
    (hl : TMLocated M c sc σ) (hr : r < 10 + 2 * M.k ∨ 10 + 4 * M.k ≤ r)
    (ν : ℕ → ℤ) : TMLocated M c sc ⟨Function.update σ.loc r z, ν⟩ := by
  have he (v : ℕ) (hlo : 10 + 2 * M.k ≤ v) (hhi : v < 10 + 4 * M.k) :
      Function.update σ.loc r z v = σ.loc v := by
    apply Function.update_of_ne
    intro hv
    rcases hr with hr | hr <;> omega
  constructor
  · intro j
    exact (he _ (by unfold tmOldHead; omega)
      (by have := j.isLt; unfold tmOldHead; omega)).trans (hl.oldHeads j)
  · intro j
    exact (he _ (by unfold tmAddress; omega)
      (by have := j.isLt; unfold tmAddress; omega)).trans (hl.addresses j)

/-- Updating a local outside the captured input/work scan slots preserves their old symbol
codes, independently of the replacement memory. -/
private theorem tmScanned_tmp {M : Turing.FinTM Bool} {x : List Bool}
    {c : Turing.Cfg M.k Bool M.State x} {r : ℕ} {σ : State} {z : ℤ}
    (hs : TMScanned M c σ) (hr9 : r ≠ 9) (hr : r < 10 + M.k ∨ 10 + 2 * M.k ≤ r)
    (ν : ℕ → ℤ) : TMScanned M c ⟨Function.update σ.loc r z, ν⟩ := by
  constructor
  · exact (Function.update_of_ne hr9.symm z σ.loc).trans hs.input
  · intro j
    have hne : tmScan M.k j.val ≠ r := by
      have hj := j.isLt
      unfold tmScan
      rcases hr with hr | hr <;> omega
    exact (Function.update_of_ne hne z σ.loc).trans (hs.work j)

/-- The scratch address of the nonnegative cell code `code` on tape `j`. -/
private def tmAddrExpr (tapes j : ℕ) (code : Expr) : Expr :=
  .op .add (.var 3) (.op .add (.op .mul code (.const tapes)) (.const j))

/-- A natural cell-code expression gives the corresponding safe interleaved address whenever
its code, the two constants, and the resulting address fit the limits. -/
private theorem tmAddrExpr_read {lim : Limits} {σ : State} {tapes j sc n : ℕ}
    (code : Expr) (hsc : σ.loc 3 = (sc : ℤ)) (hc : code.Safe lim σ)
    (hv : code.val σ = (n : ℤ)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hk : (tapes : ℤ) ≤ lim.word) (hj : (j : ℤ) ≤ lim.word)
    (hs : sc + n * tapes + j ≤ lim.space) :
    (tmAddrExpr tapes j code).Safe lim σ ∧
      (tmAddrExpr tapes j code).val σ = ((sc + n * tapes + j : ℕ) : ℤ) := by
  have hsZ : (sc : ℤ) + (n : ℤ) * tapes + j ≤ (lim.space : ℤ) := by exact_mod_cast hs
  have hp : 0 ≤ (n : ℤ) * tapes := by positivity
  constructor
  · simp only [tmAddrExpr, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, Op.eval_mul,
      hsc, hv, hc, true_and, abs_le]
    omega
  · simp only [tmAddrExpr, Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add,
      Op.eval_mul, hsc, hv, Nat.cast_add, Nat.cast_mul, add_assoc]

/-- Initialize the next two interleaved cell-code rows using the existing pass routine.
Locals eight and nine hold its destination and length; its counter is beyond the tape locals. -/
private def tmClearRing (M : Turing.FinTM Bool) : Stmt :=
  tmSeq [.set 8 (tmAddrExpr M.k 0 (.op .mul (.const 2) (.var 7))),
    .set 9 (.const (2 * M.k)), pass (10 + 4 * M.k) (.var 9) (.var 8) (.const 0)]

/-- Clearing one newly reachable ring costs `26 * M.k + 18` steps, leaves the represented
memory `tmRingMemory`, and changes only the pass's three temporary locals.

**Proof sketch.** Compute the ring destination and its constant length in locals eight and
nine. Apply `Ends.pass` with the constant-zero expression, using the published expression
readers for its safety and cost. `wrote` is exactly `tmRingMemory`; the pass changes only its
counter, and `Function.update_of_ne` preserves the other locals. -/
private theorem tmClearRing_ends (M : Turing.FinTM Bool) {lim : Limits} {P : Program} {d : ℕ}
    (σ : State) (sc i : ℕ) (hsc : σ.loc 3 = (sc : ℤ)) (hi : σ.loc 7 = (i : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hs : sc + 2 * (i + 1) * M.k ≤ lim.space)
    (hi2 : (2 : ℤ) * ((i : ℤ) + 1) ≤ lim.word)
    (hk2 : (2 : ℤ) * M.k ≤ lim.word) :
    Ends lim P d (tmClearRing M) σ (26 * M.k + 18) fun τ =>
      τ.mem = tmRingMemory sc M.k i σ.mem ∧
      ∀ v, v ≠ 8 → v ≠ 9 → v ≠ 10 + 4 * M.k → τ.loc v = σ.loc v := by
  let dst := sc + 2 * i * M.k
  have hsZ : (sc : ℤ) + 2 * ((i : ℤ) + 1) * M.k ≤ (lim.space : ℤ) := by
    exact_mod_cast hs
  have hdst : dst + 2 * M.k ≤ lim.space := by dsimp only [dst]; nlinarith
  have hzero : (0 : ℤ) ≤ lim.word := by nlinarith [Int.natCast_nonneg M.k]
  have hc : (Expr.op .mul (.const 2) (.var 7)).Safe lim σ := by
    simp only [Expr.safe_op_iff, Expr.safe_const_iff, Expr.safe_var_iff, Expr.val_const,
      Expr.val_var, Op.eval_mul, hi, Nat.cast_ofNat, true_and, abs_le]
    omega
  have hvc : (Expr.op .mul (.const 2) (.var 7)).val σ = ((2 * i : ℕ) : ℤ) := by
    simp only [Expr.val_op, Expr.val_const, Expr.val_var, Op.eval_mul, hi,
      Nat.cast_mul, Nat.cast_ofNat]
  obtain ⟨hsafe, hv⟩ := tmAddrExpr_read (.op .mul (.const 2) (.var 7)) hsc hc hvc hw
    (show (M.k : ℤ) ≤ lim.word by omega) hzero
    (show sc + (2 * i) * M.k + 0 ≤ lim.space by dsimp only [dst] at hdst; omega)
  change (tmAddrExpr M.k 0 (.op .mul (.const 2) (.var 7))).val σ = (dst : ℤ) at hv
  unfold tmClearRing tmSeq
  refine Ends.seq 10 (26 * M.k + 8) (Ends.set hsafe ?_ ?_) (by omega)
  · simp only [tmAddrExpr, Expr.cost_op, Expr.cost_var, Expr.cost_const]
    omega
  · rw [hv]
    refine Ends.seq 2 (26 * M.k + 6) (Ends.set ?_ ?_ ?_) (by omega)
    · rw [Expr.safe_const_iff, Nat.cast_mul, Nat.cast_ofNat]
      exact hk2
    · rw [Expr.cost_const]
    · rw [Expr.val_const]
      refine Ends.seq (26 * M.k + 6) 0 ?_ (by omega)
      refine Ends.pass (c := 10 + 4 * M.k) (x := 9) (y := 8) (n := 2 * M.k)
        (dst := dst) (fun _ => (0 : ℤ)) ?_ ?_ hw hdst ?_ ?_
        (by omega) (by omega) ?_
      · intro j hj
        exact ⟨(Expr.safe_const_iff _ _ 0).mpr hzero, Expr.val_const _ 0⟩
      · apply Ends.skip
        refine ⟨rfl, ?_⟩
        intro v h8 h9 hc
        simp only [Function.update_of_ne hc, Function.update_of_ne h9,
          Function.update_of_ne h8]
      · change Function.update (Function.update σ.loc 8 (dst : ℤ)) 9 ((2 * M.k : ℕ) : ℤ) 9 =
          ((2 * M.k : ℕ) : ℤ)
        exact Function.update_self ..
      · change Function.update (Function.update σ.loc 8 (dst : ℤ)) 9 ((2 * M.k : ℕ) : ℤ) 8 =
          (dst : ℤ)
        rw [Function.update_of_ne (by decide : (8 : ℕ) ≠ 9)]
        exact Function.update_self ..
      · rw [Expr.cost_const]
        omega

/-- The two arithmetic branches computing a signed tape position's cell code. -/
private def tmCodeExpr (src : ℕ) : Bool → Expr
  | false => .op .mul (.const 2) (.var src)
  | true => .op .add (.op .mul (.const 2) (.op .sub (.const 0) (.var src))) (.const 1)

/-- The selected sign branch safely computes the signed cell code using only linear
arithmetic in the head position.

**Proof sketch.** Split on the sign branch and read each arithmetic constructor through its
published equations. `tmCell` has the same two branches; the sign hypothesis identifies
`Int.toNat` with the corresponding nonnegative position. The code bound controls every
intermediate value, and the separate bound on two controls the constants. -/
private theorem tmCodeExpr_read {lim : Limits} {σ : State} {src : ℕ} {z : ℤ}
    (negative : Bool) (hz : σ.loc src = z) (h2 : (2 : ℤ) ≤ lim.word)
    (hc : (tmCell z : ℤ) ≤ lim.word) (hside : if negative then z < 0 else 0 ≤ z) :
    (tmCodeExpr src negative).Safe lim σ ∧
      (tmCodeExpr src negative).val σ = (tmCell z : ℤ) := by
  cases negative with
  | false =>
    change 0 ≤ z at hside
    have hn : ¬z < 0 := by omega
    simp only [tmCodeExpr, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_mul, hz, tmCell, if_neg hn,
      Nat.cast_mul, Nat.cast_ofNat, true_and, abs_le] at hc ⊢
    omega
  | true =>
    change z < 0 at hside
    simp only [tmCodeExpr, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, Op.eval_mul, Op.eval_sub,
      hz, tmCell, if_pos hside, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one, true_and, abs_le] at hc ⊢
    omega

/-- Compute a head's direct scratch address by branching on its sign. -/
private def tmLocate (M : Turing.FinTM Bool) (j : Fin M.k) : Stmt :=
  .seq (.set (tmOldHead M.k j.val) (.var (tmHead j.val)))
    (.ite (.lt (.var (tmHead j.val)) (.const 0))
      (.set (tmAddress M.k j.val) (tmAddrExpr M.k j.val (tmCodeExpr (tmHead j.val) true)))
      (.set (tmAddress M.k j.val) (tmAddrExpr M.k j.val (tmCodeExpr (tmHead j.val) false))))

/-- Locating one tape freezes its head and records its direct scratch address, changing no
memory and no other locals.

**Proof sketch.** The first assignment freezes the work head. Its temporary local is distinct
from both the current head and scratch base. The guard therefore reads the original sign.
In either branch, `tmCodeExpr_read` computes the signed cell code and `tmAddrExpr_read`
computes the interleaved address; the two assignments give the displayed exact state. -/
private theorem tmLocate_runs (M : Turing.FinTM Bool) {lim : Limits} (σ : State)
    (j : Fin M.k) (sc : ℕ) (z : ℤ) (hsc : σ.loc 3 = (sc : ℤ))
    (hz : σ.loc (tmHead j.val) = z) (hw : (lim.space : ℤ) ≤ lim.word)
    (h2 : (2 : ℤ) ≤ lim.word) (hc : (tmCell z : ℤ) ≤ lim.word)
    (hk : (M.k : ℤ) ≤ lim.word) (hj : (j.val : ℤ) ≤ lim.word)
    (ha : sc + tmCell z * M.k + j.val ≤ lim.space) :
    (tmLocate M j).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update (Function.update σ.loc (tmOldHead M.k j.val) z) (tmAddress M.k j.val) (tmAddr sc M.k j z : ℤ) } := by
  unfold tmLocate
  apply Stmt.Runs.seq
  refine ⟨(Stmt.blockSafe_set_iff _ _ _ _).mpr ((Expr.safe_var_iff _ _ _).mpr trivial), ?_⟩
  rw [Stmt.after_set, Expr.val_var, hz]
  let σ₁ : State := { σ with loc := Function.update σ.loc (tmOldHead M.k j.val) z }
  have hs₁ : σ₁.loc 3 = (sc : ℤ) := by
    change Function.update σ.loc (tmOldHead M.k j.val) z 3 = (sc : ℤ)
    rw [Function.update_of_ne (by unfold tmOldHead; omega)]
    exact hsc
  have hz₁ : σ₁.loc (tmHead j.val) = z := by
    change Function.update σ.loc (tmOldHead M.k j.val) z (tmHead j.val) = z
    rw [Function.update_of_ne (by have := j.isLt; unfold tmHead tmOldHead; omega)]
    exact hz
  have hbranch (negative : Bool) (hside : if negative then z < 0 else 0 ≤ z) :
      (Stmt.set (tmAddress M.k j.val)
        (tmAddrExpr M.k j.val (tmCodeExpr (tmHead j.val) negative))).Runs lim σ₁ fun τ =>
          τ = { σ with loc := Function.update (Function.update σ.loc (tmOldHead M.k j.val) z) (tmAddress M.k j.val) (tmAddr sc M.k j z : ℤ) } := by
    obtain ⟨hcode, hval⟩ := tmCodeExpr_read negative hz₁ h2 hc hside
    obtain ⟨haddr, hvaladdr⟩ := tmAddrExpr_read _ hs₁ hcode hval hw hk hj ha
    simpa only [σ₁, tmAddr] using (tmSet_runs (dst := tmAddress M.k j.val) haddr hvaladdr)
  have hguard : (Cond.lt (.var (tmHead j.val)) (.const 0)).Holds σ₁ ↔ z < 0 := by
    rw [Cond.holds_lt_iff, Expr.val_var, Expr.val_const, hz₁, Nat.cast_zero]
  have hsafe : (Cond.lt (.var (tmHead j.val)) (.const 0)).Safe lim σ₁ := by
    rw [Cond.safe_lt_iff, Expr.safe_var_iff, Expr.safe_const_iff]
    exact ⟨trivial, by omega⟩
  by_cases hn : z < 0
  · exact Stmt.Runs.ite_pos (hbranch true hn) (hguard.mpr hn) hsafe
  · have hznonneg : 0 ≤ z := le_of_not_gt hn
    exact Stmt.Runs.ite_neg (hbranch false hznonneg) (fun hh => hn (hguard.mp hh)) hsafe

/-- Locating the whole work-head bank preserves the frame and memory and records every frozen
head and direct address.

**Proof sketch.** Apply `tmSeq_accumulate` to the static tape list. `tmLocate_runs` gives each
pair of local assignments. `tmFrame_tmp` preserves the stable frame through them, while
`tmLocal_ne` separates different banks and different tape indices. Thus every existing
frozen-head/address property survives and the visited tape's property is established. -/
private theorem tmLocateBank_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} {a b sc i : ℕ} (σ : State)
    (hf : TMFrame M c a b sc i σ) (hw : (lim.space : ℤ) ≤ lim.word)
    (h2 : (2 : ℤ) ≤ lim.word) (hk : (M.k : ℤ) ≤ lim.word)
    (hc : ∀ j : Fin M.k, (tmCell (c.workTapePos j) : ℤ) ≤ lim.word)
    (ha : ∀ j : Fin M.k, sc + tmCell (c.workTapePos j) * M.k + j.val ≤ lim.space) :
    (tmBank M (tmLocate M)).Runs lim σ fun τ =>
      TMFrame M c a b sc i τ ∧ τ.mem = σ.mem ∧ TMLocated M c sc τ := by
  let I : State → Prop := fun τ => TMFrame M c a b sc i τ ∧ τ.mem = σ.mem
  let F : Fin M.k → State → Prop := fun j τ =>
    τ.loc (tmOldHead M.k j.val) = c.workTapePos j ∧
      τ.loc (tmAddress M.k j.val) = (tmAddr sc M.k j (c.workTapePos j) : ℤ)
  have hr : ∀ j ∈ List.finRange M.k, ∀ τ, I τ → (tmLocate M j).Runs lim τ fun ν =>
      I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν := by
    rintro j _ τ ⟨hft, hmt⟩
    have hj : (j.val : ℤ) ≤ lim.word := by have := j.isLt; omega
    apply (tmLocate_runs M τ j sc (c.workTapePos j) hft.scratch (hft.heads j)
      hw h2 (hc j) hk hj (ha j)).mono
    rintro ν rfl
    let ν : State := { τ with loc := Function.update (Function.update τ.loc (tmOldHead M.k j.val) (c.workTapePos j)) (tmAddress M.k j.val) (tmAddr sc M.k j (c.workTapePos j) : ℤ) }
    change I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν
    have hf₁ := tmFrame_tmp (r := tmOldHead M.k j.val) (z := c.workTapePos j) hft
      (by unfold tmOldHead; omega) (Or.inr (by unfold tmOldHead; omega)) τ.mem
    have hf₂ := tmFrame_tmp (r := tmAddress M.k j.val)
      (z := (tmAddr sc M.k j (c.workTapePos j) : ℤ)) hf₁
      (by unfold tmAddress; omega) (Or.inr (by unfold tmAddress; omega)) τ.mem
    have hda : tmOldHead M.k j.val ≠ tmAddress M.k j.val := by
      simpa only [tmOldHead, tmAddress] using
        (tmLocal_ne (r := 3) (s := 2) (j := j) (l := j) (Or.inl (by decide)))
    have hfresh : F j ν := by
      simp only [F, ν, Function.update_self, Function.update_of_ne hda, true_and]
    refine ⟨⟨hf₂, hmt⟩, hfresh, ?_⟩
    intro l hl
    by_cases he : l = j
    · subst l
      exact hfresh
    · have hoo : tmOldHead M.k l.val ≠ tmOldHead M.k j.val := by
        simpa only [tmOldHead] using
          (tmLocal_ne (r := 3) (s := 3) (j := l) (l := j) (Or.inr he))
      have hoa : tmOldHead M.k l.val ≠ tmAddress M.k j.val := by
        simpa only [tmOldHead, tmAddress] using
          (tmLocal_ne (r := 3) (s := 2) (j := l) (l := j) (Or.inl (by decide)))
      have hao : tmAddress M.k l.val ≠ tmOldHead M.k j.val := by
        simpa only [tmOldHead, tmAddress] using
          (tmLocal_ne (r := 2) (s := 3) (j := l) (l := j) (Or.inl (by decide)))
      have haa : tmAddress M.k l.val ≠ tmAddress M.k j.val := by
        simpa only [tmAddress] using
          (tmLocal_ne (r := 2) (s := 2) (j := l) (l := j) (Or.inr he))
      dsimp only [F, ν] at hl ⊢
      simpa only [Function.update_of_ne hoo, Function.update_of_ne hoa,
        Function.update_of_ne hao, Function.update_of_ne haa] using hl
  have hbank := tmSeq_accumulate (I := I) (F := F) (rows := List.finRange M.k) ⟨hf, rfl⟩ hr
  apply hbank.mono
  rintro τ ⟨hI, hF, _⟩
  exact ⟨hI.1, hI.2, ⟨fun j => (hF j (List.mem_finRange j)).1,
    fun j => (hF j (List.mem_finRange j)).2⟩⟩

/-- Read the symbol at one previously computed work-tape address into its scan local. -/
private def tmReadTape (M : Turing.FinTM Bool) (j : Fin M.k) : Stmt :=
  .set (tmScan M.k j.val) (.load (.var (tmAddress M.k j.val)))

/-- Reading all work symbols preserves the frame, located data, input code, and memory.

**Proof sketch.** Use `tmSeq_accumulate` for the static tape list. Each load reads the address
from `TMLocated` and its value from the supplied memory encoding. `tmSet_runs` changes only the
corresponding scan local. `tmFrame_tmp`, `tmLocated_tmp`, and `tmLocal_ne` preserve the stable
and located data and all other established scan values. -/
private theorem tmScanBank_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} {a b sc i : ℕ} (σ : State)
    (hf : TMFrame M c a b sc i σ) (hl : TMLocated M c sc σ)
    (hi : σ.loc 9 = (tmSym c.inputSymbol : ℤ))
    (hread : ∀ j : Fin M.k, σ.mem (tmAddr sc M.k j (c.workTapePos j)) =
      (tmSym (c.workTapeSymbols j) : ℤ))
    (hrange : ∀ j : Fin M.k, tmAddr sc M.k j (c.workTapePos j) < lim.space) :
    (tmBank M (tmReadTape M)).Runs lim σ fun τ =>
      TMFrame M c a b sc i τ ∧ TMLocated M c sc τ ∧ TMScanned M c τ ∧ τ.mem = σ.mem := by
  let I : State → Prop := fun τ => TMFrame M c a b sc i τ ∧ TMLocated M c sc τ ∧
    τ.loc 9 = (tmSym c.inputSymbol : ℤ) ∧ τ.mem = σ.mem
  let F : Fin M.k → State → Prop := fun j τ =>
    τ.loc (tmScan M.k j.val) = (tmSym (c.workTapeSymbols j) : ℤ)
  have hr : ∀ j ∈ List.finRange M.k, ∀ τ, I τ → (tmReadTape M j).Runs lim τ fun ν =>
      I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν := by
    rintro j _ τ ⟨hft, hlt, hit, hmt⟩
    have hs : (Expr.load (.var (tmAddress M.k j.val))).Safe lim τ := by
      rw [Expr.safe_load_iff, Expr.safe_var_iff, Expr.val_var, hlt.addresses j, Limits.addr_iff]
      exact ⟨trivial, Int.natCast_nonneg _, by exact_mod_cast hrange j⟩
    have hv : (Expr.load (.var (tmAddress M.k j.val))).val τ =
        (tmSym (c.workTapeSymbols j) : ℤ) := by
      rw [Expr.val_load, Expr.val_var, hlt.addresses j, Int.toNat_natCast, hmt, hread j]
    apply (tmSet_runs (dst := tmScan M.k j.val) hs hv).mono
    rintro ν rfl
    let ν : State := { τ with loc := Function.update τ.loc (tmScan M.k j.val) (tmSym (c.workTapeSymbols j) : ℤ) }
    change I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν
    have hf' := tmFrame_tmp (r := tmScan M.k j.val)
      (z := (tmSym (c.workTapeSymbols j) : ℤ)) hft
      (by unfold tmScan; omega) (Or.inr (by unfold tmScan; omega)) τ.mem
    have hl' := tmLocated_tmp (r := tmScan M.k j.val)
      (z := (tmSym (c.workTapeSymbols j) : ℤ)) hlt
      (Or.inl (by have := j.isLt; unfold tmScan; omega)) τ.mem
    have hi' : ν.loc 9 = (tmSym c.inputSymbol : ℤ) := by
      change Function.update τ.loc (tmScan M.k j.val) (tmSym (c.workTapeSymbols j) : ℤ) 9 = _
      rw [Function.update_of_ne (by unfold tmScan; omega)]
      exact hit
    refine ⟨⟨hf', hl', hi', hmt⟩, ?_, ?_⟩
    · simp only [F, ν, Function.update_self]
    · intro l hlold
      by_cases he : l = j
      · subst l
        simp only [F, ν, Function.update_self]
      · have hne : tmScan M.k l.val ≠ tmScan M.k j.val := by
          simpa only [tmScan, Nat.one_mul] using
            (tmLocal_ne (r := 1) (s := 1) (j := l) (l := j) (Or.inr he))
        dsimp only [F, ν] at hlold ⊢
        simpa only [Function.update_of_ne hne] using hlold
  have hbank := tmSeq_accumulate (I := I) (F := F) (rows := List.finRange M.k)
    ⟨hf, hl, hi, rfl⟩ hr
  apply hbank.mono
  rintro τ ⟨⟨hft, hlt, hit, hmt⟩, hF, _⟩
  exact ⟨hft, hlt, ⟨hit, fun j => hF j (List.mem_finRange j)⟩, hmt⟩

/-- The zero-position test is safe and identifies exactly the left input end marker. -/
private theorem tmInputZeroTest {n : ℕ} {lim : Limits} {σ : State}
    (p : Fin (n + 2)) (hp : σ.loc 4 = (p.val : ℤ)) (h0 : (0 : ℤ) ≤ lim.word) :
    (Cond.eq (.var 4) (.const 0)).Safe lim σ ∧
      ((Cond.eq (.var 4) (.const 0)).Holds σ ↔ p = 0) := by
  constructor
  · rw [Cond.safe_eq_iff, Expr.safe_var_iff, Expr.safe_const_iff]
    exact ⟨trivial, h0⟩
  · rw [Cond.holds_eq_iff, Expr.val_var, Expr.val_const, hp, Nat.cast_zero]
    constructor
    · intro he
      exact Fin.val_eq_zero_iff.mp (by exact_mod_cast he)
    · intro he
      have hv := Fin.val_eq_zero_iff.mpr he
      exact_mod_cast hv

/-- The expression for the right input end marker is safe and has value `n + 1`. -/
private theorem tmInputEnd_read {n : ℕ} {lim : Limits} {σ : State}
    (hn : σ.loc 1 = (n : ℤ)) (hL : (n : ℤ) + 1 ≤ lim.word) :
    (Expr.op .add (.var 1) (.const 1)).Safe lim σ ∧
      (Expr.op .add (.var 1) (.const 1)).val σ = (n : ℤ) + 1 := by
  constructor
  · simp only [Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_var, Expr.val_const, Op.eval_add, hn, Nat.cast_one, true_and, abs_le]
    omega
  · rw [Expr.val_op, Op.eval_add, Expr.val_var, Expr.val_const, hn, Nat.cast_one]

/-- Read the input in place, encoding either end marker as blank. -/
private def tmReadInput : Stmt :=
  .ite (.eq (.var 4) (.const 0)) (.set 9 (.const 0))
    (.ite (.eq (.var 4) (.op .add (.var 1) (.const 1))) (.set 9 (.const 0))
      (.set 9 (.op .add
        (.load (.op .add (.var 0) (.op .sub (.var 4) (.const 1)))) (.const 1))))

/-- Reading the input changes only the scanned-input local, and returns the machine's actual
input symbol under the blank/bit encoding.

**Proof sketch.** The two end-marker branches use `Cfg.inputSymbol_of_zero` and
`Cfg.inputSymbol_of_end`. In the interior, `inputSymbolInner` identifies the bit at the
one-shifted head position. Its memory cell is inside the input region; loading its bit value
and adding one gives `tmSym_some_eq`. The word bounds control the address subtraction, address
addition, and final symbol code. -/
private theorem tmReadInput_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} (σ : State) (a : ℕ)
    (hsrc : σ.loc 0 = (a : ℤ)) (hlen : σ.loc 1 = (x.length : ℤ))
    (hpos : σ.loc 4 = (c.inputPos.val : ℤ))
    (hread : ∀ u < x.length, σ.mem (a + u) = ((x.getD u false).toNat : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2 : (2 : ℤ) ≤ lim.word) (hL : (x.length : ℤ) + 1 ≤ lim.word) :
    tmReadInput.Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc 9 (tmSym c.inputSymbol : ℤ) } := by
  have hblank : (Stmt.set 9 (.const 0)).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc 9 (0 : ℤ) } := by
    constructor
    · rw [Stmt.blockSafe_set_iff, Expr.safe_const_iff]
      omega
    · rw [Stmt.after_set, Expr.val_const, Nat.cast_zero]
  obtain ⟨hs0, hg0⟩ := tmInputZeroTest c.inputPos hpos (show (0 : ℤ) ≤ lim.word by omega)
  obtain ⟨hendsafe, hendval⟩ := tmInputEnd_read hlen hL
  have hgend : (Cond.eq (.var 4) (.op .add (.var 1) (.const 1))).Holds σ ↔
      c.inputPos.val = x.length + 1 := by
    rw [Cond.holds_eq_iff, Expr.val_var, hpos, hendval]
    constructor <;> intro he <;> exact_mod_cast he
  have hsend : (Cond.eq (.var 4) (.op .add (.var 1) (.const 1))).Safe lim σ :=
    (Cond.safe_eq_iff _ _ _ _).mpr ⟨(Expr.safe_var_iff _ _ _).mpr trivial, hendsafe⟩
  unfold tmReadInput
  by_cases hleft : c.inputPos = 0
  · apply Stmt.Runs.ite_pos ?_ (hg0.mpr hleft) hs0
    simpa only [Turing.Cfg.inputSymbol_of_zero hleft, tmSym, Nat.cast_zero] using hblank
  · apply Stmt.Runs.ite_neg ?_ (fun hh => hleft (hg0.mp hh)) hs0
    by_cases hend : c.inputPos.val = x.length + 1
    · apply Stmt.Runs.ite_pos ?_ (hgend.mpr hend) hsend
      simpa only [Turing.Cfg.inputSymbol_of_end hend, tmSym, Nat.cast_zero] using hblank
    · apply Stmt.Runs.ite_neg ?_ (fun hh => hend (hgend.mp hh)) hsend
      let u := c.inputPos.val - 1
      have hp0 : c.inputPos.val ≠ 0 := by
        intro he
        exact hleft (Fin.ext he)
      have hu : u < x.length := by
        have := c.inputPos.isLt
        dsimp only [u]
        omega
      have hpu : c.inputPos.val = 1 + u := by dsimp only [u]; omega
      have hsym : c.inputSymbol = some (x.getD u false) := by
        rw [Turing.inputSymbolInner u hpu hu, List.getD_eq_getElem _ _ hu]
      let ea : Expr := .op .add (.var 0) (.op .sub (.var 4) (.const 1))
      have hpuZ : (c.inputPos.val : ℤ) = 1 + (u : ℤ) := by exact_mod_cast hpu
      have haddrlt : a + u < lim.space := by omega
      have haddrZ : (a : ℤ) + (u : ℤ) < (lim.space : ℤ) := by exact_mod_cast haddrlt
      have hvaladdr : ea.val σ = ((a + u : ℕ) : ℤ) := by
        simp only [ea, Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add,
          Op.eval_sub, hsrc, hpos, Nat.cast_one, Nat.cast_add]
        omega
      have hsafeaddr : ea.Safe lim σ := by
        simp only [ea, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
          Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, Op.eval_sub,
          hsrc, hpos, Nat.cast_one, true_and, abs_le]
        omega
      have hloadval : (Expr.load ea).val σ = ((x.getD u false).toNat : ℤ) := by
        rw [Expr.val_load, hvaladdr, Int.toNat_natCast, hread u hu]
      have hloadsafe : (Expr.load ea).Safe lim σ := by
        rw [Expr.safe_load_iff, hvaladdr, Limits.addr_iff]
        exact ⟨hsafeaddr, Int.natCast_nonneg _, by exact_mod_cast haddrlt⟩
      let e : Expr := .op .add (.load ea) (.const 1)
      have hv : e.val σ = (tmSym c.inputSymbol : ℤ) := by
        simp only [e, Expr.val_op, Op.eval_add, hloadval, Expr.val_const, Nat.cast_one,
          hsym, tmSym_some_eq, Nat.cast_add]
      have hsafe : e.Safe lim σ := by
        simp only [e, Expr.safe_op_iff, hloadsafe, Expr.safe_const_iff, hloadval,
          Expr.val_const, Op.eval_add, Nat.cast_one, true_and, abs_le]
        have hbit := Bool.toNat_le (x.getD u false)
        omega
      exact tmSet_runs hsafe hv

/-- The read-only preparation of a transition: locate the work heads and read all symbols. -/
private def tmPrepare (M : Turing.FinTM Bool) : Stmt :=
  .seq (tmBank M (tmLocate M)) (.seq tmReadInput (tmBank M (tmReadTape M)))

/-- Transition preparation preserves memory and the stable frame and captures all addresses,
frozen heads, and scanned symbols.

**Proof sketch.** Compose `tmLocateBank_runs`, `tmReadInput_runs`, and `tmScanBank_runs`.
The input read changes only temporary local nine, which preserves both the frame and located
data by `tmFrame_tmp` and `tmLocated_tmp`. The two bank rules preserve memory, so the supplied
input and work-cell encodings remain valid throughout. -/
private theorem tmPrepare_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} {a b sc i : ℕ} (σ : State)
    (hf : TMFrame M c a b sc i σ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hin : a + x.length ≤ lim.space) (h2 : (2 : ℤ) ≤ lim.word)
    (hL : (x.length : ℤ) + 1 ≤ lim.word) (hk : (M.k : ℤ) ≤ lim.word)
    (hc : ∀ j : Fin M.k, (tmCell (c.workTapePos j) : ℤ) ≤ lim.word)
    (hinput : ∀ u < x.length, σ.mem (a + u) = ((x.getD u false).toNat : ℤ))
    (hwork : ∀ j : Fin M.k, σ.mem (tmAddr sc M.k j (c.workTapePos j)) =
      (tmSym (c.workTapeSymbols j) : ℤ))
    (hrange : ∀ j : Fin M.k, tmAddr sc M.k j (c.workTapePos j) < lim.space) :
    (tmPrepare M).Runs lim σ fun τ =>
      TMFrame M c a b sc i τ ∧ TMLocated M c sc τ ∧ TMScanned M c τ ∧ τ.mem = σ.mem := by
  unfold tmPrepare
  apply Stmt.Runs.seq
  apply (tmLocateBank_runs M c σ hf hw h2 hk hc
    (fun j => by simpa only [tmAddr] using (hrange j).le)).mono
  rintro τ ⟨hft, hmt, hlt⟩
  apply Stmt.Runs.seq
  have hinputτ : ∀ u < x.length, τ.mem (a + u) = ((x.getD u false).toNat : ℤ) := by
    intro u hu
    rw [hmt]
    exact hinput u hu
  apply (tmReadInput_runs M c τ a hft.src hft.len hft.inputPos hinputτ hw hin h2 hL).mono
  rintro ν rfl
  let ν : State := { τ with loc := Function.update τ.loc 9 (tmSym c.inputSymbol : ℤ) }
  have hf' := tmFrame_tmp (r := 9) (z := (tmSym c.inputSymbol : ℤ)) hft
    (by decide) (Or.inl (by decide)) τ.mem
  have hl' := tmLocated_tmp (r := 9) (z := (tmSym c.inputSymbol : ℤ)) hlt
    (Or.inl (by omega)) τ.mem
  have hi' : ν.loc 9 = (tmSym c.inputSymbol : ℤ) := by
    change Function.update τ.loc 9 (tmSym c.inputSymbol : ℤ) 9 = _
    exact Function.update_self ..
  have hworkν : ∀ j : Fin M.k, ν.mem (tmAddr sc M.k j (c.workTapePos j)) =
      (tmSym (c.workTapeSymbols j) : ℤ) := by
    intro j
    change τ.mem _ = _
    rw [hmt]
    exact hwork j
  apply (tmScanBank_runs M c ν hf' hl' hi' hworkν hrange).mono
  rintro ρ ⟨hfρ, hlρ, hsρ, hmρ⟩
  exact ⟨hfρ, hlρ, hsρ, hmρ.trans hmt⟩

/-- A fixed transition displacement applied to a frozen work-head local. -/
private def tmDisplace (src : ℕ) : SignType → Expr
  | .neg => .op .sub (.var src) (.const 1)
  | .zero => .var src
  | .pos => .op .add (.var src) (.const 1)

/-- A displacement expression is safe under its unit and result bounds and returns the
signed head position plus the transition displacement. -/
private theorem tmDisplace_read {lim : Limits} {σ : State} {src : ℕ} {z : ℤ} (m : SignType)
    (hz : σ.loc src = z) (h1 : (1 : ℤ) ≤ lim.word)
    (hm : |z + (m.cast : ℤ)| ≤ lim.word) :
    (tmDisplace src m).Safe lim σ ∧ (tmDisplace src m).val σ = z + (m.cast : ℤ) := by
  cases m <;>
    simp only [tmDisplace, Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_sub, Op.eval_add, hz,
      Nat.cast_one, SignType.neg_eq_neg_one, SignType.zero_eq_zero, SignType.pos_eq_one,
      SignType.coe_neg_one, SignType.coe_zero, SignType.coe_one, sub_eq_add_neg,
      add_zero, eq_self, true_and, and_true] at hm ⊢
  all_goals exact ⟨h1, hm⟩

/-- Move a work head from its frozen position. The frozen locals make all tape updates
independent, so the static bank implements simultaneous work-tape actions. -/
private def tmMoveWork (dst src : ℕ) (m : SignType) : Stmt :=
  .set dst (tmDisplace src m)

/-- A work-head update changes only its destination local and returns the prescribed signed
position; its expression safety is `tmDisplace_read`. -/
private theorem tmMoveWork_runs {lim : Limits} {σ : State} {dst src : ℕ} {z : ℤ}
    (m : SignType) (hz : σ.loc src = z) (h1 : (1 : ℤ) ≤ lim.word)
    (hm : |z + (m.cast : ℤ)| ≤ lim.word) :
    (tmMoveWork dst src m).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc dst (z + (m.cast : ℤ)) } := by
  obtain ⟨hs, hv⟩ := tmDisplace_read m hz h1 hm
  exact tmSet_runs hs hv

/-- Move the input head, clamping outward moves at the two end markers. -/
private def tmMoveInput : SignType → Stmt
  | .neg => .ite (.eq (.var 4) (.const 0)) .skip
      (.set 4 (.op .sub (.var 4) (.const 1)))
  | .zero => .skip
  | .pos => .ite (.lt (.var 4) (.op .add (.var 1) (.const 1)))
      (.set 4 (.op .add (.var 4) (.const 1))) .skip

/-- Input-head motion changes only its local and agrees with the machine's clamped movement.

**Proof sketch.** `tmInputZeroTest` handles the left boundary and `tmInputEnd_read` supplies
the right-boundary expression. A stationary or clamped move leaves the state unchanged.
The interior decrement and increment use `moveInputPos_neg_of_ne_left` and
`moveInputPos_pos_of_ne_right`, with the right-end bound controlling their arithmetic. -/
private theorem tmMoveInput_runs {n : ℕ} {lim : Limits} (σ : State) (p : Fin (n + 2))
    (m : SignType) (hp : σ.loc 4 = (p.val : ℤ)) (hn : σ.loc 1 = (n : ℤ))
    (hL : (n : ℤ) + 1 ≤ lim.word) :
    (tmMoveInput m).Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc 4 ((Turing.moveInputPos p m).val : ℤ) } := by
  have hskip (r : Fin (n + 2)) (he : r = p) : Stmt.skip.Runs lim σ fun τ =>
      τ = { σ with loc := Function.update σ.loc 4 (r.val : ℤ) } := by
    subst r
    constructor
    · exact (Stmt.blockSafe_skip_iff _ _).mpr trivial
    · rw [Stmt.after_skip, ← hp, Function.update_eq_self]
  cases m with
  | zero =>
    simpa only [tmMoveInput, SignType.zero_eq_zero, Turing.moveInputPos_zero] using hskip p rfl
  | neg =>
    obtain ⟨hs0, hg0⟩ := tmInputZeroTest p hp (show (0 : ℤ) ≤ lim.word by omega)
    unfold tmMoveInput
    by_cases hz : p = 0
    · have hm : Turing.moveInputPos p .neg = p := by
        rw [hz, SignType.neg_eq_neg_one, Turing.moveInputPos_leftBoundary]
      exact Stmt.Runs.ite_pos (hskip _ hm) (hg0.mpr hz) hs0
    · apply Stmt.Runs.ite_neg ?_ (fun hh => hz (hg0.mp hh)) hs0
      have hp0 : p.val ≠ 0 := fun hh => hz (Fin.val_eq_zero_iff.mp hh)
      have hplt := p.isLt
      constructor
      · simp only [Stmt.blockSafe_set_iff, Expr.safe_op_iff, Expr.safe_var_iff,
          Expr.safe_const_iff, Expr.val_var, Expr.val_const, Op.eval_sub,
          hp, Nat.cast_one, true_and, abs_le]
        omega
      · simp only [Stmt.after_set, Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_sub,
          hp, Nat.cast_one, Turing.moveInputPos_neg_of_ne_left p hz]
        have he : (p.val : ℤ) - 1 = ((p.val - 1 : ℕ) : ℤ) := by omega
        rw [he]
  | pos =>
    obtain ⟨hendsafe, hendval⟩ := tmInputEnd_read hn hL
    have hg : (Cond.lt (.var 4) (.op .add (.var 1) (.const 1))).Holds σ ↔
        p.val < n + 1 := by
      rw [Cond.holds_lt_iff, Expr.val_var, hp, hendval]
      constructor <;> intro he <;> exact_mod_cast he
    have hs : (Cond.lt (.var 4) (.op .add (.var 1) (.const 1))).Safe lim σ :=
      (Cond.safe_lt_iff _ _ _ _).mpr ⟨(Expr.safe_var_iff _ _ _).mpr trivial, hendsafe⟩
    have hplt := p.isLt
    unfold tmMoveInput
    by_cases hi : p.val < n + 1
    · apply Stmt.Runs.ite_pos ?_ (hg.mpr hi) hs
      have hne : p.val ≠ n + 1 := by omega
      constructor
      · simp only [Stmt.blockSafe_set_iff, Expr.safe_op_iff, Expr.safe_var_iff,
          Expr.safe_const_iff, Expr.val_var, Expr.val_const, Op.eval_add,
          hp, Nat.cast_one, true_and, abs_le]
        omega
      · simp only [Stmt.after_set, Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add,
          hp, Turing.moveInputPos_pos_of_ne_right p hne, Nat.cast_add, Nat.cast_one]
    · have he : p = (⟨n + 1, by omega⟩ : Fin (n + 2)) :=
        Fin.ext (show p.val = n + 1 from by omega)
      have hm : Turing.moveInputPos p .pos = p := by
        rw [he, SignType.pos_eq_one, Turing.moveInputPos_rightBoundary]
      exact Stmt.Runs.ite_neg (hskip _ hm) (fun hh => hi (hg.mp hh)) hs

/-- One tape's transition writes the chosen symbol, or writes back the scanned symbol when
there is no write, then moves the head. -/
private def tmWriteMove (M : Turing.FinTM Bool) (action : Turing.Action M.k Bool M.State)
    (j : Fin M.k) : Stmt :=
  .seq (.store (.var (tmAddress M.k j.val))
    (match (action.workTapes j).1 with
      | none => .var (tmScan M.k j.val)
      | some sym => .const (tmSym sym)))
    (tmMoveWork (tmHead j.val) (tmOldHead M.k j.val) (action.workTapes j).2)

/-- One tape's write and head movement have the normalized optional-write effect used by
`Action.apply_workTapes` and change only that tape cell and head local.

**Proof sketch.** Choose the stored symbol from the optional write, defaulting to the captured
scanned symbol. Its expression is either a scan local or a bounded symbol constant.
`tmStore_runs` writes it to the frozen address. The store preserves locals, so
`tmMoveWork_runs` then reads the frozen head and establishes the prescribed displacement. -/
private theorem tmWriteMove_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    {lim : Limits} (σ : State) (sc : ℕ) (j : Fin M.k)
    (hl : TMLocated M c sc σ) (hs : TMScanned M c σ) (h2 : (2 : ℤ) ≤ lim.word)
    (hm : |c.workTapePos j + ((action.workTapes j).2.cast : ℤ)| ≤ lim.word)
    (ha : tmAddr sc M.k j (c.workTapePos j) < lim.space) :
    (tmWriteMove M action j).Runs lim σ fun τ =>
      τ = ⟨Function.update σ.loc (tmHead j.val) (c.workTapePos j + ((action.workTapes j).2.cast : ℤ)),
        Function.update σ.mem (tmAddr sc M.k j (c.workTapePos j))
          (tmSym ((action.workTapes j).1.getD (c.workTapeSymbols j)) : ℤ)⟩ := by
  let e : Expr := match (action.workTapes j).1 with
    | none => .var (tmScan M.k j.val)
    | some sym => .const (tmSym sym)
  let w := (action.workTapes j).1.getD (c.workTapeSymbols j)
  have he : e.Safe lim σ ∧ e.val σ = (tmSym w : ℤ) := by
    cases hwrite : (action.workTapes j).1 with
    | none =>
      simp only [e, w, hwrite, Option.getD_none]
      exact ⟨(Expr.safe_var_iff _ _ _).mpr trivial,
        (Expr.val_var _ _).trans (hs.work j)⟩
    | some sym =>
      simp only [e, w, hwrite, Option.getD_some]
      refine ⟨(Expr.safe_const_iff _ _ _).mpr ?_, Expr.val_const _ _⟩
      have hsym := tmSym_le_two sym
      omega
  have haddr : (Expr.var (tmAddress M.k j.val)).val σ =
      (tmAddr sc M.k j (c.workTapePos j) : ℤ) :=
    (Expr.val_var _ _).trans (hl.addresses j)
  unfold tmWriteMove
  apply Stmt.Runs.seq
  apply (tmStore_runs ((Expr.safe_var_iff _ _ _).mpr trivial) he.1 haddr he.2 ha).mono
  rintro τ rfl
  let σ₁ : State := { σ with mem := Function.update σ.mem (tmAddr sc M.k j (c.workTapePos j)) (tmSym w : ℤ) }
  have hh : σ₁.loc (tmOldHead M.k j.val) = c.workTapePos j := hl.oldHeads j
  simpa only [σ₁, w] using
    (tmMoveWork_runs (dst := tmHead j.val) (src := tmOldHead M.k j.val)
      (action.workTapes j).2 hh (show (1 : ℤ) ≤ lim.word by omega) hm)

/-- The complete tape-action bank preserves the eight scalar locals and old output, updates
all heads and represented tape cells as the action prescribes, and keeps the external memory.

**Proof sketch.** `tmSeq_accumulate` visits the tape bank. Its invariant keeps the scalar,
located, and scanned locals, all tape cells away from old heads, the output segment, and the
external-memory promise. `tmWriteMove_runs` gives each exact store/head update. The store
preserves away cells by `tmTapesAway_write`, output by `Seg.update_out`, and external memory by
`SameOutside2.update`. For the visited tape, `Action.apply_workTapes` and
`Action.apply_workTapePos` identify the full new tape and head. `tmAddr_injective` and
`tmLocal_ne` preserve the properties already established for different tapes. -/
private theorem tmWriteBank_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    {lim : Limits} {b sc radius outLen scratchLen : ℕ} (σ : State) (μ₀ : ℕ → ℤ)
    (hl : TMLocated M c sc σ) (hs : TMScanned M c σ)
    (ht : TMTapes M c sc radius σ.mem) (hout : Seg σ.mem b (tmBits c.output))
    (hkeep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen) (h2 : (2 : ℤ) ≤ lim.word)
    (hm : ∀ j : Fin M.k, |c.workTapePos j + ((action.workTapes j).2.cast : ℤ)| ≤ lim.word)
    (hrange : ∀ j : Fin M.k, tmAddr sc M.k j (c.workTapePos j) < lim.space)
    (hinside : ∀ j : Fin M.k, Inside sc scratchLen (tmAddr sc M.k j (c.workTapePos j)))
    (houtside : ∀ j : Fin M.k, Outside b c.output.length (tmAddr sc M.k j (c.workTapePos j))) :
    (tmBank M (tmWriteMove M action)).Runs lim σ fun τ =>
      (∀ v < 8, τ.loc v = σ.loc v) ∧
      (∀ j : Fin M.k, τ.loc (tmHead j.val) = (action.apply c).workTapePos j) ∧
      TMTapes M (action.apply c) sc radius τ.mem ∧ Seg τ.mem b (tmBits c.output) ∧
      SameOutside2 μ₀ τ.mem b outLen sc scratchLen := by
  let I : State → Prop := fun τ => (∀ v < 8, τ.loc v = σ.loc v) ∧
    TMLocated M c sc τ ∧ TMScanned M c τ ∧ TMTapesAway M c sc radius τ.mem ∧
    Seg τ.mem b (tmBits c.output) ∧ SameOutside2 μ₀ τ.mem b outLen sc scratchLen
  let F : Fin M.k → State → Prop := fun j τ =>
    τ.loc (tmHead j.val) = (action.apply c).workTapePos j ∧
    ∀ z : ℤ, |z| < (radius : ℤ) →
      τ.mem (tmAddr sc M.k j z) = (tmSym ((action.apply c).workTapes j z) : ℤ)
  have hr : ∀ j ∈ List.finRange M.k, ∀ τ, I τ → (tmWriteMove M action j).Runs lim τ fun ν =>
      I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν := by
    rintro j _ τ ⟨hscalar, hlt, hst, haway, houtτ, hkeepτ⟩
    apply (tmWriteMove_runs M c action τ sc j hlt hst h2 (hm j) (hrange j)).mono
    rintro ν rfl
    let addr := tmAddr sc M.k j (c.workTapePos j)
    let value : ℤ := tmSym ((action.workTapes j).1.getD (c.workTapeSymbols j))
    let pos : ℤ := c.workTapePos j + ((action.workTapes j).2.cast : ℤ)
    let ν : State := ⟨Function.update τ.loc (tmHead j.val) pos, Function.update τ.mem addr value⟩
    change I ν ∧ F j ν ∧ ∀ l, F l τ → F l ν
    have hscalar' : ∀ v < 8, ν.loc v = σ.loc v := by
      intro v hv
      change Function.update τ.loc (tmHead j.val) pos v = _
      rw [Function.update_of_ne (by unfold tmHead; omega)]
      exact hscalar v hv
    have hl' := tmLocated_tmp (r := tmHead j.val) (z := pos) hlt
      (Or.inl (by have := j.isLt; unfold tmHead; omega)) (Function.update τ.mem addr value)
    have hs' := tmScanned_tmp (r := tmHead j.val) (z := pos) hst
      (by unfold tmHead; omega) (Or.inl (by have := j.isLt; unfold tmHead; omega))
      (Function.update τ.mem addr value)
    have haway' := tmTapesAway_write j haway value
    have hout' := Seg.update_out houtτ
      (show addr < b ∨ b + (tmBits c.output).length ≤ addr from by
        simpa only [tmBits, List.length_map] using houtside j) value
    have hkeep' := SameOutside2.update hkeepτ (Or.inr (hinside j)) value
    have hI : I ν := ⟨hscalar', hl', hs', haway', hout', hkeep'⟩
    have hfresh : F j ν := by
      constructor
      · change Function.update τ.loc (tmHead j.val) pos (tmHead j.val) = _
        rw [Function.update_self, Turing.Action.apply_workTapePos]
      · intro z hz
        rw [Turing.Action.apply_workTapes]
        by_cases he : z = c.workTapePos j
        · subst z
          change Function.update τ.mem addr value addr =
            (tmSym (Function.update (c.workTapes j) (c.workTapePos j)
              ((action.workTapes j).1.getD (c.workTapeSymbols j)) (c.workTapePos j)) : ℤ)
          rw [Function.update_self, Function.update_self]
        · have haddr : tmAddr sc M.k j z ≠ addr := by
            intro heq
            exact he (tmAddr_injective heq).2
          change Function.update τ.mem addr value (tmAddr sc M.k j z) =
            (tmSym (Function.update (c.workTapes j) (c.workTapePos j)
              ((action.workTapes j).1.getD (c.workTapeSymbols j)) z) : ℤ)
          rw [Function.update_of_ne haddr, Function.update_of_ne he]
          exact haway j z hz he
    refine ⟨hI, hfresh, ?_⟩
    intro l hlold
    by_cases he : l = j
    · subst l
      exact hfresh
    · constructor
      · have hhead : tmHead l.val ≠ tmHead j.val := by
          simpa only [tmHead, Nat.zero_mul, Nat.add_zero] using
            (tmLocal_ne (r := 0) (s := 0) (j := l) (l := j) (Or.inr he))
        change Function.update τ.loc (tmHead j.val) pos (tmHead l.val) = _
        rw [Function.update_of_ne hhead]
        exact hlold.1
      · intro z hz
        have haddr : tmAddr sc M.k l z ≠ addr := by
          intro heq
          exact he (tmAddr_injective heq).1
        change Function.update τ.mem addr value (tmAddr sc M.k l z) = _
        rw [Function.update_of_ne haddr]
        exact hlold.2 z hz
  have hI : I σ := ⟨fun _ _ => rfl, hl, hs, fun j z hz _ => ht j z hz, hout, hkeep⟩
  have hbank := tmSeq_accumulate (I := I) (F := F) (rows := List.finRange M.k) hI hr
  apply hbank.mono
  rintro τ ⟨⟨hscalar, _, _, _, houtτ, hkeepτ⟩, hF, _⟩
  refine ⟨hscalar, fun j => (hF j (List.mem_finRange j)).1, ?_, houtτ, hkeepτ⟩
  intro j z hz
  exact (hF j (List.mem_finRange j)).2 z hz

/-- Append the optional output bit and advance the output length. -/
private def tmEmit : Option Bool → Stmt
  | none => .skip
  | some bit => .seq (.store (.op .add (.var 2) (.var 6)) (.const bit.toNat))
      (.set 6 (.op .add (.var 6) (.const 1)))

/-- The exact state after an optional output emission. -/
private def tmEmitState (σ : State) (b o : ℕ) : Option Bool → State
  | none => σ
  | some bit => ⟨Function.update σ.loc 6 ((o + 1 : ℕ) : ℤ),
      Function.update σ.mem (b + o) (bit.toNat : ℤ)⟩

/-- The output cursor is the only local changed by emission, with absent emission leaving
its existing value unchanged. -/
private theorem tmEmitState_locals (σ : State) (b o : ℕ) (v : Option Bool)
    (ho : σ.loc 6 = (o : ℤ)) :
    (tmEmitState σ b o v).loc = Function.update σ.loc 6 ((o + v.toList.length : ℕ) : ℤ) := by
  cases v with
  | none =>
    simp only [tmEmitState, Option.toList_none, List.length_nil, Nat.add_zero]
    rw [← ho, Function.update_eq_self]
  | some bit =>
    simp only [tmEmitState, Option.toList_some, List.length_singleton]

/-- Emission extends the output segment and keeps represented work tapes and external memory
when the final output region is apart from scratch.

**Proof sketch.** No emission changes no memory. For a bit, its cursor lies inside the final
output region. Every represented work cell lies in scratch, so `Apart` separates it from that
cursor and `Function.update_of_ne` preserves its encoding. `Seg.snoc` extends the bit segment,
and `SameOutside2.update` preserves memory outside the two allowed regions. -/
private theorem tmEmitState_data (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (σ : State) (bits : List Bool)
    (b sc radius outLen scratchLen : ℕ) (v : Option Bool) (μ₀ : ℕ → ℤ)
    (ht : TMTapes M c sc radius σ.mem) (hout : Seg σ.mem b (tmBits bits))
    (hkeep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen)
    (hbound : bits.length + v.toList.length ≤ outLen) (hsep : Apart b outLen sc scratchLen)
    (hinside : ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) →
      Inside sc scratchLen (tmAddr sc M.k j z)) :
    TMTapes M c sc radius (tmEmitState σ b bits.length v).mem ∧
      Seg (tmEmitState σ b bits.length v).mem b (tmBits (bits ++ v.toList)) ∧
      SameOutside2 μ₀ (tmEmitState σ b bits.length v).mem b outLen sc scratchLen := by
  cases v with
  | none =>
    simpa only [tmEmitState, Option.toList_none, List.append_nil] using ⟨ht, hout, hkeep⟩
  | some bit =>
    have hb : bits.length + 1 ≤ outLen := by
      simpa only [Option.toList_some, List.length_singleton] using hbound
    refine ⟨?_, ?_, ?_⟩
    · intro j z hz
      have hcell := hinside j z hz
      have hne : tmAddr sc M.k j z ≠ b + bits.length := by
        rcases hcell with ⟨hlo, hhi⟩
        rcases hsep with hsep | hsep <;> omega
      change Function.update σ.mem (b + bits.length) (bit.toNat : ℤ) (tmAddr sc M.k j z) = _
      rw [Function.update_of_ne hne]
      exact ht j z hz
    · simpa only [tmEmitState, tmBits, List.length_map, Option.toList_some,
        List.map_append, List.map_cons, List.map_nil] using hout.snoc (bit.toNat : ℤ)
    · exact SameOutside2.update hkeep
        (Or.inl ⟨by omega, by omega⟩) (bit.toNat : ℤ)

/-- Output emission appends the optional bit at the output cursor, advances its length,
and leaves every other local and memory cell unchanged.

**Proof sketch.** The absent-bit branch is `skip`. In the present-bit branch, `tmStore_runs`
writes the bounded bit at the in-range output cursor. Its exact state keeps the length local
unchanged, so `tmSet_runs` increments that local safely. The two exact updates are
`tmEmitState`. -/
private theorem tmEmit_runs {lim : Limits} (σ : State) (b o : ℕ) (v : Option Bool)
    (hb : σ.loc 2 = (b : ℤ)) (ho : σ.loc 6 = (o : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hs : b + o + v.toList.length ≤ lim.space) :
    (tmEmit v).Runs lim σ fun τ => τ = tmEmitState σ b o v := by
  cases v with
  | none =>
    exact ⟨(Stmt.blockSafe_skip_iff _ _).mpr trivial, Stmt.after_skip _⟩
  | some bit =>
    have hs1 : b + o + 1 ≤ lim.space := by
      simpa only [Option.toList_some, List.length_singleton] using hs
    have hsZ : (b : ℤ) + (o : ℤ) + 1 ≤ (lim.space : ℤ) := by exact_mod_cast hs1
    have haddrlt : b + o < lim.space := by omega
    let ea : Expr := .op .add (.var 2) (.var 6)
    have hvaladdr : ea.val σ = ((b + o : ℕ) : ℤ) := by
      simp only [ea, Expr.val_op, Expr.val_var, Op.eval_add, hb, ho, Nat.cast_add]
    have hsafeaddr : ea.Safe lim σ := by
      simp only [ea, Expr.safe_op_iff, Expr.safe_var_iff, Expr.val_var, Op.eval_add,
        hb, ho, true_and, abs_le]
      omega
    have hbit := Bool.toNat_le bit
    have hsafebit : (Expr.const bit.toNat).Safe lim σ :=
      (Expr.safe_const_iff _ _ _).mpr (by omega)
    unfold tmEmit
    apply Stmt.Runs.seq
    apply (tmStore_runs hsafeaddr hsafebit hvaladdr (Expr.val_const _ _) haddrlt).mono
    rintro τ rfl
    let σ₁ : State := { σ with mem := Function.update σ.mem (b + o) (bit.toNat : ℤ) }
    have ho₁ : σ₁.loc 6 = (o : ℤ) := ho
    have hsafe : (Expr.op .add (.var 6) (.const 1)).Safe lim σ₁ := by
      simp only [Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff, Expr.val_var,
        Expr.val_const, Op.eval_add, ho₁, Nat.cast_one, true_and, abs_le]
      omega
    have hv : (Expr.op .add (.var 6) (.const 1)).val σ₁ = ((o + 1 : ℕ) : ℤ) := by
      simp only [Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, ho₁,
        Nat.cast_add, Nat.cast_one]
    simpa only [tmEmitState, σ₁] using (tmSet_runs (dst := 6) hsafe hv)

/-- Finish a transition after the work-tape bank: move the input head, emit output, and
install the next control state, as an exact-state description. -/
private noncomputable def tmFinishState (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    (b : ℕ) (σ : State) : State :=
  let moved : State := { σ with loc := Function.update σ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) }
  let emitted := tmEmitState moved b c.output.length action.output
  { emitted with loc := Function.update emitted.loc 5 (tmStateCode M action.state : ℤ) }

/-- Finishing the scalar updates after a correct tape bank gives the complete next frame.

**Proof sketch.** `tmEmitState_locals` expresses both output cases by one cursor update.
The resulting locals are three updates of the bank's locals, at input position four, output
length six, and control state five. The other scalar locals and every head are preserved.
The published field equations `Action.apply_inputPos`, `apply_output`, and `apply_state`
identify the three new frame fields. -/
private theorem tmFinishState_frame (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    {a b sc i : ℕ} (σ ρ : State) (hf : TMFrame M c a b sc i σ)
    (he : ∀ v < 8, ρ.loc v = σ.loc v)
    (hh : ∀ j : Fin M.k, ρ.loc (tmHead j.val) = (action.apply c).workTapePos j) :
    TMFrame M (action.apply c) a b sc i (tmFinishState M c action b ρ) := by
  let moved : State := { ρ with loc := Function.update ρ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) }
  have ho : moved.loc 6 = (c.output.length : ℤ) := by
    change Function.update ρ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) 6 = _
    rw [Function.update_of_ne (by decide : (6 : ℕ) ≠ 4)]
    exact (he 6 (by decide)).trans hf.outputLen
  have hl : (tmFinishState M c action b ρ).loc =
      Function.update (Function.update (Function.update ρ.loc 4
        ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ)) 6
          ((c.output.length + action.output.toList.length : ℕ) : ℤ)) 5
            (tmStateCode M action.state : ℤ) := by
    change Function.update (tmEmitState moved b c.output.length action.output).loc 5
      (tmStateCode M action.state : ℤ) = _
    rw [tmEmitState_locals moved b c.output.length action.output ho]
  have hsame (v : ℕ) (hne : v ≠ 4 ∧ v ≠ 5 ∧ v ≠ 6) :
      (tmFinishState M c action b ρ).loc v = ρ.loc v := by
    rw [hl, Function.update_of_ne hne.2.1, Function.update_of_ne hne.2.2,
      Function.update_of_ne hne.1]
  have hscalar (v : ℕ) (hv : v < 4 ∨ v = 7) :
      (tmFinishState M c action b ρ).loc v = σ.loc v :=
    (hsame v (by omega)).trans (he v (by omega))
  constructor
  · exact (hscalar 0 (by decide)).trans hf.src
  · exact (hscalar 1 (by decide)).trans hf.len
  · exact (hscalar 2 (by decide)).trans hf.dst
  · exact (hscalar 3 (by decide)).trans hf.scratch
  · rw [hl, Function.update_of_ne (by decide : (4 : ℕ) ≠ 5),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), Function.update_self,
      Turing.Action.apply_inputPos]
  · rw [hl, Function.update_self, Turing.Action.apply_state]
  · rw [hl, Function.update_of_ne (by decide : (6 : ℕ) ≠ 5), Function.update_self,
      Turing.Action.apply_output, List.length_append]
  · exact (hscalar 7 (by decide)).trans hf.round
  · intro j
    exact (hsame (tmHead j.val) (by unfold tmHead; omega)).trans (hh j)

/-- The executable block for one fixed action. -/
private noncomputable def tmActionBody (M : Turing.FinTM Bool)
    (action : Turing.Action M.k Bool M.State) : Stmt :=
  .seq (tmBank M (tmWriteMove M action)) (.seq (tmMoveInput action.inputTape)
    (.seq (tmEmit action.output) (.set 5 (.const (tmStateCode M action.state)))))

/-- A fixed transition action updates the complete configuration representation, output, and
external-memory promise within the supplied word and region bounds.

**Proof sketch.** Run `tmWriteBank_runs`, then the verified input motion and emission blocks.
The tape bank preserves all scalar arguments needed by those two blocks. `tmEmitState_data`
preserves the new work tapes, appends output, and keeps external memory. Assign the bounded
next-state code; `tmFinishState_frame` identifies the resulting complete frame. -/
private theorem tmActionBody_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (action : Turing.Action M.k Bool M.State)
    {lim : Limits} {a b sc i radius outLen scratchLen : ℕ} (σ : State) (μ₀ : ℕ → ℤ)
    (hf : TMFrame M c a b sc i σ) (hl : TMLocated M c sc σ) (hs : TMScanned M c σ)
    (ht : TMTapes M c sc radius σ.mem) (hout : Seg σ.mem b (tmBits c.output))
    (hkeep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen)
    (hw : (lim.space : ℤ) ≤ lim.word) (h2 : (2 : ℤ) ≤ lim.word)
    (hL : (x.length : ℤ) + 1 ≤ lim.word) (hc : (tmStateCode M action.state : ℤ) ≤ lim.word)
    (hm : ∀ j : Fin M.k, |c.workTapePos j + ((action.workTapes j).2.cast : ℤ)| ≤ lim.word)
    (hhead : ∀ j : Fin M.k, |c.workTapePos j| < (radius : ℤ))
    (hinside : ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) →
      Inside sc scratchLen (tmAddr sc M.k j z))
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + outLen ≤ lim.space)
    (hsep : Apart b outLen sc scratchLen)
    (hprefix : c.output.length + action.output.toList.length ≤ outLen) :
    (tmActionBody M action).Runs lim σ fun τ =>
      TMFrame M (action.apply c) a b sc i τ ∧ TMTapes M (action.apply c) sc radius τ.mem ∧
      Seg τ.mem b (tmBits (action.apply c).output) ∧
      SameOutside2 μ₀ τ.mem b outLen sc scratchLen := by
  have hinsideHead (j : Fin M.k) := hinside j (c.workTapePos j) (hhead j)
  have hrange (j : Fin M.k) : tmAddr sc M.k j (c.workTapePos j) < lim.space := by
    have hcell := hinsideHead j
    omega
  have houtside (j : Fin M.k) : Outside b c.output.length (tmAddr sc M.k j (c.workTapePos j)) := by
    have hcell := hinsideHead j
    rcases hsep with hsep | hsep <;> omega
  unfold tmActionBody
  apply Stmt.Runs.seq
  apply (tmWriteBank_runs M c action σ μ₀ hl hs ht hout hkeep h2 hm hrange
    hinsideHead houtside).mono
  rintro ρ ⟨hscalar, hheads, htρ, houtρ, hkeepρ⟩
  apply Stmt.Runs.seq
  have hpρ : ρ.loc 4 = (c.inputPos.val : ℤ) := (hscalar 4 (by decide)).trans hf.inputPos
  have hnρ : ρ.loc 1 = (x.length : ℤ) := (hscalar 1 (by decide)).trans hf.len
  apply (tmMoveInput_runs ρ c.inputPos action.inputTape hpρ hnρ hL).mono
  rintro σ₁ rfl
  let σ₁ : State := { ρ with loc := Function.update ρ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) }
  have hmoved (v : ℕ) (hv : v < 8) (hne : v ≠ 4) : σ₁.loc v = σ.loc v := by
    change Function.update ρ.loc 4 ((Turing.moveInputPos c.inputPos action.inputTape).val : ℤ) v = _
    rw [Function.update_of_ne hne]
    exact hscalar v hv
  have hb₁ : σ₁.loc 2 = (b : ℤ) := (hmoved 2 (by decide) (by decide)).trans hf.dst
  have ho₁ : σ₁.loc 6 = (c.output.length : ℤ) :=
    (hmoved 6 (by decide) (by decide)).trans hf.outputLen
  apply Stmt.Runs.seq
  apply (tmEmit_runs σ₁ b c.output.length action.output hb₁ ho₁ hw
    (show (1 : ℤ) ≤ lim.word by omega) (show b + c.output.length + action.output.toList.length ≤ lim.space by omega)).mono
  rintro σ₂ rfl
  let σ₂ := tmEmitState σ₁ b c.output.length action.output
  have hdata := tmEmitState_data M (action.apply c) σ₁ c.output b sc radius outLen scratchLen
    action.output μ₀ htρ houtρ hkeepρ hprefix hsep hinside
  have hsafe : (Expr.const (tmStateCode M action.state)).Safe lim σ₂ :=
    (Expr.safe_const_iff _ _ _).mpr hc
  apply (tmSet_runs (dst := 5) hsafe (Expr.val_const _ _)).mono
  rintro σ₃ rfl
  refine ⟨tmFinishState_frame M c action σ ρ hf hscalar hheads, hdata.1, ?_, hdata.2.2⟩
  rw [Turing.Action.apply_output]
  exact hdata.2.1

/-- The block implementing one fixed row of the machine's transition function. -/
private noncomputable def tmRowBody (M : Turing.FinTM Bool) (row : TMRow M) : Stmt :=
  tmActionBody M (M.tm.tr row.1 row.2.1 row.2.2)

/-- The local-value tests identifying a transition row. -/
private noncomputable def tmRowTests (M : Turing.FinTM Bool) (row : TMRow M) : List (ℕ × ℕ) :=
  (5, tmStateCode M (some row.1)) :: (9, tmSym row.2.1) ::
    (List.finRange M.k).map (fun j => (tmScan M.k j.val, tmSym (row.2.2 j)))

/-- Reading a row's tests gives exactly its control state and scanned symbols. -/
private theorem tmRowTests_matches_iff (M : Turing.FinTM Bool) (row : TMRow M) (σ : State) :
    tmMatches (tmRowTests M row) σ ↔
      σ.loc 5 = (tmStateCode M (some row.1) : ℤ) ∧
      σ.loc 9 = (tmSym row.2.1 : ℤ) ∧
      ∀ j : Fin M.k, σ.loc (tmScan M.k j.val) = (tmSym (row.2.2 j) : ℤ) := by
  simp only [tmMatches, tmRowTests, List.forall_mem_cons, List.forall_mem_map,
    List.mem_finRange, forall_true_left]

/-- If the scanned locals encode `actual`, a row's tests succeed exactly for that row. -/
private theorem tmRowTests_unique (M : Turing.FinTM Bool) (actual row : TMRow M) (σ : State)
    (ha : tmMatches (tmRowTests M actual) σ) :
    tmMatches (tmRowTests M row) σ ↔ row = actual := by
  constructor
  · intro hr
    obtain ⟨haq, hai, haw⟩ := (tmRowTests_matches_iff M actual σ).mp ha
    obtain ⟨hrq, hri, hrw⟩ := (tmRowTests_matches_iff M row σ).mp hr
    have hq : some row.1 = some actual.1 :=
      tmStateCode_injective M (by exact_mod_cast hrq.symm.trans haq)
    have hi : row.2.1 = actual.2.1 :=
      tmSym_injective (by exact_mod_cast hri.symm.trans hai)
    have hw : row.2.2 = actual.2.2 := by
      funext j
      exact tmSym_injective (by exact_mod_cast (hrw j).symm.trans (haw j))
    exact Prod.ext (Option.some.inj hq) (Prod.ext hi hw)
  · intro he
    subst row
    exact ha

/-- The block after scratch initialization: read the old configuration, execute its
transition row, and advance the round count. -/
private noncomputable def tmTail (M : Turing.FinTM Bool) : Stmt :=
  .seq (tmPrepare M) (.seq (tmDispatch (tmRowTests M) (tmRowBody M) (tmRows M))
    (.set 7 (.op .add (.var 7) (.const 1))))

/-- The transition selected by a live configuration. -/
private def tmAction (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (q : M.State) : Turing.Action M.k Bool M.State :=
  M.tm.tr q c.inputSymbol c.workTapeSymbols

/-- Reading a live configuration, selecting its row, and advancing the counter simulates
exactly one machine step under the given word and region bounds.

**Proof sketch.** `tmPrepare_runs` freezes the old heads and reads the scanned symbols without
changing memory. The row for the live state and those symbols belongs to `tmRows`, and
`tmRowTests_unique` excludes every other row. Apply `tmDispatch_runs` with
`tmActionBody_runs` as its selected-row rule. The last assignment advances only the round
counter, so `tmFrame_round` gives the next complete frame. -/
private theorem tmTail_runs (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) (q : M.State) (hq : c.state = some q)
    {lim : Limits} {a b sc i radius outLen scratchLen : ℕ} (σ : State) (μ₀ : ℕ → ℤ)
    (hf : TMFrame M c a b sc i σ) (ht : TMTapes M c sc radius σ.mem)
    (hout : Seg σ.mem b (tmBits c.output)) (hkeep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen)
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2 : (2 : ℤ) ≤ lim.word) (hL : (x.length : ℤ) + 1 ≤ lim.word)
    (hk : (M.k : ℤ) ≤ lim.word) (hi : (i : ℤ) + 1 ≤ lim.word)
    (hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word)
    (hc : ∀ j : Fin M.k, (tmCell (c.workTapePos j) : ℤ) ≤ lim.word)
    (hinput : ∀ u < x.length, σ.mem (a + u) = ((x.getD u false).toNat : ℤ))
    (hm : ∀ j : Fin M.k,
      |c.workTapePos j + (((tmAction M c q).workTapes j).2.cast : ℤ)| ≤ lim.word)
    (hhead : ∀ j : Fin M.k, |c.workTapePos j| < (radius : ℤ))
    (hinside : ∀ (j : Fin M.k) (z : ℤ), |z| < (radius : ℤ) →
      Inside sc scratchLen (tmAddr sc M.k j z))
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + outLen ≤ lim.space)
    (hsep : Apart b outLen sc scratchLen)
    (hprefix : c.output.length + (tmAction M c q).output.toList.length ≤ outLen) :
    (tmTail M).Runs lim σ fun τ =>
      TMFrame M (M.tm.step c) a b sc (i + 1) τ ∧ TMTapes M (M.tm.step c) sc radius τ.mem ∧
      Seg τ.mem b (tmBits (M.tm.step c).output) ∧ SameOutside2 μ₀ τ.mem b outLen sc scratchLen := by
  classical
  have hstep : M.tm.step c = (tmAction M c q).apply c := Turing.MultiTapeTM.step_of_some hq
  rw [hstep]
  have hrange (j : Fin M.k) : tmAddr sc M.k j (c.workTapePos j) < lim.space := by
    have hcell := hinside j (c.workTapePos j) (hhead j)
    omega
  have hwork (j : Fin M.k) : σ.mem (tmAddr sc M.k j (c.workTapePos j)) =
      (tmSym (c.workTapeSymbols j) : ℤ) := by
    rw [Turing.Cfg.workTapeSymbols_eq]
    exact ht j (c.workTapePos j) (hhead j)
  unfold tmTail
  apply Stmt.Runs.seq
  apply (tmPrepare_runs M c σ hf hw hin h2 hL hk hc hinput hwork hrange).mono
  rintro ρ ⟨hfρ, hlρ, hsρ, hmem⟩
  apply Stmt.Runs.seq
  let actual : TMRow M := (q, c.inputSymbol, c.workTapeSymbols)
  have hactual : tmMatches (tmRowTests M actual) ρ := by
    apply (tmRowTests_matches_iff M actual ρ).mpr
    exact ⟨by simpa only [hq] using hfρ.control, hsρ.input, hsρ.work⟩
  have htests (row : TMRow M) (_ : row ∈ tmRows M) :
      ∀ pair ∈ tmRowTests M row, (pair.2 : ℤ) ≤ lim.word := by
    simp only [tmRowTests, List.forall_mem_cons, List.forall_mem_map,
      List.mem_finRange, forall_true_left]
    refine ⟨hstates _, ?_, fun j => ?_⟩
    · have := tmSym_le_two row.2.1
      omega
    · have := tmSym_le_two (row.2.2 j)
      omega
  have hrow : (tmRowBody M actual).Runs lim ρ fun τ =>
      TMFrame M ((tmAction M c q).apply c) a b sc i τ ∧
      TMTapes M ((tmAction M c q).apply c) sc radius τ.mem ∧
      Seg τ.mem b (tmBits ((tmAction M c q).apply c).output) ∧
      SameOutside2 μ₀ τ.mem b outLen sc scratchLen :=
    tmActionBody_runs M c (tmAction M c q) ρ μ₀ hfρ hlρ hsρ
      (by rw [hmem]; exact ht) (by rw [hmem]; exact hout) (by rw [hmem]; exact hkeep)
      hw h2 hL (hstates _) hm hhead hinside hscratch hspace hsep hprefix
  apply (tmDispatch_runs (actual := actual)
    (show actual ∈ tmRows M from Finset.mem_toList.mpr (Finset.mem_univ actual)) htests
    (fun row _ => tmRowTests_unique M actual row ρ hactual) hrow).mono
  rintro ν ⟨hfν, htν, houtν, hkeepν⟩
  have hsafe : (Expr.op .add (.var 7) (.const 1)).Safe lim ν := by
    simp only [Expr.safe_op_iff, Expr.safe_var_iff, Expr.safe_const_iff,
      Expr.val_var, Expr.val_const, Op.eval_add, hfν.round, Nat.cast_one, true_and]
    exact ⟨by omega, by rw [abs_of_nonneg (by positivity)]; exact hi⟩
  have hval : (Expr.op .add (.var 7) (.const 1)).val ν = ((i + 1 : ℕ) : ℤ) := by
    rw [Expr.val_op, Expr.val_var, Expr.val_const, Op.eval_add, hfν.round, Nat.cast_add,
      Nat.cast_one]
  apply (tmSet_runs (dst := 7) hsafe hval).mono
  rintro τ rfl
  exact ⟨tmFrame_round hfν (i + 1), htν, houtν, hkeepν⟩

/-- One simulator round initializes its newly reachable cells, then executes the transition. -/
private noncomputable def tmRound (M : Turing.FinTM Bool) : Stmt :=
  .seq (tmClearRing M) (tmTail M)

/-! ## Private bounded-run invariant -/

/-- Before round `i`, the stable frame, initialized work cells, output prefix, and untouched
external memory encode the machine after exactly `i` steps. -/
private structure TMRunInv (M : Turing.FinTM Bool) (x : List Bool)
    (a b sc outLen scratchLen : ℕ) (μ₀ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop where
  frame : TMFrame M (M.tm.runFrom (M.tm.initCfg x) i) a b sc i σ
  tapes : TMTapes M (M.tm.runFrom (M.tm.initCfg x) i) sc i σ.mem
  output : Seg σ.mem b (tmBits (M.tm.runFrom (M.tm.initCfg x) i).output)
  keep : SameOutside2 μ₀ σ.mem b outLen sc scratchLen

/-- A simulator round preserves the run invariant when its next initialized ring and all
intermediate words fit the supplied limits.

**Proof sketch.** `tmClearRing_ends` changes only the initialization temporaries and the next
scratch ring. Its `SameOutside` contract preserves the output and composes with the external
memory promise. `tmRingMemory_tapes` extends the represented tapes to radius `i + 1`.
The unchanged-memory promise and region separation recover the input words. Head envelopes
bound cell codes and next head values. `tmTail_runs` then performs the live step; the published
successor-run equation identifies its result with round `i + 1`. -/
private theorem tmRound_ends (M : Turing.FinTM Bool) (x : List Bool)
    {lim : Limits} {P : Program} {d a b sc outLen scratchLen i : ℕ}
    (σ : State) (μ₀ : ℕ → ℤ) (hI : TMRunInv M x a b sc outLen scratchLen μ₀ i σ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2i : (2 : ℤ) * ((i : ℤ) + 1) ≤ lim.word) (hk2 : (2 : ℤ) * M.k ≤ lim.word)
    (hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word)
    (hring : 2 * (i + 1) * M.k ≤ scratchLen)
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + outLen ≤ lim.space)
    (hsepIO : Apart a x.length b outLen) (hsepIS : Apart a x.length sc scratchLen)
    (hsepOS : Apart b outLen sc scratchLen)
    (hinput : ∀ u < x.length, μ₀ (a + u) = ((x.getD u false).toNat : ℤ))
    (hL : (x.length : ℤ) + 1 ≤ lim.word)
    (hlive : (M.tm.runFrom (M.tm.initCfg x) i).state ≠ none)
    (hnext : (M.tm.runFrom (M.tm.initCfg x) (i + 1)).output.length ≤ outLen) :
    Ends lim P d (tmRound M) σ (26 * M.k + 18 + (tmTail M).blockCost)
      (TMRunInv M x a b sc outLen scratchLen μ₀ (i + 1)) := by
  let c := M.tm.runFrom (M.tm.initCfg x) i
  obtain ⟨q, hq⟩ : ∃ q, c.state = some q := Option.ne_none_iff_exists'.mp hlive
  have hstep : M.tm.step c = (tmAction M c q).apply c := Turing.MultiTapeTM.step_of_some hq
  have hprefix : c.output.length + (tmAction M c q).output.toList.length ≤ outLen := by
    rw [Turing.MultiTapeTM.runFrom_succ_eq_step'] at hnext
    change (M.tm.step c).output.length ≤ outLen at hnext
    rw [hstep, Turing.Action.apply_output, List.length_append] at hnext
    exact hnext
  have hend : sc + 2 * i * M.k + 2 * M.k ≤ sc + scratchLen := by nlinarith
  unfold tmRound
  refine Ends.seq (26 * M.k + 18) (tmTail M).blockCost ?_ (Nat.le_refl _)
  apply (tmClearRing_ends M σ sc i hI.frame.scratch hI.frame.round hw
    (by omega) h2i hk2).mono (Nat.le_refl _)
  rintro ρ ⟨hmem, hloc⟩
  have hfρ : TMFrame M c a b sc i ρ := by
    apply tmFrame_transfer hI.frame
    · intro v hv _
      apply hloc v
      · rcases hv with hv | ⟨j, hj⟩ <;> (try unfold tmHead at hj) <;> omega
      · rcases hv with hv | ⟨j, hj⟩ <;> (try unfold tmHead at hj) <;> omega
      · rcases hv with hv | ⟨j, hj⟩
        · omega
        · have := j.isLt
          unfold tmHead at hj
          omega
    · exact (hloc 7 (by decide) (by decide) (by omega)).trans hI.frame.round
  have hclear : SameOutside σ.mem ρ.mem sc scratchLen := by
    rw [hmem]
    exact SameOutside.mono (sameOutside_wrote (μ := σ.mem)
      (dst := sc + 2 * i * M.k) (f := fun _ => (0 : ℤ)) (j := 2 * M.k)
      (n := 2 * M.k) (Nat.le_refl _)) (by omega) hend
  have hkeepρ : SameOutside2 μ₀ ρ.mem b outLen sc scratchLen :=
    SameOn.then hI.keep hclear (fun _ h => ⟨h, h.2⟩)
  have houtρ : Seg ρ.mem b (tmBits c.output) := by
    have hout0 : Seg σ.mem b (tmBits c.output) := hI.output
    apply hout0.of_sameOutside hclear
    simp only [tmBits, List.length_map]
    rcases hsepOS with hsepOS | hsepOS <;> omega
  have htρ : TMTapes M c sc (i + 1) ρ.mem := by
    intro j z hz
    rw [hmem]
    exact tmRingMemory_tapes M x i sc σ.mem hI.tapes j z (by omega)
  have hhead (j : Fin M.k) : |c.workTapePos j| < ((i + 1 : ℕ) : ℤ) := by
    have hb := tmHead_abs_le M x i j
    change |c.workTapePos j| ≤ (i : ℤ) at hb
    omega
  have hinside (j : Fin M.k) (z : ℤ) (hz : |z| < ((i + 1 : ℕ) : ℤ)) :
      Inside sc scratchLen (tmAddr sc M.k j z) := by
    have haddr := tmAddr_lt (sc := sc) (tapes := M.k) (n := i) j (show |z| ≤ (i : ℤ) by omega)
    have hs : M.k * (2 * i + 2) ≤ scratchLen := by nlinarith
    exact ⟨by unfold tmAddr; omega, by omega⟩
  have hc (j : Fin M.k) : (tmCell (c.workTapePos j) : ℤ) ≤ lim.word := by
    have hn := tmCell_le (tmHead_abs_le M x i j)
    have hnZ : (tmCell (c.workTapePos j) : ℤ) ≤ 2 * (i : ℤ) + 1 := by exact_mod_cast hn
    omega
  have hinputρ (u : ℕ) (hu : u < x.length) :
      ρ.mem (a + u) = ((x.getD u false).toNat : ℤ) := by
    have he : ρ.mem (a + u) = μ₀ (a + u) :=
      SameOn.cell (hkeepρ.mono (by
        intro v hv
        subst v
        constructor
        · rcases hsepIO with h | h <;> omega
        · rcases hsepIS with h | h <;> omega))
    exact he.trans (hinput u hu)
  have hm (j : Fin M.k) :
      |c.workTapePos j + (((tmAction M c q).workTapes j).2.cast : ℤ)| ≤ lim.word := by
    have hb := tmHead_abs_le M x (i + 1) j
    rw [Turing.MultiTapeTM.runFrom_succ_eq_step'] at hb
    change |(M.tm.step c).workTapePos j| ≤ ((i + 1 : ℕ) : ℤ) at hb
    rw [hstep, Turing.Action.apply_workTapePos] at hb
    omega
  refine Ends.block ?_ (Nat.le_refl _)
  apply (tmTail_runs M c q hq ρ μ₀ hfρ htρ houtρ hkeepρ hw hin
    (by omega) hL (by omega) (by omega) hstates hc hinputρ hm hhead hinside
    hscratch hspace hsepOS hprefix).mono
  rintro τ ⟨hfτ, htτ, houtτ, hkeepτ⟩
  constructor
  · simpa only [Turing.MultiTapeTM.runFrom_succ_eq_step'] using hfτ
  · simpa only [Turing.MultiTapeTM.runFrom_succ_eq_step'] using htτ
  · simpa only [Turing.MultiTapeTM.runFrom_succ_eq_step'] using houtτ
  · exact hkeepτ

/-- Initialize the scalar configuration locals and the work-head bank. -/
private noncomputable def tmSetup (M : Turing.FinTM Bool) : Stmt :=
  .seq (.set 4 (.const 1)) (.seq (.set 5 (.const (tmStateCode M (some M.tm.q₀))))
    (.seq (.set 6 (.const 0)) (.seq (.set 7 (.const 0))
      (tmBank M (fun j => .set (tmHead j.val) (.const 0))))))

/-- Zeroing the static head bank preserves all scalar locals and memory.

**Proof sketch.** Apply `tmSeq_accumulate` to the finite tape list. Every assignment changes
only its own head local, which is above all eight scalar locals. It sets that head to zero
and preserves any head already known to be zero, even when the two indices coincide. -/
private theorem tmZeroHeads_runs (M : Turing.FinTM Bool) {lim : Limits} (σ : State)
    (h0 : (0 : ℤ) ≤ lim.word) :
    (tmBank M (fun j => .set (tmHead j.val) (.const 0))).Runs lim σ fun τ =>
      (∀ v < 8, τ.loc v = σ.loc v) ∧ τ.mem = σ.mem ∧
      ∀ j : Fin M.k, τ.loc (tmHead j.val) = 0 := by
  let I : State → Prop := fun τ => (∀ v < 8, τ.loc v = σ.loc v) ∧ τ.mem = σ.mem
  let F : Fin M.k → State → Prop := fun j τ => τ.loc (tmHead j.val) = 0
  have hr : (tmBank M (fun j => .set (tmHead j.val) (.const 0))).Runs lim σ fun τ =>
      I τ ∧ (∀ j ∈ List.finRange M.k, F j τ) ∧ ∀ j, F j σ → F j τ := by
    apply tmSeq_accumulate (I := I) (F := F) ⟨fun _ _ => rfl, rfl⟩
    intro j _ τ hτ
    apply (tmSet_runs (dst := tmHead j.val) ((Expr.safe_const_iff _ _ _).mpr h0)
      (Expr.val_const _ 0)).mono
    rintro τ' rfl
    refine ⟨⟨?_, hτ.2⟩, ?_, ?_⟩
    · intro v hv
      exact (Function.update_of_ne (show v ≠ tmHead j.val by unfold tmHead; omega)
        (0 : ℤ) τ.loc).trans (hτ.1 v hv)
    · exact Function.update_self ..
    · intro l hl
      change Function.update τ.loc (tmHead j.val) (0 : ℤ) (tmHead l.val) = 0
      by_cases he : tmHead l.val = tmHead j.val
      · rw [he, Function.update_self]
      · exact (Function.update_of_ne he (0 : ℤ) τ.loc).trans hl
  exact hr.mono fun τ hτ => ⟨hτ.1.1, hτ.1.2, fun j => hτ.2.1 j (List.mem_finRange j)⟩

/-- Setup produces the initial machine frame and preserves the argument memory.

**Proof sketch.** Perform the four safe scalar assignments, then use `tmZeroHeads_runs` for
the head bank. The bank preserves the scalar assignments and the original arguments. The
published initialization field equations identify these values with `M.tm.initCfg x`. -/
private theorem tmSetup_runs (M : Turing.FinTM Bool) (x : List Bool)
    {lim : Limits} {a b sc : ℕ} (σ : State)
    (ha : σ.loc 0 = (a : ℤ)) (hn : σ.loc 1 = (x.length : ℤ))
    (hb : σ.loc 2 = (b : ℤ)) (hsc : σ.loc 3 = (sc : ℤ))
    (h1 : (1 : ℤ) ≤ lim.word) (hq : (tmStateCode M (some M.tm.q₀) : ℤ) ≤ lim.word) :
    (tmSetup M).Runs lim σ fun τ => TMFrame M (M.tm.initCfg x) a b sc 0 τ ∧ τ.mem = σ.mem := by
  have h0 : (0 : ℤ) ≤ lim.word := by omega
  unfold tmSetup
  apply Stmt.Runs.seq
  apply (tmSet_runs (dst := 4) ((Expr.safe_const_iff _ _ _).mpr h1) (Expr.val_const _ 1)).mono
  rintro σ₁ rfl
  apply Stmt.Runs.seq
  apply (tmSet_runs (dst := 5) ((Expr.safe_const_iff _ _ _).mpr hq) (Expr.val_const _ _)).mono
  rintro σ₂ rfl
  apply Stmt.Runs.seq
  apply (tmSet_runs (dst := 6) ((Expr.safe_const_iff _ _ _).mpr h0) (Expr.val_const _ 0)).mono
  rintro σ₃ rfl
  apply Stmt.Runs.seq
  apply (tmSet_runs (dst := 7) ((Expr.safe_const_iff _ _ _).mpr h0) (Expr.val_const _ 0)).mono
  rintro σ₄ rfl
  apply (tmZeroHeads_runs M _ h0).mono
  rintro τ ⟨hscalar, hmem, hheads⟩
  have harg (v : ℕ) (hv : v < 4) : τ.loc v = σ.loc v := by
    simpa only [Function.update_of_ne (show v ≠ 7 by omega),
      Function.update_of_ne (show v ≠ 6 by omega), Function.update_of_ne (show v ≠ 5 by omega),
      Function.update_of_ne (show v ≠ 4 by omega)] using hscalar v (by omega)
  refine ⟨?_, hmem⟩
  constructor
  · exact (harg 0 (by decide)).trans ha
  · exact (harg 1 (by decide)).trans hn
  · exact (harg 2 (by decide)).trans hb
  · exact (harg 3 (by decide)).trans hsc
  · rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_inputPos]
    simpa only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 7),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 5), Function.update_self] using hscalar 4 (by decide)
  · rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_state]
    simpa only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 7),
      Function.update_of_ne (by decide : (5 : ℕ) ≠ 6), Function.update_self] using hscalar 5 (by decide)
  · rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_output]
    simpa only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 7),
      Function.update_self, List.length_nil, Nat.cast_zero] using hscalar 6 (by decide)
  · simpa only [Function.update_self, Nat.cast_zero] using hscalar 7 (by decide)
  · intro j
    rw [Turing.MultiTapeTM.initCfg_eq, Turing.Cfg.init_workTapePos]
    exact hheads j

/-- The loop guard is safe when zero fits, and it holds exactly for a live encoded state. -/
private theorem tmGuard_read (M : Turing.FinTM Bool) {x : List Bool}
    (c : Turing.Cfg M.k Bool M.State x) {lim : Limits} (σ : State)
    (hc : σ.loc 5 = (tmStateCode M c.state : ℤ)) (h0 : (0 : ℤ) ≤ lim.word) :
    (Cond.lt (.const 0) (.var 5)).Safe lim σ ∧
      ((Cond.lt (.const 0) (.var 5)).Holds σ ↔ c.state ≠ none) := by
  constructor
  · rw [Cond.safe_lt_iff, Expr.safe_const_iff, Expr.safe_var_iff]
    exact ⟨h0, trivial⟩
  · rw [Cond.holds_lt_iff, Expr.val_const, Expr.val_var, hc, Nat.cast_zero]
    cases hs : c.state with
    | none => simp only [tmStateCode, Nat.cast_zero, lt_self_iff_false, ne_self_iff_false]
    | some q =>
      simp only [tmStateCode, Nat.cast_add, Nat.cast_one, ne_eq, Option.some_ne_none, not_false_eq_true,
        iff_true]
      positivity

/-- The verified rounds run until the first halting time, with a constant cost per round.

**Proof sketch.** Apply `Ends.whileConst` to `TMRunInv`. `tmGuard_read` makes the guard true
before the supplied first halt and false at it. Each live iteration uses `tmRound_ends`;
the initialized-head envelope and the total scratch bound supply its ring bounds. The output
prefix theorem bounds every intermediate emission by the final output. -/
private theorem tmLoop_ends (M : Turing.FinTM Bool) (x out : List Bool) (u : ℕ)
    {lim : Limits} {P : Program} {d a b sc scratchLen : ℕ} (σ : State) (μ₀ : ℕ → ℤ)
    (hI : TMRunInv M x a b sc out.length scratchLen μ₀ 0 σ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2u : (2 : ℤ) * u ≤ lim.word) (hk2 : (2 : ℤ) * M.k ≤ lim.word)
    (hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word)
    (hrings : 2 * u * M.k ≤ scratchLen)
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + out.length ≤ lim.space)
    (hsepIO : Apart a x.length b out.length) (hsepIS : Apart a x.length sc scratchLen)
    (hsepOS : Apart b out.length sc scratchLen)
    (hinput : ∀ j < x.length, μ₀ (a + j) = ((x.getD j false).toNat : ℤ))
    (hL : (x.length : ℤ) + 1 ≤ lim.word)
    (hhalt : (M.tm.runFrom (M.tm.initCfg x) u).state = none)
    (hout : (M.tm.runFrom (M.tm.initCfg x) u).output = out)
    (hlive : ∀ i < u, (M.tm.runFrom (M.tm.initCfg x) i).state ≠ none) :
    Ends lim P d (.while (.lt (.const 0) (.var 5)) (tmRound M)) σ
      (u * (4 + (26 * M.k + 18 + (tmTail M).blockCost)) + 4)
      (TMRunInv M x a b sc out.length scratchLen μ₀ u) := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg _) hw
  refine Ends.whileConst (TMRunInv M x a b sc out.length scratchLen μ₀) u
    (26 * M.k + 18 + (tmTail M).blockCost) hI ?_ ?_ ?_
  · intro i τ hi hτ
    have hg := tmGuard_read M _ τ hτ.frame.control h0
    refine ⟨hg.1, hg.2.mpr (hlive i hi), ?_⟩
    have hr : 2 * (i + 1) * M.k ≤ scratchLen :=
      (Nat.mul_le_mul_right M.k (show 2 * (i + 1) ≤ 2 * u by omega)).trans hrings
    have hn : (M.tm.runFrom (M.tm.initCfg x) (i + 1)).output.length ≤ out.length := by
      have hp := M.tm.output_prefix (M.tm.initCfg x) (t := i + 1) (t' := u) (by omega)
      rw [hout] at hp
      exact hp.length_le
    exact tmRound_ends M x τ μ₀ hτ hw hin (by omega) hk2 hstates hr hscratch hspace
      hsepIO hsepIS hsepOS hinput hL (hlive i hi) hn
  · intro τ hτ
    have hg := tmGuard_read M _ τ hτ.frame.control h0
    exact ⟨hg.1, fun hh => (hg.2.mp hh) hhalt, hτ⟩
  · simp only [Cond.cost_lt, Expr.cost_const, Expr.cost_var]
    exact Nat.le_refl _

/-- The generated simulator has one procedure and no calls. The loop observes the encoded
halting state, and local zero receives the final output length only after the loop. -/
private noncomputable def tmBody (M : Turing.FinTM Bool) : Stmt :=
  .seq (tmSetup M) (.seq (.while (.lt (.const 0) (.var 5)) (tmRound M)) (.set 0 (.var 6)))

/-- Read a bit segment in the exact default-index form used by the procedure specification. -/
private theorem tmBits_read {μ : ℕ → ℤ} {b : ℕ} {out : List Bool}
    (h : Seg μ b (tmBits out)) {j : ℕ} (hj : j < out.length) :
    μ (b + j) = ((out.getD j false).toNat : ℤ) := by
  have hj' : j < (tmBits out).length := by simpa only [tmBits, List.length_map] using hj
  rw [List.getD_eq_getElem _ _ hj]
  simpa only [tmBits, List.getElem_map] using h.get hj'

/-- Setup, the finite simulation loop, and the final return give the complete body contract.

**Proof sketch.** The read-only setup produces the initial frame; its empty tape radius and
empty output establish `TMRunInv` at zero. Run `tmLoop_ends` to the supplied first halt. Its
frame records the final output length and its output segment is the prescribed output. A last
safe variable assignment copies that length into the return local, preserving memory. -/
private theorem tmBody_ends (M : Turing.FinTM Bool) (x out : List Bool) (u : ℕ)
    {lim : Limits} {P : Program} {d a b sc scratchLen : ℕ} (σ : State)
    (ha : σ.loc 0 = (a : ℤ)) (hn : σ.loc 1 = (x.length : ℤ))
    (hb : σ.loc 2 = (b : ℤ)) (hsc : σ.loc 3 = (sc : ℤ))
    (hw : (lim.space : ℤ) ≤ lim.word) (hin : a + x.length ≤ lim.space)
    (h2u : (2 : ℤ) * u ≤ lim.word) (hk2 : (2 : ℤ) * M.k ≤ lim.word)
    (hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word)
    (hrings : 2 * u * M.k ≤ scratchLen)
    (hscratch : sc + scratchLen ≤ lim.space) (hspace : b + out.length ≤ lim.space)
    (hsepIO : Apart a x.length b out.length) (hsepIS : Apart a x.length sc scratchLen)
    (hsepOS : Apart b out.length sc scratchLen)
    (hinput : ∀ j < x.length, σ.mem (a + j) = ((x.getD j false).toNat : ℤ))
    (hL : (x.length : ℤ) + 1 ≤ lim.word)
    (hhalt : (M.tm.runFrom (M.tm.initCfg x) u).state = none)
    (hout : (M.tm.runFrom (M.tm.initCfg x) u).output = out)
    (hlive : ∀ i < u, (M.tm.runFrom (M.tm.initCfg x) i).state ≠ none) :
    Ends lim P d (tmBody M) σ
      ((tmSetup M).blockCost + u * (4 + (26 * M.k + 18 + (tmTail M).blockCost)) + 6)
      fun τ => τ.loc 0 = (out.length : ℤ) ∧ Seg τ.mem b (tmBits out) ∧
        SameOutside2 σ.mem τ.mem b out.length sc scratchLen := by
  let loopCost := u * (4 + (26 * M.k + 18 + (tmTail M).blockCost)) + 4
  unfold tmBody
  refine Ends.seq (tmSetup M).blockCost (loopCost + 2) ?_ (by dsimp only [loopCost]; omega)
  refine Ends.block ?_ (Nat.le_refl _)
  apply (tmSetup_runs M x σ ha hn hb hsc (by omega) (hstates _)).mono
  rintro ρ ⟨hfρ, hmem⟩
  have hI : TMRunInv M x a b sc out.length scratchLen σ.mem 0 ρ := by
    constructor
    · simpa only [Turing.MultiTapeTM.runFrom_zero] using hfρ
    · intro j z hz
      have := abs_nonneg z
      omega
    · rw [Turing.MultiTapeTM.runFrom_zero, Turing.MultiTapeTM.initCfg_eq,
        Turing.Cfg.init_output]
      exact Seg.nil
    · rw [hmem]
      exact SameOutside2.refl
  refine Ends.seq loopCost 2 ?_ (by omega)
  apply (tmLoop_ends M x out u ρ σ.mem hI hw hin h2u hk2 hstates hrings hscratch hspace
    hsepIO hsepIS hsepOS hinput hL hhalt hout hlive).mono (Nat.le_refl _)
  intro τ hτ
  have hlen : τ.loc 6 = (out.length : ℤ) := by rw [hτ.frame.outputLen, hout]
  have houtτ : Seg τ.mem b (tmBits out) := by rw [← hout]; exact hτ.output
  refine Ends.set ((Expr.safe_var_iff _ _ _).mpr trivial) ?_ ?_
  · rw [Expr.cost_var]
  · rw [Expr.val_var]
    refine ⟨?_, houtτ, hτ.keep⟩
    change Function.update τ.loc 0 (τ.loc 6) 0 = (out.length : ℤ)
    rw [Function.update_self, hlen]

/-- **A Turing machine as a Light procedure.** For every finite binary machine `M` there are a
program `Q`, a procedure number `p` in it, and constants `A` and `k` such that, wherever `Q` is
placed (behind any program `Pre`, followed by any procedures `Post`), procedure `p + |Pre|`, called
with the arguments `[a, len, b, sc]`, does the following. If the memory holds the input `x` at
`a`, one cell per bit (`0` or `1`), and `M` computes `out` from `x` within `t` steps, then within
`A·(t + len + 1)` steps it returns `|out|`, holds `out` at `b`, one cell per bit, and changes no
cell outside the output's cells and the scratch region of `A·(t + len + 1)` cells at `sc`. The
hypotheses: the regions fit in memory and are pairwise apart; addresses fit in a word; and the
procedure's call depth `k` fits.

`Q`, `p`, `A` and `k` depend on `M` only, so a uniform machine gives a uniform procedure, and a
program calling it stays one program for all inputs.

**Proof sketch.**
- **Encoding.** `tmStateCode` assigns zero to halt and positive indices from a fixed finite
  enumeration to live states. `tmSym` assigns zero, one, and two to blank, false, and true.
  `tmCell` and `tmAddr` interleave the signed cells of the work tapes in scratch memory;
  `tmAddr_injective` separates the cells and `tmAddr_lt` bounds the memory needed at a radius.
  `TMFrame` records the stable locals.
- **One step.** `tmRound` first clears its next ring with the existing `pass` routine.
  `tmClearRing_ends` bounds that initialization and `tmRingMemory_tapes` extends the valid tape
  representation. `tmLocate_runs` freezes each old head and computes its direct address;
  `tmReadInput_runs` reads the input in place. The finite code branches generated by
  `tmDispatch` choose exactly the row identified by `tmRowTests_unique`. The row writes each
  tape, moves the heads, appends the optional output bit, and updates the control state.
- **The run.** `TMRunInv` couples each round to `M.tm.runFrom (M.tm.initCfg x) i`, and
  `tmRound_ends` preserves its configuration, tapes, output prefix, and memory promise.
  `tmSetup_runs` initializes the frame. `tmFirstHalt` supplies the first halting time at most
  `t`; `tmLoop_ends` applies `Ends.whileConst`, and `tmBody_ends` returns the output length.
  Choose `A` as the sum of setup cost, per-round cost, the state-code bound, twice the tape
  count, and ten. It bounds time, scratch, and intermediate words. `tmBits_read` recovers
  the specified individual output bits.
- **Placement.** Build the procedure specification for its singleton program and use
  `tmMeets_behind` to carry it to `Program.behind Pre Q ++ Post`. -/
theorem exists_tmProc (M : Turing.FinTM Bool) :
    ∃ (Q : Program) (p A k : ℕ), ∀ (Pre Post : Program) (lim : Limits) (d : ℕ)
      (a len b sc : ℕ) (μ : ℕ → ℤ) (x out : List Bool) (t : ℕ),
      x.length = len →
      (∀ i < len, μ (a + i) = ((x.getD i false).toNat : ℤ)) →
      M.ComputesInTime x out t →
      (lim.space : ℤ) ≤ lim.word →
      a + len ≤ lim.space → b + out.length ≤ lim.space → sc + A * (t + len + 1) ≤ lim.space →
      Apart a len b out.length → Apart a len sc (A * (t + len + 1)) →
      Apart b out.length sc (A * (t + len + 1)) →
      d + k ≤ lim.depth →
      Meets lim (Program.behind Pre Q ++ Post) (p + Pre.length) d [(a : ℤ), len, b, sc] μ
        (A * (t + len + 1)) fun r μ' =>
          r = out.length ∧ (∀ i < out.length, μ' (b + i) = ((out.getD i false).toNat : ℤ)) ∧
          SameOutside2 μ μ' b out.length sc (A * (t + len + 1)) := by
  classical
  let setup := (tmSetup M).blockCost
  let step := 4 + (26 * M.k + 18 + (tmTail M).blockCost)
  let states := (Finset.univ.toList : List M.State).length + 1
  let A := setup + step + states + 2 * M.k + 10
  refine ⟨[tmBody M], 0, A, 0, ?_⟩
  intro Pre Post lim d a len b sc μ x out t hlen hinput ht hw hin hspace hscratch
    hsepIO hsepIS hsepOS _
  subst len
  obtain ⟨u, hu, _, hhalt, hout, hlive⟩ := tmFirstHalt M ht
  let S := t + x.length + 1
  let N := A * S
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have huS : u + 1 ≤ S := by dsimp only [S]; omega
  have hA1 : 1 ≤ A := by dsimp only [A]; omega
  have hA2 : 2 ≤ A := by omega
  have hAk : 2 * M.k ≤ A := by dsimp only [A]; omega
  have hAstates : states ≤ A := by dsimp only [A]; omega
  have hAstep : step ≤ A := by dsimp only [A]; omega
  have hAsetup : setup + 6 ≤ A := by dsimp only [A]; omega
  have hAN : A ≤ N := by dsimp only [N]; nlinarith
  have hNspace : N ≤ lim.space := by
    change sc + N ≤ lim.space at hscratch
    omega
  have hNword : (N : ℤ) ≤ lim.word :=
    (show (N : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast hNspace).trans hw
  have h2uN : 2 * u ≤ N := Nat.mul_le_mul hA2 (show u ≤ S by omega)
  have hkN : 2 * M.k ≤ N := hAk.trans hAN
  have hstates : ∀ s, (tmStateCode M s : ℤ) ≤ lim.word := by
    intro s
    have hsN : tmStateCode M s ≤ N := (tmStateCode_le M s).trans (hAstates.trans hAN)
    exact (show (tmStateCode M s : ℤ) ≤ (N : ℤ) by exact_mod_cast hsN).trans hNword
  have hrings : 2 * u * M.k ≤ N := by
    calc
      2 * u * M.k = (2 * M.k) * u := by ring
      _ ≤ A * S := Nat.mul_le_mul hAk (by omega)
  have hLN : x.length + 1 ≤ N := by
    have hLS : x.length + 1 ≤ S := by dsimp only [S]; omega
    dsimp only [N]
    nlinarith
  have hL : (x.length : ℤ) + 1 ≤ lim.word :=
    (show (x.length : ℤ) + 1 ≤ (N : ℤ) by exact_mod_cast hLN).trans hNword
  have htime : setup + u * step + 6 ≤ N := by
    calc
      setup + u * step + 6 ≤ A + u * A := by
        have := Nat.mul_le_mul_left u hAstep
        omega
      _ = A * (u + 1) := by ring
      _ ≤ A * S := Nat.mul_le_mul_left A huS
  refine tmMeets_behind (Meets.of_body (p := 0)
    (show ([tmBody M] : Program)[0]? = some (tmBody M) from rfl) ?_) Pre Post
  apply (tmBody_ends M x out u (State.mk (frame [(a : ℤ), x.length, b, sc]) μ)
    (by change frame [(a : ℤ), x.length, b, sc] 0 = (a : ℤ); rw [frame_apply]; rfl)
    (by change frame [(a : ℤ), x.length, b, sc] 1 = (x.length : ℤ); rw [frame_apply]; rfl)
    (by change frame [(a : ℤ), x.length, b, sc] 2 = (b : ℤ); rw [frame_apply]; rfl)
    (by change frame [(a : ℤ), x.length, b, sc] 3 = (sc : ℤ); rw [frame_apply]; rfl)
    hw hin
    ((show (2 : ℤ) * u ≤ (N : ℤ) by exact_mod_cast h2uN).trans hNword)
    ((show (2 : ℤ) * M.k ≤ (N : ℤ) by exact_mod_cast hkN).trans hNword)
    hstates hrings hscratch hspace hsepIO hsepIS hsepOS hinput hL hhalt hout hlive).mono htime
  rintro τ ⟨hret, hseg, hkeep⟩
  exact ⟨hret, fun j hj => tmBits_read hseg hj, hkeep⟩


end Light
