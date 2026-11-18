/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Reach
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Scan
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.SeamLayout

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed-width words on tapes: arithmetic rows

A word of `W` bits (`BitVec W`) is held on a work tape as its `W` bits, least significant first,
delimited by blanks at the head's offsets `-1` and `W`. This file proves the rows that compute
on such words: addition, subtraction and multiplication modulo `2^W`, the arithmetic shift right,
sign extension, writing the word of an integer constant, and the sign and zero tests. They are the
arithmetic of a word RAM run on a Turing machine (`WordRAM.exists_simulation`).

Every row is a five-tape machine over `Bool`: tapes `0` and `1` hold the operands, tape `2` the
destination, and tapes `3` and `4` are blank scratch tapes, left blank. A row writes only the
destination's word interval, leaves every head where it was, and is stated with
`Turing.ReachesWithin`. A consumer places the five tapes among its own with `Turing.embedEmitTM`
and composes the rows with `Turing.Contract.ofReaches`. The words have one width throughout, so
the length of an operand delimits every scan and `W = 0` (empty words) needs no special case.

No row of the catalog reads two tapes with a carry, so one framed, alias-safe lockstep
transducer supplies addition, subtraction, copies, constant writes, and the multiplier's
in-place addition. The public phase host composes multiplication, halving and sign extension
from these sweeps and the catalog's scan, walk, constant-writer, clear and rewind rows.
The sign and zero tests reuse the one-tape `Turing.scanTM` through its read-only fold instance.

## Main definitions

* `Turing.bvBits`: the bits of a word, least significant first.
* `Turing.WordAt`: a word delimited at a head.
* `Turing.wordWrite`: the tapes after writing a word at a head.

## Main results

* `Turing.exists_wordAddTM`, `Turing.exists_wordSubTM`, `Turing.exists_wordMulTM`: addition,
  subtraction and multiplication modulo `2^W`, in `O(W)`, `O(W)` and `O(W²)` steps.
* `Turing.exists_wordHalfTM`: the arithmetic shift right by one place.
* `Turing.exists_wordSignExtendTM`: sign extension from `W` to `W + a` bits.
* `Turing.exists_wordIntTM`: the word of an integer constant, as wide as a guide word plus `a`.
* `Turing.exists_wordSignTM`, `Turing.exists_wordNonzeroTM`: the tests `u < 0` and `u ≠ 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: multitape machines; Exercise 1.9: a RAM simulated by a
  Turing machine, whose arithmetic these rows provide.)
-/

namespace Turing

/-! ## Words on tapes -/

/-- **The bits of a word**, least significant first: `bvBits v = [v₀, v₁, …, v_{W-1}]`. -/
def bvBits {W : ℕ} (v : BitVec W) : List Bool := List.ofFn fun i : Fin W => v.getLsbD i

/-- The bits of a word, as an equation. -/
theorem bvBits_def {W : ℕ} (v : BitVec W) :
    bvBits v = List.ofFn fun i : Fin W => v.getLsbD i := rfl

/-- A word of `W` bits has `W` bits. -/
theorem bvBits_length {W : ℕ} (v : BitVec W) : (bvBits v).length = W := by
  simp [bvBits]

/-- Distinct words have distinct bits.

**Proof sketch.** Equal bit lists give `getLsbD` equal at every `i < W` (`List.ofFn_inj`), and
`BitVec.eq_of_getLsbD_eq` concludes. -/
theorem bvBits_injective {W : ℕ} : Function.Injective (bvBits (W := W)) := by
  intro u v h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he := List.ofFn_inj.mp h
  exact congrFun he ⟨i, hi⟩

/-- **A word delimited at a head**: tape `r` holds `w` from its head, with blanks at the head's
offsets `-1` and `|w|`. The cells beyond are arbitrary. -/
def WordAt {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K) (w : List Bool) :
    Prop :=
  ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape w p

/-- `WordAt`, as an equivalence with its definition. -/
theorem wordAt_iff {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) :
    WordAt d r w ↔ ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape w p :=
  Iff.rfl

/-- **The tapes after writing a word at a head**: on tape `r`, the cells from its head on hold `w`
over `|w|` cells; every other cell, of every tape, is unchanged. -/
def wordWrite {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) : Fin K → ℤ → Option Bool :=
  fun j q =>
    if j = r ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
      then FinTM.bufferTape w (q - d.workTapePos j)
    else d.workTapes j q

/-- `wordWrite`, as an equation. -/
theorem wordWrite_apply {K : ℕ} {S : Type} {x : List Bool} (d : Cfg K Bool S x) (r : Fin K)
    (w : List Bool) (j : Fin K) (q : ℤ) :
    wordWrite d r w j q =
      if j = r ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape w (q - d.workTapePos j)
      else d.workTapes j q :=
  rfl

/-- **The common precondition of the word rows**: tapes `3` and `4` are blank everywhere. -/
def ScratchBlank {S : Type} {x : List Bool} (d : Cfg 5 Bool S x) : Prop :=
  ∀ j : Fin 5, 3 ≤ j.val → ∀ p : ℤ, d.workTapes j p = none

/-- `ScratchBlank`, as an equivalence with its definition. -/
theorem scratchBlank_iff {S : Type} {x : List Bool} (d : Cfg 5 Bool S x) :
    ScratchBlank d ↔ ∀ j : Fin 5, 3 ≤ j.val → ∀ p : ℤ, d.workTapes j p = none :=
  Iff.rfl

/-! ## Framed lockstep transducers -/

/-- Move the three selected heads together, optionally writing one destination bit. -/
private def wordLockAction {k : ℕ} {A : Type} (src rhs dst : Fin k) (b : Option Bool)
    (m : SignType) (q : ScanPhase A) : Action k Bool (ScanPhase A) :=
  ⟨0, fun j => (if j = dst then b.map some else none,
    if j = src ∨ j = rhs ∨ j = dst then m else 0), none, some q⟩

/-- The lockstep action changes only its destination cell and the selected heads.

**Proof sketch.** Read the action's five fields through the published `Action.apply` readers.
An absent write keeps the original scanned symbol, and a present bit updates just the
destination cell. The input head and output are stationary; the selected work heads move
by the prescribed sign. -/
private theorem wordLockAction_apply {k : ℕ} {A : Type} {x : List Bool}
    (src rhs dst : Fin k) (b : Option Bool) (m : SignType) (q : ScanPhase A)
    (d : Cfg k Bool (ScanPhase A) x) :
    (wordLockAction src rhs dst b m q).apply d =
      { d with
        state := some q
        workTapes := fun j => if j = dst then
          match b with
          | none => d.workTapes j
          | some bit => Function.update (d.workTapes j) (d.workTapePos j) (some bit)
          else d.workTapes j
        workTapePos := fun j => d.workTapePos j +
          if j = src ∨ j = rhs ∨ j = dst then (m : ℤ) else 0} := by
  apply Cfg.ext
  · rw [Action.apply_state]; rfl
  · rw [Action.apply_inputPos]; exact moveInputPos_zero _
  · funext j
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    by_cases hj : j = dst <;> cases b <;>
      simp only [wordLockAction, hj, if_true, if_false, Option.map_none, Option.map_some,
        Option.getD_none, Option.getD_some, Function.update_eq_self]
  · funext j
    rw [Action.apply_workTapePos]
    by_cases hj : j = src ∨ j = rhs ∨ j = dst <;>
      simp only [wordLockAction, hj, if_true, if_false, SignType.coe_zero]
  · rw [Action.apply_output]; exact List.append_nil _

/-- A two-source finite-state sweep, followed by a return guided by the first source.
The catalog's one-tape scan cannot read both source bits with a carry. The selected tapes may
alias: the forward pass reads each cell before writing it, and every written cell stays nonblank.
The carry is discarded at the right delimiter, so every run has the same live exit. -/
private def wordLockTM {k : ℕ} {A : Type} (src rhs dst : Fin k)
    (δ : A → Bool → Bool → A × Bool) (a₀ : A) : MultiTapeTM k Bool (ScanPhase A) where
  q₀ := .fwd a₀
  tr := fun q _ w => match q with
    | .fwd a => match w src with
      | some bit =>
        let r := δ a bit ((w rhs).getD false)
        wordLockAction src rhs dst (some r.2) 1 (.fwd r.1)
      | none => wordLockAction src rhs dst none (-1) (.bwd a₀)
    | .bwd _ => match w src with
      | some _ => wordLockAction src rhs dst none (-1) (.bwd a₀)
      | none => wordLockAction src rhs dst none 1 (.done a₀)
    | .done a => wordLockAction src rhs dst none 0 (.done a)

/-- A lockstep configuration with a written destination prefix and a common head offset. -/
private def wordLockCfg {k : ℕ} {A : Type} {x : List Bool}
    (src rhs dst : Fin k) (d : Cfg k Bool (ScanPhase A) x)
    (out : List Bool) (q : ScanPhase A) (n : ℕ) (h : ℤ) : Cfg k Bool (ScanPhase A) x :=
  { d with
    state := some q
    workTapes := fun j p =>
      if j = dst ∧ d.workTapePos j ≤ p ∧ p < d.workTapePos j + (n : ℤ)
        then FinTM.bufferTape out (p - d.workTapePos j) else d.workTapes j p
    workTapePos := fun j => d.workTapePos j +
      if j = src ∨ j = rhs ∨ j = dst then h else 0}

/-- At the forward boundary no source cell has yet been overwritten, even with aliases. -/
private theorem wordLockCfg_read_fwd {k : ℕ} {A : Type} {x : List Bool}
    (src rhs dst j : Fin k) (d : Cfg k Bool (ScanPhase A) x) (out w : List Bool)
    (q : ScanPhase A) (n : ℕ) (hj : j = src ∨ j = rhs ∨ j = dst)
    (hn : n ≤ w.length) (hw : WordAt d j w) :
    (wordLockCfg src rhs dst d out q n n).workTapeSymbols j = FinTM.bufferTape w n := by
  rw [Cfg.workTapeSymbols_eq]
  simp only [wordLockCfg, if_pos hj, lt_self_iff_false, and_false, if_false]
  exact ((wordAt_iff d j w).mp hw) n (by omega) (by exact_mod_cast hn)

/-- A full destination patch keeps its delimiters; an aliased source reads the output word. -/
private theorem wordLockCfg_read_full {k : ℕ} {A : Type} {x : List Bool}
    (src rhs dst j : Fin k) (d : Cfg k Bool (ScanPhase A) x) (out w : List Bool)
    (q : ScanPhase A) (h : ℤ) (hj : j = src ∨ j = rhs ∨ j = dst)
    (hlen : out.length = w.length) (hlo : -1 ≤ h) (hhi : h ≤ (w.length : ℤ))
    (hw : WordAt d j w) :
    (wordLockCfg src rhs dst d out q w.length h).workTapeSymbols j =
      FinTM.bufferTape (if j = dst then out else w) h := by
  rw [Cfg.workTapeSymbols_eq]
  simp only [wordLockCfg, if_pos hj]
  by_cases hd : j = dst
  · have hp := wordPatch_frame (d.workTapes j) (d.workTapePos j) w out hlen
      ((wordAt_iff d j w).mp hw) h hlo (by simpa only [hlen] using hhi)
    simpa only [wordPatch_apply, hlen, hd, true_and, if_true] using hp
  · simp only [hd, false_and, if_false]
    exact ((wordAt_iff d j w).mp hw) h hlo hhi

/-- One forward action extends the output prefix by exactly its next bit.

**Proof sketch.** Apply the action-field equation to the current prefix configuration.
`catalog_write_take` identifies the single destination update with the next prefix patch;
the other cells and stationary fields agree directly. The common head move advances the
three selected heads together. -/
private theorem wordLockCfg_write {k : ℕ} {A : Type} {x : List Bool}
    (src rhs dst : Fin k) (d : Cfg k Bool (ScanPhase A) x) (out : List Bool)
    (q q' : ScanPhase A) (r : ℕ) (hr : r < out.length) :
    (wordLockAction src rhs dst (some out[r]) 1 q').apply
        (wordLockCfg src rhs dst d out q r r) =
      wordLockCfg src rhs dst d out q' (r + 1) (r + 1) := by
  rw [wordLockAction_apply]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases hj : j = dst
    · subst j
      simp only [wordLockCfg, if_true, true_and, or_true]
      exact catalog_write_take (d.workTapes dst) (d.workTapePos dst) out r hr
    · simp only [wordLockCfg, hj, if_false, false_and]
  · funext j
    by_cases hj : j = src ∨ j = rhs ∨ j = dst
    · simp only [wordLockCfg, hj, if_true, SignType.coe_one, Nat.cast_add, Nat.cast_one]
      omega
    · simp only [wordLockCfg, hj, if_false, add_zero]
  · rfl

/-- A non-writing lockstep action translates only the common head offset. -/
private theorem wordLockCfg_move {k : ℕ} {A : Type} {x : List Bool}
    (src rhs dst : Fin k) (d : Cfg k Bool (ScanPhase A) x) (out : List Bool)
    (q q' : ScanPhase A) (n : ℕ) (h : ℤ) (m : SignType) :
    (wordLockAction src rhs dst none m q').apply
        (wordLockCfg src rhs dst d out q n h) =
      wordLockCfg src rhs dst d out q' n (h + (m : ℤ)) := by
  rw [wordLockAction_apply]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    simp only [ite_self]
    rfl
  · funext j
    by_cases hj : j = src ∨ j = rhs ∨ j = dst <;>
      simp only [wordLockCfg, hj, if_true, if_false, add_zero, add_assoc]
  · rfl

/-- The framed lockstep sweep computes any transducer whose successive states and bits
satisfy the supplied cell equations. No scratch-blankness hypothesis is needed.

**Proof sketch.** `catalog_trace_run` joins the forward prefix configurations and the
return configurations. `wordLockCfg_read_fwd` reads each input before its cell can be written;
`wordLockCfg_write` extends the prefix using `catalog_write_take`. The full-patch reader
uses `wordPatch_frame`, so an aliased guide remains a delimited nonblank word during the
return. `catalogTrace_eq` gives the endpoint and excludes earlier exits. The general
`MultiTapeTM.workTapePos_runFrom_mem_Icc` bounds displacement by the linear running time. -/
private theorem wordLock_run {k : ℕ} {A : Type} {x : List Bool}
    (src rhs dst : Fin k) (δ : A → Bool → Bool → A × Bool) (a₀ : A)
    (u v out : List Bool) (c : ℕ → A) (hv : v.length = u.length)
    (ho : out.length = u.length) (hc : c 0 = a₀)
    (hδ : ∀ r (hr : r < u.length),
      δ (c r) (u[r]) (v[r]'(by omega)) = (c (r + 1), (out[r]'(by omega))))
    (d : Cfg k Bool (ScanPhase A) x) (hd : d.state = some (.fwd a₀))
    (hu : WordAt d src u) (hw : WordAt d rhs v) :
    ReachesWithin (wordLockTM src rhs dst δ a₀) d {some (.done a₀)}
      (2 * (u.length + 1)) (2 * (u.length + 1))
      {d with state := some (.done a₀), workTapes := wordWrite d dst out} := by
  let M := wordLockTM src rhs dst δ a₀
  let F := fun r => wordLockCfg src rhs dst d out (.fwd (c r)) r r
  let R := fun r : ℕ => wordLockCfg src rhs dst d out (.bwd a₀) u.length ((r : ℤ) - 1)
  let D := wordLockCfg src rhs dst d out (.done a₀) u.length 0
  have hF0 : F 0 = d := by
    apply Cfg.ext
    · simpa only [F, wordLockCfg, hc] using hd.symm
    · rfl
    · funext j z
      simp only [F, wordLockCfg, Nat.cast_zero, add_zero]
      split_ifs with h
      · omega
      · rfl
    · funext j
      simp only [F, wordLockCfg, Nat.cast_zero, ite_self, add_zero]
    · rfl
  have hF : ∀ r < u.length, M.step (F r) = F (r + 1) := by
    intro r hr
    have hs : (F r).workTapeSymbols src = some u[r] := by
      simpa only [F, FinTM.bufferTape_nat, List.getElem?_eq_getElem hr] using
        wordLockCfg_read_fwd src rhs dst src d out u (.fwd (c r)) r
          (Or.inl rfl) hr.le hu
    have ht : (F r).workTapeSymbols rhs = some (v[r]'(by omega)) := by
      simpa only [F, FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega : r < v.length)] using
        wordLockCfg_read_fwd src rhs dst rhs d out v (.fwd (c r)) r
          (Or.inr (Or.inl rfl)) (by omega) hw
    rw [MultiTapeTM.step_of_some (show (F r).state = some (.fwd (c r)) from rfl)]
    simp only [M, wordLockTM, hs, ht, Option.getD_some, hδ r hr]
    exact wordLockCfg_write src rhs dst d out (.fwd (c r)) (.fwd (c (r + 1))) r (by omega)
  have hturn : M.step (F u.length) = R u.length := by
    have hs : (F u.length).workTapeSymbols src = none := by
      simpa only [F, FinTM.bufferTape_nat, List.getElem?_length] using
        wordLockCfg_read_fwd src rhs dst src d out u (.fwd (c u.length)) u.length
          (Or.inl rfl) le_rfl hu
    rw [MultiTapeTM.step_of_some (show (F u.length).state = some (.fwd (c u.length)) from rfl)]
    simp only [M, wordLockTM, hs]
    simpa only [F, R, SignType.coe_neg_one, sub_eq_add_neg] using
      wordLockCfg_move src rhs dst d out (.fwd (c u.length)) (.bwd a₀) u.length u.length (-1)
  have hR : ∀ r < u.length, M.step (R (r + 1)) = R r := by
    intro r hr
    let guide := if src = dst then out else u
    have hg : guide.length = u.length := by
      dsimp only [guide]
      split_ifs <;> first | exact ho | rfl
    have hpos : ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) := by omega
    have hs : (R (r + 1)).workTapeSymbols src = some (guide[r]'(by omega)) := by
      have hp := wordLockCfg_read_full src rhs dst src d out u (.bwd a₀) r
        (Or.inl rfl) ho (by omega) (by omega) hu
      change (wordLockCfg src rhs dst d out (.bwd a₀) u.length r).workTapeSymbols src =
        FinTM.bufferTape guide r at hp
      rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega : r < guide.length)] at hp
      simpa only [R, hpos] using hp
    rw [MultiTapeTM.step_of_some (show (R (r + 1)).state = some (.bwd a₀) from rfl)]
    simp only [M, wordLockTM, hs]
    rw [wordLockCfg_move]
    dsimp only [R]
    congr 1
    simp only [SignType.coe_neg_one]
    omega
  have hentry : M.step (R 0) = D := by
    have hs : (R 0).workTapeSymbols src = none := by
      simpa only [R, Nat.cast_zero, zero_sub, FinTM.bufferTape_left] using
        wordLockCfg_read_full src rhs dst src d out u (.bwd a₀) (-1)
          (Or.inl rfl) ho le_rfl (by omega) hu
    rw [MultiTapeTM.step_of_some (show (R 0).state = some (.bwd a₀) from rfl)]
    simp only [M, wordLockTM, hs]
    simpa only [R, D, Nat.cast_zero, zero_sub, SignType.coe_one, neg_add_cancel] using
      wordLockCfg_move src rhs dst d out (.bwd a₀) (.done a₀) u.length (-1) 1
  have hD : M.step D = D := by
    rw [MultiTapeTM.step_of_some (show D.state = some (.done a₀) from rfl)]
    simp only [M, wordLockTM]
    simpa only [D, SignType.coe_zero, add_zero] using
      wordLockCfg_move src rhs dst d out (.done a₀) (.done a₀) u.length 0 0
  have htrace (t : ℕ) : M.runFrom d t = catalogTrace F R D u.length t := by
    simpa only [hF0] using catalog_trace_run M F R D u.length hF hturn hR hentry hD t
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨2 * u.length + 2, by omega, ?_, ?_, ?_⟩
  · intro t ht
    rw [htrace, catalogTrace_eq]
    split_ifs with h₁ h₂
    · simp only [F, wordLockCfg, Set.mem_singleton_iff]
      intro h
      cases h
    · simp only [R, wordLockCfg, Set.mem_singleton_iff]
      intro h
      cases h
    · omega
  · intro t ht j
    have hp := M.workTapePos_runFrom_mem_Icc d t j
    rw [Finset.mem_Icc] at hp
    rw [abs_le]
    constructor <;> omega
  · rw [htrace, catalogTrace_eq, if_neg (by omega), if_neg (by omega)]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp only [D, wordLockCfg, wordWrite_apply, ho]
    · funext j
      simp only [D, wordLockCfg, ite_self, add_zero]
    · rfl

/-- One ripple-carry cell, optionally complementing the second operand for subtraction. -/
private def wordRippleStep (flip : Bool) (carry u v : Bool) : Bool × Bool :=
  let bit := if flip then !v else v
  (Bool.atLeastTwo u bit carry, u ^^ (bit ^^ carry))

/-- The framed ripple row adds the optionally complemented second word and an initial carry.

**Proof sketch.** Instantiate `wordLock_run` with `BitVec.carry` as its state sequence.
`BitVec.carry_zero` supplies the entry; `BitVec.carry_succ` is the state equation, and
`BitVec.getLsbD_add_add_bool` is the output equation. Complemented input bits are read by
`BitVec.getLsbD_not`, only below the fixed word width. -/
private theorem wordRipple_run {k W : ℕ} {x : List Bool} (src rhs dst : Fin k)
    (flip carry : Bool) (u v : BitVec W) (d : Cfg k Bool (ScanPhase Bool) x)
    (hd : d.state = some (.fwd carry)) (hu : WordAt d src (bvBits u))
    (hv : WordAt d rhs (bvBits v)) :
    ReachesWithin (wordLockTM src rhs dst (wordRippleStep flip) carry) d {some (.done carry)}
      (2 * (W + 1)) (2 * (W + 1))
      { d with
        state := some (.done carry)
        workTapes := wordWrite d dst (bvBits
          (u + (if flip then ~~~v else v) + BitVec.setWidth W (BitVec.ofBool carry)))} := by
  let z := if flip then ~~~v else v
  have hstep : ∀ r (hr : r < (bvBits u).length),
      wordRippleStep flip (BitVec.carry r u z carry) ((bvBits u)[r])
        ((bvBits v)[r]'(by simpa only [bvBits_length] using hr)) =
      (BitVec.carry (r + 1) u z carry,
        (bvBits (u + z + BitVec.setWidth W (BitVec.ofBool carry)))[r]'(by
          simpa only [bvBits_length] using hr)) := by
    intro r hr
    have hrW : r < W := by simpa only [bvBits_length] using hr
    have hz : z.getLsbD r = if flip then !(v.getLsbD r) else v.getLsbD r := by
      cases flip <;> simp only [z, Bool.false_eq_true, if_true, if_false, BitVec.getLsbD_not,
        hrW, decide_true, Bool.true_and]
    simp only [bvBits_def, List.getElem_ofFn, wordRippleStep]
    apply Prod.ext
    · rw [BitVec.carry_succ, hz]
    · rw [BitVec.getLsbD_add_add_bool hrW, hz]
  simpa only [bvBits_length] using
    wordLock_run src rhs dst (wordRippleStep flip) carry (bvBits u) (bvBits v)
      (bvBits (u + z + BitVec.setWidth W (BitVec.ofBool carry)))
      (fun r => BitVec.carry r u z carry) (by simp only [bvBits_length])
      (by simp only [bvBits_length]) BitVec.carry_zero hstep d hd hu hv

/-! ## Arithmetic modulo `2^W` -/

/-- **Addition modulo `2^W`.** From the entry, with `u` on tape `0`, `v` on tape `1`, a word of
`W` cells on tape `2` and blank scratch tapes, the row writes `u + v` on tape `2` and stops at its
exit within `C·(W + 1)` steps, every head within `C·(W + 1)` cells and back where it started.
[AB09, Exercise 1.9]

**Proof sketch.** Apply the framed `wordRipple_run` with an uncomplemented second operand
and initial carry false. Its `wordLock_run` sweep writes the low sum bits and returns all
three heads. The state and bit equations are `BitVec.carry_succ` and
`BitVec.getLsbD_add_add_bool`; the final carry is discarded. The bound uses `C = 2`.
-/
theorem exists_wordAddTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u + v)) } := by
  refine ⟨ScanPhase Bool, inferInstance, inferInstance,
    wordLockTM 0 1 2 (wordRippleStep false) false, .fwd false, .done false, 2, ?_⟩
  intro x W u v w d hd hu hv _ _ _
  have h := wordRipple_run 0 1 2 false false u v d hd hu hv
  simpa [BitVec.ofBool_false] using h

/-- **Subtraction modulo `2^W`.** As `Turing.exists_wordAddTM`, writing `u - v`.
[AB09, Exercise 1.9]

**Proof sketch.** Apply the same framed `wordRipple_run` with complemented second-operand
bits and initial carry true. `BitVec.neg_eq_not_add` identifies the computed word with
`u - v`, including underflow modulo the width. The shared sweep returns every head and
uses the same constant `C = 2`. -/
theorem exists_wordSubTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u - v)) } := by
  refine ⟨ScanPhase Bool, inferInstance, inferInstance,
    wordLockTM 0 1 2 (wordRippleStep true) true, .fwd true, .done true, 2, ?_⟩
  intro x W u v w d hd hu hv _ _ _
  have hone : BitVec.setWidth W (BitVec.ofBool true) = (1#W) := by
    rw [BitVec.ofBool_true]
    exact BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1)
  have he : u + ~~~v + BitVec.setWidth W (BitVec.ofBool true) = u - v := by
    rw [hone, BitVec.add_assoc, ← BitVec.neg_eq_not_add, ← BitVec.sub_eq_add_neg]
  have h := wordRipple_run 0 1 2 true true u v d hd hu hv
  simpa only [if_true, he] using h

/-! ## Shared framed phase adapters -/

/-- State renaming does not affect a word held at a work head. -/
private theorem wordAt_mapState {k : ℕ} {S T : Type} {x : List Bool}
    (d : Cfg k Bool S x) (f : S → T) (j : Fin k) (w : List Bool) :
    WordAt (d.mapState f) j w ↔ WordAt d j w := by
  simp only [wordAt_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]

/-- A same-width word write keeps the destination delimited. -/
private theorem wordAt_write {k : ℕ} {S : Type} {x : List Bool} (d : Cfg k Bool S x)
    (j : Fin k) (u v : List Bool) (hlen : v.length = u.length) (hw : WordAt d j u) :
    WordAt {d with workTapes := wordWrite d j v} j v := by
  rw [wordAt_iff]
  intro z hlo hhi
  have h := wordPatch_frame (d.workTapes j) (d.workTapePos j) u v hlen
    ((wordAt_iff d j u).mp hw) z hlo hhi
  simpa only [wordWrite_apply, wordPatch_apply, true_and] using h

/-- A public phase-host run is a segment avoiding any designated exit in another phase.

**Proof sketch.** `phaseHostTM_run` supplies the tagged prefix and the stationary dispatch.
`Cfg.mapState_sigma_state_ne` excludes the other phase's exit. State renaming preserves
every head, so the phase's head relation holds through the dispatch. These segments compose
with the library's `Segment.trans`. -/
private theorem wordPhase_segment {k : ℕ} {I : Type} {Ph : I → Type} {x : List Bool}
    (Mf : (i : I) → MultiTapeTM k Bool (Ph i)) (q₀ : Σ i : I, Ph i)
    (red : (i : I) → Ph i → Option (Σ j : I, Ph j)) (p : I)
    (c c' : Cfg k Bool (Ph p) x) (T : ℕ) (s' : Ph p) (next exit : Σ i : I, Ph i)
    (P : (Fin k → ℤ) → Prop) (hrun : (Mf p).runFrom c T = c')
    (hs : c'.state = some s') (hr : red p s' = some next)
    (hg : ∀ u < T, ∀ s, ((Mf p).runFrom c u).state = some s → red p s = none)
    (hp : p ≠ exit.1) (he : ∀ u ≤ T, P ((Mf p).runFrom c u).workTapePos) :
    Segment (phaseHostTM Mf q₀ red) {some exit} P (c.mapState (fun s : Ph p => (⟨p, s⟩ : Σ i : I, Ph i)))
      (c'.mapState fun _ => next) (T + 1) := by
  have h := phaseHostTM_run Mf q₀ red p c c' T hrun s' hs next hr hg
  apply (segment_iff _ _ _ _ _ _).mpr
  refine ⟨h.2, ?_, ?_⟩
  · intro u hu
    rw [h.1 u (by omega)]
    exact Cfg.mapState_sigma_state_ne (Ph := Ph) p exit hp ((Mf p).runFrom c u)
  · intro u hu
    by_cases hle : u ≤ T
    · rw [h.1 u hle]
      have hpos : (((Mf p).runFrom c u).mapState (fun s : Ph p => (⟨p, s⟩ : Σ i : I, Ph i))).workTapePos =
          ((Mf p).runFrom c u).workTapePos := by
        funext j
        exact Cfg.mapState_workTapePos _ _ j
      rw [hpos]
      exact he u hle
    · have hu' : u = T + 1 := by omega
      subst u
      rw [h.2]
      have hpos : (c'.mapState fun _ => next).workTapePos = c'.workTapePos := by
        funext j
        exact Cfg.mapState_workTapePos _ _ j
      rw [hpos, ← hrun]
      exact he T le_rfl

/-- A row's exit cut supplies the phase-host guard when only its exits redirect. -/
private theorem wordPhase_guard {k : ℕ} {I : Type} {Ph : I → Type} {x : List Bool}
    (Mf : (i : I) → MultiTapeTM k Bool (Ph i))
    (red : (i : I) → Ph i → Option (Σ j : I, Ph j)) (p : I)
    (c : Cfg k Bool (Ph p) x) (T : ℕ) (X : Set (Option (Ph p)))
    (hcut : ∀ t < T, ((Mf p).runFrom c t).state ∉ X)
    (hred : ∀ q, some q ∉ X → red p q = none) :
    ∀ t < T, ∀ q, ((Mf p).runFrom c t).state = some q → red p q = none := by
  intro t ht q hq
  exact hred q (fun hX => hcut t ht (hq.symm ▸ hX))

/-- Two writes of equal-width words on one tape retain only the last word. -/
private theorem wordWrite_twice {k : ℕ} {S : Type} {x : List Bool} (d : Cfg k Bool S x)
    (j : Fin k) (u v : List Bool) (hlen : v.length = u.length) :
    wordWrite {d with workTapes := wordWrite d j u} j v = wordWrite d j v := by
  funext r z
  by_cases hr : r = j
  · subst r
    simpa only [wordWrite_apply, wordPatch_apply, true_and] using
      congrFun (wordPatch_twice (d.workTapes j) (d.workTapePos j) u v hlen) z
  · simp only [wordWrite_apply, hr, false_and, if_false]

/-- One fixed move of the selected heads. The catalog supplies its action primitives but no
standalone fixed-distance work-head row; this one-step leaf is used between the existing scan rows. -/
private def wordMoveTM {k : ℕ} (src rhs dst : Fin k) (m : SignType) : MultiTapeTM k Bool (ScanPhase Bool) where
  q₀ := .fwd false
  tr := fun q _ _ => match q with
    | .fwd _ => wordLockAction src rhs dst none m (.done false)
    | _ => wordLockAction src rhs dst none 0 (.done false)

/-- The fixed move takes one step and preserves every cell and every other head.

**Proof sketch.** The action-field lemma identifies the unique transition from the entry.
Before its one-step exit the only possible time is zero, where the entry is outside the
exit set. The machine model's displacement-from-time bound gives radius one. -/
private theorem wordMove_run {k : ℕ} {x : List Bool} (src rhs dst : Fin k) (m : SignType)
    (d : Cfg k Bool (ScanPhase Bool) x) (hd : d.state = some (.fwd false)) :
    ReachesWithin (wordMoveTM src rhs dst m) d {some (.done false)} 1 1
      { d with
        state := some (.done false)
        workTapePos := fun r => d.workTapePos r + if r = src ∨ r = rhs ∨ r = dst then (m : ℤ) else 0 } := by
  have hstep : (wordMoveTM src rhs dst m).step d =
      { d with
        state := some (.done false)
        workTapePos := fun r => d.workTapePos r + if r = src ∨ r = rhs ∨ r = dst then (m : ℤ) else 0 } := by
    rw [MultiTapeTM.step_of_some hd]
    simp only [wordMoveTM, wordLockAction_apply, ite_self]
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨1, le_rfl, ?_, ?_, ?_⟩
  · intro t ht
    have ht₀ : t = 0 := by omega
    subst t
    rw [MultiTapeTM.runFrom_zero, hd]
    simp only [Set.mem_singleton_iff]
    intro h
    cases h
  · intro t ht r
    have hp := (wordMoveTM src rhs dst m).workTapePos_runFrom_mem_Icc d t r
    rw [Finset.mem_Icc] at hp
    rw [abs_le]
    constructor <;> omega
  · rw [MultiTapeTM.runFrom_one, hstep]

/-- A linear-time phase begun within the word's span stays in one common linear envelope.

**Proof sketch.** The machine model bounds each head's displacement by elapsed time.
The triangle inequality adds the initial offset, at most `W`. A row of at most `2*(W+1)`
steps therefore lies within `3*(W+1)` of the original frame, including its dispatch. -/
private theorem wordPhase_bounded {k : ℕ} {I : Type} {Ph : I → Type} {x : List Bool}
    (Mf : (i : I) → MultiTapeTM k Bool (Ph i)) (q₀ : Σ i : I, Ph i)
    (red : (i : I) → Ph i → Option (Σ j : I, Ph j)) (p : I)
    (c c' : Cfg k Bool (Ph p) x) (T W : ℕ) (s' : Ph p) (next exit : Σ i : I, Ph i)
    (origin : Fin k → ℤ) (hrun : (Mf p).runFrom c T = c')
    (hs : c'.state = some s') (hr : red p s' = some next)
    (hg : ∀ t < T, ∀ q, ((Mf p).runFrom c t).state = some q → red p q = none)
    (hp : p ≠ exit.1) (hT : T ≤ 2 * (W + 1))
    (hpos : ∀ j, |c.workTapePos j - origin j| ≤ (W : ℤ)) :
    Segment (phaseHostTM Mf q₀ red) {some exit}
      (fun heads => ∀ j, |heads j - origin j| ≤ (3 * (W + 1) : ℕ))
      (c.mapState (fun q : Ph p => (⟨p, q⟩ : Σ i, Ph i))) (c'.mapState fun _ => next) (T + 1) := by
  apply wordPhase_segment Mf q₀ red p c c' T s' next exit _ hrun hs hr hg hp
  intro t ht j
  have h := (Mf p).workTapePos_runFrom_mem_Icc c t j
  rw [Finset.mem_Icc] at h
  have hdist : |((Mf p).runFrom c t).workTapePos j - c.workTapePos j| ≤ (t : ℤ) :=
    abs_le.mpr ⟨by omega, by omega⟩
  calc
    |((Mf p).runFrom c t).workTapePos j - origin j| =
        |(((Mf p).runFrom c t).workTapePos j - c.workTapePos j) + (c.workTapePos j - origin j)| := by
      congr 1
      ring
    _ ≤ |((Mf p).runFrom c t).workTapePos j - c.workTapePos j| + |c.workTapePos j - origin j| := abs_add_le _ _
    _ ≤ (t : ℤ) + W := add_le_add hdist (hpos j)
    _ ≤ (3 * (W + 1) : ℕ) := by omega

/-! ## Shift-and-add multiplication -/

/-- The partial product uses precisely the multiplier's first `r` low bits. -/
private def wordMulAcc {W : ℕ} (u v : BitVec W) (r : ℕ) : BitVec W :=
  u * ((v.setWidth r).setWidth W)

/-- One more multiplier bit adds the corresponding shifted multiplicand. -/
private theorem wordMulAcc_succ {W : ℕ} (u v : BitVec W) (r : ℕ) :
    wordMulAcc u v (r + 1) = wordMulAcc u v r + if v.getLsbD r then u <<< r else 0 := by
  simp only [wordMulAcc, BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_add_twoPow,
    BitVec.mul_add, BitVec.and_twoPow]
  cases v.getLsbD r <;> simp [BitVec.mul_twoPow_eq_shiftLeft]

/-- A forward one-cell delay is a left shift of the little-endian word.

**Proof sketch.** The emitted list starts with false, then the old low bits, truncated to
the original length by `zipWith`. Its first bit and successor bits agree with the core's
`getLsbD_shiftLeft` equation, including the empty word. -/
private theorem wordShiftUp_bits {W : ℕ} (u : BitVec W) :
    List.zipWith (fun (_ b : Bool) => b) (bvBits u) (false :: bvBits u) = bvBits (u <<< 1) := by
  apply List.ext_getElem
  · simp only [List.length_zipWith, List.length_cons, bvBits_length]
    omega
  · intro i hi hi'
    rw [List.getElem_zipWith]
    cases i with
    | zero => simp [bvBits_def]
    | succ i => simp [bvBits_def]

/-- Three distinct probe verdicts encode false, true, and the right delimiter. -/
private def wordProbeState : Option Bool → ScanPhase Bool
  | some b => .done b
  | none => .bwd false

/-- A stationary one-cell read. The catalog has scans but no leaf returning the currently
scanned optional symbol; the phase host needs this three-way verdict at the multiplier head. -/
private def wordProbeTM {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (ScanPhase Bool) where
  q₀ := .fwd false
  tr := fun q _ tapes => wordLockAction i i i none 0
    (match q with
      | .fwd _ => wordProbeState (tapes i)
      | _ => q)

/-- The stationary probe returns the current optional bit in exactly one step. -/
private theorem wordProbe_run {k : ℕ} {x : List Bool} (i : Fin k)
    (d : Cfg k Bool (ScanPhase Bool) x) (hd : d.state = some (.fwd false)) :
    (wordProbeTM i).runFrom d 1 =
      {d with state := some (wordProbeState (d.workTapes i (d.workTapePos i)))} := by
  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some hd]
  simp only [wordProbeTM, Cfg.workTapeSymbols_eq, wordLockAction_apply,
    ite_self, SignType.coe_zero, add_zero]

/-- The multiplier's finite row schedule; the probe supplies the loop condition. -/
private inductive WordMulStage where
  | copy | zero | probe | add | shift | advance | clear | rewind | done
  deriving DecidableEq, Fintype

/-- Only the clear and rewind catalog rows need distinct local state alphabets. -/
private def wordMulPh : WordMulStage → Type
  | .clear => SweepPhase
  | .rewind => RewindPhase
  | _ => ScanPhase Bool

/-- Every multiplier row has finite control. -/
private instance wordMulPh_fintype (p : WordMulStage) : Fintype (wordMulPh p) := by
  cases p <;> dsimp only [wordMulPh] <;> infer_instance

/-- Equality of each row's control state is decidable. -/
private instance wordMulPh_decidableEq (p : WordMulStage) : DecidableEq (wordMulPh p) := by
  cases p <;> dsimp only [wordMulPh] <;> infer_instance

/-- The multiplier reuses the framed sweeps, catalog shift, scratch clear, and prefix rewind. -/
private def wordMulRows : (p : WordMulStage) → MultiTapeTM 5 Bool (wordMulPh p)
  | .copy => wordLockTM 0 0 3 (fun (_ : Bool) bit _ => (false, bit)) false
  | .zero => wordLockTM 0 0 2 (fun (_ : Bool) _ _ => (false, false)) false
  | .probe => wordProbeTM 1
  | .add => wordLockTM 3 2 2 (wordRippleStep false) false
  | .shift => scanTM 5 3 (scanShift id (fun (_ bit : Bool) => bit)) scanKeep false
  | .advance => wordMoveTM 1 1 1 1
  | .clear => clearTM 5 3
  | .rewind => rewindTM 5 1
  | .done => wordMoveTM 1 1 1 0

/-- Only the probe branches; all completed arithmetic rows return to its next iteration. -/
private def wordMulRed : (p : WordMulStage) → wordMulPh p → Option (Σ p, wordMulPh p)
  | .copy, .done false => some ⟨.zero, .fwd false⟩
  | .zero, .done false => some ⟨.probe, .fwd false⟩
  | .probe, .done true => some ⟨.add, .fwd false⟩
  | .probe, .done false => some ⟨.shift, .fwd false⟩
  | .probe, .bwd false => some ⟨.clear, .sweep⟩
  | .add, .done false => some ⟨.shift, .fwd false⟩
  | .shift, .done _ => some ⟨.advance, .fwd false⟩
  | .advance, .done false => some ⟨.probe, .fwd false⟩
  | .clear, .done => some ⟨.rewind, .start⟩
  | .rewind, .done => some ⟨.done, .done false⟩
  | _, _ => none

/-- The public phase host supplies the multiplier's loop and all stationary dispatches. -/
private def wordMulTM : MultiTapeTM 5 Bool (Σ p, wordMulPh p) :=
  phaseHostTM wordMulRows ⟨.copy, .fwd false⟩ wordMulRed

/-- The catalog exits which may dispatch out of each multiplier row. -/
private def wordMulExit : (p : WordMulStage) → Set (Option (wordMulPh p))
  | .probe => {some (.done true), some (.done false), some (.bwd false)}
  | .shift => {some (.done true), some (.done false)}
  | .clear => {some .done}
  | .rewind => {some .done}
  | .done => ∅
  | .copy | .zero | .add | .advance => {some (.done false)}

/-- A multiplier row redirects only from one of its stated exits. -/
private theorem wordMulRed_none (p : WordMulStage) (q : wordMulPh p)
    (h : some q ∉ wordMulExit p) : wordMulRed p q = none := by
  cases p <;> cases q <;> try rfl
  all_goals simp_all [wordMulExit, wordMulRed]
  all_goals rename_i b; cases b <;> simp_all

/-- The multiplier frame patches just the destination and the single scratch word. -/
private def wordMulTapes {S : Type} {x : List Bool} {W : ℕ} (d : Cfg 5 Bool S x)
    (acc shifted : BitVec W) : Fin 5 → ℤ → Option Bool := fun j z =>
  if j = 2 then wordPatch (d.workTapes 2) (d.workTapePos 2) (bvBits acc) z
  else if j = 3 then wordPatch (d.workTapes 3) (d.workTapePos 3) (bvBits shifted) z
  else d.workTapes j z

/-- Only the multiplier-input head has a nonzero offset at the seams of its loop. -/
private def wordMulHeads {S : Type} {x : List Bool} (d : Cfg 5 Bool S x) (r : ℕ) : Fin 5 → ℤ :=
  fun j => d.workTapePos j + if j = 1 then (r : ℤ) else 0

/-- A canonical loop configuration carries the partial product, shifted word, and bit index. -/
private def wordMulCfg {S T : Type} {x : List Bool} {W : ℕ} (d : Cfg 5 Bool S x)
    (acc shifted : BitVec W) (r : ℕ) (q : T) : Cfg 5 Bool T x where
  state := some q
  inputPos := d.inputPos
  workTapes := wordMulTapes d acc shifted
  workTapePos := wordMulHeads d r
  output := d.output

/-- Renaming a loop configuration tags only its state. -/
private theorem wordMulCfg_mapState {S T U : Type} {x : List Bool} {W : ℕ}
    (d : Cfg 5 Bool S x) (acc shifted : BitVec W) (r : ℕ) (q : T) (f : T → U) :
    (wordMulCfg d acc shifted r q).mapState f = wordMulCfg d acc shifted r (f q) := by
  rw [Cfg.mapState_eq]
  rfl

/-- Replacing either canonical word keeps just its latest value.

**Proof sketch.** Split on the two distinct writable tapes. On the updated tape,
`wordPatch_twice` removes the old same-width patch; the other tape and every frame cell
are unchanged. The loop head is on tape one, so neither write is offset. -/
private theorem wordMulCfg_write {S T : Type} {x : List Bool} {W : ℕ} (d : Cfg 5 Bool S x)
    (acc shifted v : BitVec W) (r : ℕ) (q : T) (i : Fin 5) (hi : i = 2 ∨ i = 3) :
    wordWrite (wordMulCfg d acc shifted r q) i (bvBits v) =
      wordMulTapes d (if i = 2 then v else acc) (if i = 3 then v else shifted) := by
  rcases hi with rfl | rfl
  · funext j z
    by_cases hj : j = 2
    · subst j
      simpa [wordWrite_apply, wordMulCfg, wordMulHeads, wordMulTapes, wordPatch_apply] using
        congrFun (wordPatch_twice (d.workTapes 2) (d.workTapePos 2) (bvBits acc) (bvBits v)
          (by simp only [bvBits_length])) z
    · simp [wordWrite_apply, wordMulCfg, wordMulHeads, wordMulTapes, hj]
  · funext j z
    by_cases hj : j = 3
    · subst j
      simpa [wordWrite_apply, wordMulCfg, wordMulHeads, wordMulTapes, wordPatch_apply] using
        congrFun (wordPatch_twice (d.workTapes 3) (d.workTapePos 3) (bvBits shifted) (bvBits v)
          (by simp only [bvBits_length])) z
    · simp [wordWrite_apply, wordMulCfg, wordMulHeads, wordMulTapes, hj]

/-- Both patched words remain delimited at every loop seam.

**Proof sketch.** For the destination use `wordPatch_frame` on its original delimited word.
For scratch, blankness supplies every cell outside the patch; `bufferTape_eq_none_of_not_mem`
identifies those cells with the word's blank buffer. The tape-one head offset affects neither. -/
private theorem wordMulCfg_words {S T : Type} {x : List Bool} {W : ℕ} (d : Cfg 5 Bool S x)
    (w : List Bool) (hw : WordAt d 2 w) (hlen : w.length = W) (hb : ScratchBlank d)
    (acc shifted : BitVec W) (r : ℕ) (q : T) :
    WordAt (wordMulCfg d acc shifted r q) 2 (bvBits acc) ∧
      WordAt (wordMulCfg d acc shifted r q) 3 (bvBits shifted) := by
  constructor
  · rw [wordAt_iff]
    intro p hlo hhi
    have h := wordPatch_frame (d.workTapes 2) (d.workTapePos 2) w (bvBits acc)
      (by simp only [bvBits_length, hlen]) ((wordAt_iff d 2 w).mp hw) p hlo hhi
    simpa [wordMulCfg, wordMulHeads, wordMulTapes] using h
  · rw [wordAt_iff]
    intro p hlo hhi
    have hz := (scratchBlank_iff d).mp hb 3 (by decide)
    simp only [wordMulCfg, wordMulHeads, wordMulTapes]
    simp only [show (3 : Fin 5) ≠ 1 by decide, show (3 : Fin 5) ≠ 2 by decide,
      if_false, if_true, add_zero, wordPatch_apply]
    split_ifs with hin
    · rw [add_sub_cancel_left]
    · rw [hz]
      exact (FinTM.bufferTape_eq_none_of_not_mem (bvBits shifted) (by omega)).symm

/-- A canonical loop seam lies within `W` of its original frame while `r ≤ W`. -/
private theorem wordMulCfg_pos {S T : Type} {x : List Bool} {W : ℕ} (d : Cfg 5 Bool S x)
    (acc shifted : BitVec W) (r : ℕ) (q : T) (hr : r ≤ W) :
    ∀ j, |(wordMulCfg d acc shifted r q).workTapePos j - d.workTapePos j| ≤ (W : ℤ) := by
  intro j
  by_cases hj : j = 1
  · simpa [wordMulCfg, wordMulHeads, hj] using (show (r : ℤ) ≤ W by exact_mod_cast hr)
  · simp [wordMulCfg, wordMulHeads, hj]

/-- A verified returning row becomes a bounded segment in the multiplier's public host.

**Proof sketch.** Extract the first-exit time from `ReachesWithin`, use `wordMulRed_none`
to obtain the dispatch guard, and apply the shared phase and head-envelope adapter.
This factors the identical placement of the copy, zero, addition, and head-move rows. -/
private theorem wordMul_phase {x : List Bool} (p : WordMulStage)
    (c c' : Cfg 5 Bool (wordMulPh p) x) (B W : ℕ) (q : wordMulPh p)
    (next : Σ p, wordMulPh p) (origin : Fin 5 → ℤ)
    (hR : ReachesWithin (wordMulRows p) c (wordMulExit p) B B c')
    (hq : c'.state = some q) (hred : wordMulRed p q = some next) (hp : p ≠ .done)
    (hB : B ≤ 2 * (W + 1)) (hpos : ∀ j, |c.workTapePos j - origin j| ≤ (W : ℤ)) :
    ∃ t ≤ B + 1, Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - origin j| ≤ (3 * (W + 1) : ℕ))
      (c.mapState (fun q : wordMulPh p => (⟨p, q⟩ : Σ p, wordMulPh p)))
      (c'.mapState fun _ => next) t := by
  obtain ⟨t, ht, cut, _, run⟩ := (reachesWithin_iff _ _ _ _ _ _).mp hR
  have guard := wordPhase_guard wordMulRows wordMulRed p c t (wordMulExit p) cut (wordMulRed_none p)
  refine ⟨t + 1, by omega, ?_⟩
  exact wordPhase_bounded wordMulRows ⟨.copy, .fwd false⟩ wordMulRed p c c' t W q next
    ⟨.done, .done false⟩ origin run hq hred guard hp (ht.trans hB) hpos

/-- Copying the multiplicand and zeroing the destination establish the loop invariant.

**Proof sketch.** Instantiate the framed transducer twice: first copy source zero to scratch
three, then emit false into destination two while source zero supplies the width. Both runs
return their heads. The phase adapter composes them; disjoint tape patches identify the
canonical zero-product frame. Scratch need not be blank for the second run. -/
private theorem wordMul_init {W : ℕ} {x : List Bool} (u : BitVec W)
    (d : Cfg 5 Bool (Σ p, wordMulPh p) x) (hd : d.state = some ⟨.copy, .fwd false⟩)
    (hu : WordAt d 0 (bvBits u)) :
    ∃ t ≤ 4 * W + 6, Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ)) d
      (wordMulCfg d (0#W) u 0 ⟨.probe, .fwd false⟩) t := by
  let c₀ := d.mapState fun _ => (ScanPhase.fwd false)
  let e₀ : Cfg 5 Bool (ScanPhase Bool) x :=
    {c₀ with state := some (.done false), workTapes := wordWrite c₀ 3 (bvBits u)}
  have hcopy := wordLock_run 0 0 3 (fun (_ : Bool) bit _ => (false, bit)) false
    (bvBits u) (bvBits u) (bvBits u) (fun _ => false) rfl rfl rfl (fun _ _ => rfl)
    c₀ (by simp only [c₀, Cfg.mapState_state, hd, Option.map_some])
    ((wordAt_mapState d _ 0 _).mpr hu) ((wordAt_mapState d _ 0 _).mpr hu)
  simp only [bvBits_length] at hcopy
  obtain ⟨t₀, ht₀, seg₀⟩ := wordMul_phase .copy c₀ e₀ (2 * (W + 1)) W (.done false)
    ⟨.zero, .fwd false⟩ d.workTapePos hcopy rfl rfl (by decide) le_rfl
    (by intro j; simp only [c₀, Cfg.mapState_workTapePos, sub_self, abs_zero]; omega)
  let d₁ := {d with
    state := some (⟨.zero, .fwd false⟩ : Σ p, wordMulPh p)
    workTapes := wordWrite d 3 (bvBits u)}
  have hstart : {d with state := some (⟨.copy, .fwd false⟩ : Σ p, wordMulPh p)} = d := by rw [← hd]
  have seg₀' : Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ)) d d₁ t₀ := by
    simpa only [c₀, e₀, d₁, Cfg.mapState_eq, hd, Option.map_some, hstart] using seg₀
  let c₁ := d₁.mapState fun _ => (ScanPhase.fwd false)
  let e₁ : Cfg 5 Bool (ScanPhase Bool) x :=
    {c₁ with state := some (.done false), workTapes := wordWrite c₁ 2 (bvBits (0#W))}
  have hu₁ : WordAt c₁ 0 (bvBits u) := by
    rw [wordAt_mapState]
    simpa [d₁, wordAt_iff, wordWrite_apply] using hu
  have hzero := wordLock_run 0 0 2 (fun (_ : Bool) _ _ => (false, false)) false
    (bvBits u) (bvBits u) (bvBits (0#W)) (fun _ => false) rfl
    (by simp only [bvBits_length]) rfl
    (by intro r hr; simp [bvBits_def]) c₁
    (by simp only [c₁, d₁, Cfg.mapState_state, Option.map_some]) hu₁ hu₁
  simp only [bvBits_length] at hzero
  obtain ⟨t₁, ht₁, seg₁⟩ := wordMul_phase .zero c₁ e₁ (2 * (W + 1)) W (.done false)
    ⟨.probe, .fwd false⟩ d.workTapePos hzero rfl rfl (by decide) le_rfl
    (by intro j; simp only [c₁, Cfg.mapState_workTapePos, d₁, sub_self, abs_zero]; omega)
  have hend : e₁.mapState (fun _ => (⟨.probe, .fwd false⟩ : Σ p, wordMulPh p)) =
      wordMulCfg d (0#W) u 0 ⟨.probe, .fwd false⟩ := by
    apply Cfg.ext
    · simp only [e₁, Cfg.mapState_state, Option.map_some, wordMulCfg]
    · simp only [e₁, c₁, d₁, Cfg.mapState_inputPos, wordMulCfg]
    · funext j z
      by_cases h₂ : j = 2 <;> by_cases h₃ : j = 3 <;>
        simp [e₁, c₁, d₁, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
          wordMulCfg, wordMulTapes, wordWrite_apply, wordPatch_apply, h₂, h₃]
    · funext j
      simp [e₁, c₁, d₁, Cfg.mapState_workTapePos, wordMulCfg, wordMulHeads]
    · simp only [e₁, c₁, d₁, Cfg.mapState_output, wordMulCfg]
  have seg₁' : Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ)) d₁
      (wordMulCfg d (0#W) u 0 ⟨.probe, .fwd false⟩) t₁ := by
    have hs : Segment wordMulTM {some ⟨.done, .done false⟩}
        (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ))
        (c₁.mapState (fun q : ScanPhase Bool => (⟨.zero, q⟩ : Σ p, wordMulPh p)))
        (wordMulCfg d (0#W) u 0 ⟨.probe, .fwd false⟩) t₁ := hend ▸ seg₁
    simpa only [c₁, d₁, Cfg.mapState_eq, Option.map_some] using hs
  exact ⟨t₀ + t₁, by omega, seg₀'.trans seg₁'⟩

/-- A stationary probe and its dispatch preserve the canonical frame in two steps.

**Proof sketch.** The probe leaf reads the current multiplier cell without moving or writing.
Its entry is outside all probe exits. The public host's single dispatch enters the supplied
next phase, and `wordMulCfg_pos` gives the shared linear head envelope. -/
private theorem wordMul_probe {W : ℕ} {x : List Bool}
    (d : Cfg 5 Bool (Σ p, wordMulPh p) x) (acc shifted : BitVec W) (r : ℕ) (hr : r ≤ W)
    (sym : Option Bool) (next : Σ p, wordMulPh p)
    (hread : d.workTapes 1 (d.workTapePos 1 + r) = sym)
    (hred : wordMulRed .probe (wordProbeState sym) = some next) :
    Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ))
      (wordMulCfg d acc shifted r ⟨.probe, .fwd false⟩) (wordMulCfg d acc shifted r next) 2 := by
  let c := wordMulCfg d acc shifted r (ScanPhase.fwd false)
  let q := wordProbeState sym
  let e := wordMulCfg d acc shifted r q
  have hs : c.workTapes 1 (c.workTapePos 1) = sym := by
    simpa [c, wordMulCfg, wordMulTapes, wordMulHeads] using hread
  have hrun : (wordMulRows .probe).runFrom c 1 = e := by
    rw [show wordMulRows .probe = wordProbeTM 1 by rfl, wordProbe_run 1 c rfl, hs]
    rfl
  have guard := wordPhase_guard wordMulRows wordMulRed .probe c 1 (wordMulExit .probe)
    (by
      intro t ht
      have hz : t = 0 := by omega
      subst t
      rw [MultiTapeTM.runFrom_zero]
      simp [c, wordMulCfg, wordMulExit]) (wordMulRed_none .probe)
  have hseg := wordPhase_bounded wordMulRows ⟨.copy, .fwd false⟩ wordMulRed .probe c e 1 W q next
    ⟨.done, .done false⟩ d.workTapePos hrun rfl hred guard (by decide) (by omega)
    (wordMulCfg_pos d acc shifted r _ hr)
  simpa only [wordMulTM, c, e, wordMulCfg_mapState] using hseg

/-- A catalog delay shift and one fixed input-head move prepare the next multiplier bit.

**Proof sketch.** `scanResult_shiftRight` and `wordShiftUp_bits` identify the scratch rewrite
with a one-place left shift. The canonical overwrite lemma keeps the destination intact.
The shared fixed-move row then advances only tape one's head, and its dispatch returns to
the probe. Both phase placements use the same linear envelope; their time is at most `2*W+5`. -/
private theorem wordMul_shift_advance {W : ℕ} {x : List Bool}
    (d : Cfg 5 Bool (Σ p, wordMulPh p) x) (w : List Bool)
    (hw : WordAt d 2 w) (hlen : w.length = W) (hb : ScratchBlank d)
    (acc shifted : BitVec W) (r : ℕ) (hr : r < W) :
    ∃ t ≤ 2 * W + 5, Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ))
      (wordMulCfg d acc shifted r ⟨.shift, .fwd false⟩)
      (wordMulCfg d acc (shifted <<< 1) (r + 1) ⟨.probe, .fwd false⟩) t := by
  let c₀ := wordMulCfg d acc shifted r (ScanPhase.fwd false)
  let flag := (bvBits shifted).getLast?.getD false
  let e₀ := wordMulCfg d acc (shifted <<< 1) r (ScanPhase.done flag)
  have hword := (wordMulCfg_words d w hw hlen hb acc shifted r (ScanPhase.fwd false)).2
  have hscan := scanTM_run_ofCfg 3 (scanShift id (fun (_ bit : Bool) => bit)) scanKeep false
    (bvBits shifted) c₀ rfl ((wordAt_iff c₀ 3 _).mp hword)
  have run₀ : (wordMulRows .shift).runFrom c₀ (2 * W + 2) = e₀ := by
    have h := hscan.1
    simp only [scanResult_shiftRight, List.map_id, wordShiftUp_bits, bvBits_length] at h
    apply h.trans
    apply Cfg.ext <;> try rfl
    have htapes := wordMulCfg_write d acc shifted (shifted <<< 1) r (ScanPhase.fwd false) 3 (Or.inr rfl)
    funext j z
    simpa only [wordWrite_apply, bvBits_length, c₀, e₀, wordMulCfg,
      show (3 : Fin 5) ≠ 2 by decide, if_false, if_true] using congrFun (congrFun htapes j) z
  have guard₀ := wordPhase_guard wordMulRows wordMulRed .shift c₀ (2 * W + 2) (wordMulExit .shift)
    (by
      intro t ht h
      simp only [wordMulExit, Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · exact hscan.2.1 t (by simpa only [bvBits_length] using ht) true h
      · exact hscan.2.1 t (by simpa only [bvBits_length] using ht) false h)
    (wordMulRed_none .shift)
  have seg₀ := wordPhase_bounded wordMulRows ⟨.copy, .fwd false⟩ wordMulRed .shift c₀ e₀ (2 * W + 2) W
    (.done flag) ⟨.advance, .fwd false⟩ ⟨.done, .done false⟩ d.workTapePos run₀ rfl rfl guard₀
    (by decide) (by omega) (wordMulCfg_pos d acc shifted r _ hr.le)
  simp only [c₀, e₀, wordMulCfg_mapState] at seg₀
  let c₁ := wordMulCfg d acc (shifted <<< 1) r (ScanPhase.fwd false)
  let e₁ : Cfg 5 Bool (ScanPhase Bool) x := {c₁ with
    state := some (.done false)
    workTapePos := fun j => c₁.workTapePos j + if j = 1 ∨ j = 1 ∨ j = 1 then ((1 : SignType) : ℤ) else 0}
  have hmove := wordMove_run 1 1 1 1 c₁ rfl
  obtain ⟨t₁, ht₁, seg₁⟩ := wordMul_phase .advance c₁ e₁ 1 W (.done false)
    ⟨.probe, .fwd false⟩ d.workTapePos hmove rfl rfl (by decide) (by omega)
    (wordMulCfg_pos d acc (shifted <<< 1) r _ hr.le)
  have hend : e₁.mapState (fun _ => (⟨.probe, .fwd false⟩ : Σ p, wordMulPh p)) =
      wordMulCfg d acc (shifted <<< 1) (r + 1) ⟨.probe, .fwd false⟩ := by
    rw [Cfg.mapState_eq]
    apply Cfg.ext <;> try rfl
    funext j
    by_cases hj : j = 1 <;> simp [e₁, c₁, wordMulCfg, wordMulHeads, hj, add_assoc]
  have seg₁' : Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ))
      (wordMulCfg d acc (shifted <<< 1) r ⟨.advance, .fwd false⟩)
      (wordMulCfg d acc (shifted <<< 1) (r + 1) ⟨.probe, .fwd false⟩) t₁ := by
    have hs := hend ▸ seg₁
    simpa only [c₁, wordMulCfg_mapState] using hs
  exact ⟨2 * W + 2 + 1 + t₁, by omega, seg₀.trans seg₁'⟩

/-- The same ripple row adds occupied scratch into the destination in place.

**Proof sketch.** Apply `wordRipple_run` with tape three as first operand and tape two as
both second operand and destination. Its arbitrary frame and alias-safe proof permit both
the occupied scratch and the overwritten input. The canonical patch overwrite removes the
old product, and the shared phase adapter dispatches to the shift row. -/
private theorem wordMul_add {W : ℕ} {x : List Bool}
    (d : Cfg 5 Bool (Σ p, wordMulPh p) x) (w : List Bool)
    (hw : WordAt d 2 w) (hlen : w.length = W) (hb : ScratchBlank d)
    (acc shifted : BitVec W) (r : ℕ) (hr : r ≤ W) :
    ∃ t ≤ 2 * W + 3, Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ))
      (wordMulCfg d acc shifted r ⟨.add, .fwd false⟩)
      (wordMulCfg d (acc + shifted) shifted r ⟨.shift, .fwd false⟩) t := by
  let c := wordMulCfg d acc shifted r (ScanPhase.fwd false)
  let e := wordMulCfg d (acc + shifted) shifted r (ScanPhase.done false)
  have hwords := wordMulCfg_words d w hw hlen hb acc shifted r (ScanPhase.fwd false)
  have h := wordRipple_run 3 2 2 false false shifted acc c rfl hwords.2 hwords.1
  have heq : shifted + (if false then ~~~acc else acc) +
      BitVec.setWidth W (BitVec.ofBool false) = acc + shifted := by
    simp [BitVec.add_comm]
  rw [heq] at h
  have hend : {c with state := some (.done false), workTapes := wordWrite c 2 (bvBits (acc + shifted))} = e := by
    apply Cfg.ext <;> try rfl
    simpa only [e, wordMulCfg, if_true, show (2 : Fin 5) ≠ 3 by decide, if_false] using
      wordMulCfg_write d acc shifted (acc + shifted) r (ScanPhase.fwd false) 2 (Or.inl rfl)
  have hR : ReachesWithin (wordMulRows .add) c (wordMulExit .add) (2 * (W + 1)) (2 * (W + 1)) e := by
    simpa only [Bool.false_eq_true, if_false, hend] using h
  obtain ⟨t, ht, hseg⟩ := wordMul_phase .add c e (2 * (W + 1)) W (.done false)
    ⟨.shift, .fwd false⟩ d.workTapePos hR rfl rfl (by decide) le_rfl
    (wordMulCfg_pos d acc shifted r _ hr)
  refine ⟨t, by omega, ?_⟩
  simpa only [c, e, wordMulCfg_mapState] using hseg

/-- One multiplier bit preserves the partial-product invariant and advances its bit index.

**Proof sketch.** Read the unchanged tape-one bit using its original `WordAt` condition.
The probe dispatches either directly to the shared shift/advance segment or through the
in-place ripple addition. `wordMulAcc_succ` identifies the new product, and `shiftLeft_add`
identifies the shifted scratch word. The two branches share the same framed round lemmas. -/
private theorem wordMul_round {W : ℕ} {x : List Bool} (u v : BitVec W)
    (d : Cfg 5 Bool (Σ p, wordMulPh p) x) (w : List Bool)
    (hv : WordAt d 1 (bvBits v)) (hw : WordAt d 2 w) (hlen : w.length = W) (hb : ScratchBlank d)
    (r : ℕ) (hr : r < W) :
    ∃ t ≤ 4 * W + 10, Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ))
      (wordMulCfg d (wordMulAcc u v r) (u <<< r) r ⟨.probe, .fwd false⟩)
      (wordMulCfg d (wordMulAcc u v (r + 1)) (u <<< (r + 1)) (r + 1) ⟨.probe, .fwd false⟩) t := by
  have hread : d.workTapes 1 (d.workTapePos 1 + r) = some (v.getLsbD r) := by
    have h := (wordAt_iff d 1 _).mp hv r (by omega) (by simp only [bvBits_length]; omega)
    have hrlist : r < (bvBits v).length := by simpa only [bvBits_length] using hr
    rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem hrlist] at h
    simpa only [bvBits_def, List.getElem_ofFn] using h
  cases hbit : v.getLsbD r with
  | false =>
    have hprobe := wordMul_probe d (wordMulAcc u v r) (u <<< r) r hr.le (some false)
      ⟨.shift, .fwd false⟩ (by simpa only [hbit] using hread) rfl
    obtain ⟨t, ht, hshift⟩ := wordMul_shift_advance d w hw hlen hb (wordMulAcc u v r) (u <<< r) r hr
    refine ⟨2 + t, by omega, ?_⟩
    have hs := hprobe.trans hshift
    simpa [wordMulAcc_succ, hbit, ← BitVec.shiftLeft_add] using hs
  | true =>
    have hprobe := wordMul_probe d (wordMulAcc u v r) (u <<< r) r hr.le (some true)
      ⟨.add, .fwd false⟩ (by simpa only [hbit] using hread) rfl
    obtain ⟨t₀, ht₀, hadd⟩ := wordMul_add d w hw hlen hb (wordMulAcc u v r) (u <<< r) r hr.le
    obtain ⟨t₁, ht₁, hshift⟩ := wordMul_shift_advance d w hw hlen hb
      (wordMulAcc u v r + (u <<< r)) (u <<< r) r hr
    refine ⟨2 + t₀ + t₁, by omega, ?_⟩
    have hs := (hprobe.trans hadd).trans hshift
    simpa only [wordMulAcc_succ, hbit, if_true, ← BitVec.shiftLeft_add] using hs

/-- The first `r` multiplier rounds compose with quadratic time and one linear envelope.

**Proof sketch.** Induct on `r ≤ W`. The empty segment has zero product and the unshifted
multiplicand. At each successor append `wordMul_round` with `Segment.trans`, and add its
`4*W+10` time allowance. The shared head predicate is preserved by segment composition. -/
private theorem wordMul_loop {W : ℕ} {x : List Bool} (u v : BitVec W)
    (d : Cfg 5 Bool (Σ p, wordMulPh p) x) (w : List Bool)
    (hv : WordAt d 1 (bvBits v)) (hw : WordAt d 2 w) (hlen : w.length = W) (hb : ScratchBlank d)
    (r : ℕ) (hr : r ≤ W) :
    ∃ t ≤ r * (4 * W + 10), Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ))
      (wordMulCfg d (0#W) u 0 ⟨.probe, .fwd false⟩)
      (wordMulCfg d (wordMulAcc u v r) (u <<< r) r ⟨.probe, .fwd false⟩) t := by
  induction r with
  | zero =>
    refine ⟨0, by omega, ?_⟩
    have hz : wordMulAcc u v 0 = 0#W := by
      dsimp only [wordMulAcc]
      rw [BitVec.of_length_zero (x := v.setWidth 0), BitVec.setWidth_zero]
      simp
    rw [hz, BitVec.shiftLeft_zero]
    exact Segment.zero (fun j => by simp [wordMulCfg, wordMulHeads]; omega)
  | succ r ih =>
    obtain ⟨t₀, ht₀, h₀⟩ := ih (by omega)
    obtain ⟨t₁, ht₁, h₁⟩ := wordMul_round u v d w hv hw hlen hb r (by omega)
    exact ⟨t₀ + t₁, by nlinarith, h₀.trans h₁⟩

/-- After clearing scratch, the output frame has only the tape-one head left to return. -/
private def wordMulRestCfg {S T : Type} {x : List Bool} {W : ℕ} (d : Cfg 5 Bool S x)
    (acc : BitVec W) (r : ℕ) (q : T) : Cfg 5 Bool T x where
  state := some q
  inputPos := d.inputPos
  workTapes := wordWrite d 2 (bvBits acc)
  workTapePos := wordMulHeads d r
  output := d.output

/-- Tagging the final rewind frame changes only its state. -/
private theorem wordMulRestCfg_mapState {S T U : Type} {x : List Bool} {W : ℕ}
    (d : Cfg 5 Bool S x) (acc : BitVec W) (r : ℕ) (q : T) (f : T → U) :
    (wordMulRestCfg d acc r q).mapState f = wordMulRestCfg d acc r (f q) := by
  rw [Cfg.mapState_eq]
  rfl

/-- At the multiplier's right delimiter, clear scratch and return the last displaced head.

**Proof sketch.** The stationary probe sees the delimiter and dispatches to `clearTM` on the
scratch word. Its interval erasure restores the original globally blank scratch tape and
leaves the output patch. The catalog rewind then traverses the unchanged multiplier prefix
from offset `W`, returning tape one's head. The three dispatches give time `3*W+8`. -/
private theorem wordMul_finish {W : ℕ} {x : List Bool} (v : BitVec W)
    (d : Cfg 5 Bool (Σ p, wordMulPh p) x) (w : List Bool)
    (hv : WordAt d 1 (bvBits v)) (hw : WordAt d 2 w) (hlen : w.length = W) (hb : ScratchBlank d)
    (acc shifted : BitVec W) :
    Segment wordMulTM {some ⟨.done, .done false⟩}
      (fun heads => ∀ j, |heads j - d.workTapePos j| ≤ (3 * (W + 1) : ℕ))
      (wordMulCfg d acc shifted W ⟨.probe, .fwd false⟩)
      {d with state := some ⟨.done, .done false⟩, workTapes := wordWrite d 2 (bvBits acc)}
      (3 * W + 8) := by
  have hread : d.workTapes 1 (d.workTapePos 1 + W) = none := by
    have h := (wordAt_iff d 1 _).mp hv W (by omega) (by simp only [bvBits_length]; omega)
    rw [FinTM.bufferTape_nat, List.getElem?_eq_none (by simp only [bvBits_length]; omega)] at h
    exact h
  have hprobe := wordMul_probe d acc shifted W le_rfl none ⟨.clear, .sweep⟩ hread rfl
  let c₀ := wordMulCfg d acc shifted W SweepPhase.sweep
  let e₀ := wordMulRestCfg d acc W SweepPhase.done
  have hword := (wordMulCfg_words d w hw hlen hb acc shifted W SweepPhase.sweep).2
  have hclear := clearTM_run_ofCfg 3 (bvBits shifted) c₀ rfl ((wordAt_iff c₀ 3 _).mp hword)
  have run₀ : (wordMulRows .clear).runFrom c₀ (2 * W + 2) = e₀ := by
    have h := hclear.1
    simp only [bvBits_length] at h
    apply h.trans
    apply Cfg.ext <;> try rfl
    funext j z
    have hblank := (scratchBlank_iff d).mp hb 3 (by decide)
    by_cases h₂ : j = 2 <;> by_cases h₃ : j = 3 <;>
      simp [c₀, e₀, wordMulCfg, wordMulHeads, wordMulTapes, wordMulRestCfg,
        wordWrite_apply, wordPatch_apply, bvBits_length, h₂, h₃, hblank]
    all_goals omega
  have guard₀ := wordPhase_guard wordMulRows wordMulRed .clear c₀ (2 * W + 2) (wordMulExit .clear)
    (by intro t ht h; exact hclear.2.1 t (by simpa only [bvBits_length] using ht) h)
    (wordMulRed_none .clear)
  have seg₀ := wordPhase_bounded wordMulRows ⟨.copy, .fwd false⟩ wordMulRed .clear c₀ e₀ (2 * W + 2) W
    .done ⟨.rewind, .start⟩ ⟨.done, .done false⟩ d.workTapePos run₀ rfl rfl guard₀
    (by decide) (by omega) (wordMulCfg_pos d acc shifted W _ le_rfl)
  simp only [c₀, e₀, wordMulCfg_mapState, wordMulRestCfg_mapState] at seg₀
  let c₁ := wordMulRestCfg d acc W RewindPhase.start
  let e₁ := wordMulRestCfg d acc 0 RewindPhase.done
  have hrewind := rewindTM_run_ofCfg 1 (bvBits v) W (by simp only [bvBits_length]; omega) c₁ rfl (by
    intro p hlo hhi
    have h := (wordAt_iff d 1 _).mp hv p hlo (by simp only [bvBits_length]; omega)
    simpa [c₁, wordMulRestCfg, wordMulHeads, wordWrite_apply] using h)
  have run₁ : (wordMulRows .rewind).runFrom c₁ (W + 2) = e₁ := by
    apply hrewind.1.trans
    apply Cfg.ext <;> try rfl
    funext j
    by_cases hj : j = 1 <;>
      simp [c₁, e₁, wordMulRestCfg, wordMulHeads, Function.update_apply, hj]
  have guard₁ := wordPhase_guard wordMulRows wordMulRed .rewind c₁ (W + 2) (wordMulExit .rewind)
    hrewind.2.1 (wordMulRed_none .rewind)
  have seg₁ := wordPhase_bounded wordMulRows ⟨.copy, .fwd false⟩ wordMulRed .rewind c₁ e₁ (W + 2) W
    .done ⟨.done, .done false⟩ ⟨.done, .done false⟩ d.workTapePos run₁ rfl rfl guard₁
    (by decide) (by omega) (wordMulCfg_pos d acc shifted W RewindPhase.start le_rfl)
  simp only [c₁, e₁, wordMulRestCfg_mapState] at seg₁
  have hs := (hprobe.trans seg₀).trans seg₁
  have hend : wordMulRestCfg d acc 0 (⟨.done, .done false⟩ : Σ p, wordMulPh p) =
      {d with state := some ⟨.done, .done false⟩, workTapes := wordWrite d 2 (bvBits acc)} := by
    apply Cfg.ext <;> try rfl
    funext j
    simp only [wordMulRestCfg, wordMulHeads, Nat.cast_zero, ite_self, add_zero]
  have htime : 2 + (2 * W + 2 + 1) + (W + 2 + 1) = 3 * W + 8 := by omega
  simpa only [wordMulTM, hend, htime] using hs

/-- **Multiplication modulo `2^W`.** As `Turing.exists_wordAddTM`, writing `u * v`, within
`C·(W + 1)²` steps and radius `C·(W + 1)`. [AB09, Exercise 1.9]

**Proof sketch.** `wordMul_init` copies `u` to scratch three and zeroes the destination.
`wordMul_loop` composes `W` rounds, whose invariant is `wordMulAcc u v r` in the destination
and `u <<< r` in scratch. Each round probes the next multiplier bit, conditionally invokes the
same alias-safe ripple adder in place, then uses the catalog delay shift and advances tape one.
`wordMulAcc_succ` is core's low-bit-width multiplication recurrence. `wordMul_finish` clears
scratch and rewinds the multiplier head. The public phase host drives all rows; `Segment.trans`
preserves one linear envelope while adding times. The constant `30` bounds both the quadratic
time and linear radius, including the empty-width case. -/
theorem exists_wordMulTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u v : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 1 (bvBits v) → WordAt d 2 w →
        w.length = W → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1) ^ 2) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u * v)) } := by
  refine ⟨(Σ p, wordMulPh p), inferInstance, inferInstance, wordMulTM,
    ⟨.copy, .fwd false⟩, ⟨.done, .done false⟩, 30, ?_⟩
  intro x W u v w d hd hu hv hw hlen hb
  obtain ⟨t₀, ht₀, hinit⟩ := wordMul_init u d hd hu
  obtain ⟨t₁, ht₁, hloop⟩ := wordMul_loop u v d w hv hw hlen hb W le_rfl
  have hfinish := wordMul_finish v d w hv hw hlen hb (wordMulAcc u v W) (u <<< W)
  have hs := (segment_iff _ _ _ _ _ _).mp ((hinit.trans hloop).trans hfinish)
  have htime : t₀ + t₁ + (3 * W + 8) ≤ 30 * (W + 1) ^ 2 := by nlinarith
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t₀ + t₁ + (3 * W + 8), htime, hs.2.1, ?_, ?_⟩
  · intro s hst j
    exact (hs.2.2 s hst j).trans (by omega)
  · simpa only [wordMulAcc, BitVec.setWidth_eq] using hs.1

/-! ## Framed read-only folds -/

/-- A Boolean fold scans one delimited word, returns the head, and preserves every cell.

**Proof sketch.** Apply `scanTM_run_ofCfg` and `scanResult_fold`. The `WordAt` interval
identifies every cell of the resulting word patch with its original value. The catalog's
first-exit clause excludes both Boolean exits, and its head envelope gives radius
`2 * (w.length + 1)`. -/
private theorem wordFold_run (δ : Bool → Bool → Bool) (a₀ : Bool) {x : List Bool}
    (w : List Bool) (d : Cfg 5 Bool (ScanPhase Bool) x)
    (hd : d.state = some (.fwd a₀)) (hw : WordAt d 0 w) :
    ReachesWithin (scanTM 5 0 (scanFold δ) scanKeep a₀) d
      {some (.done true), some (.done false)} (2 * (w.length + 1)) (2 * (w.length + 1))
      {d with state := some (.done (w.foldl δ a₀))} := by
  obtain ⟨hrun, hcut, henv⟩ :=
    scanTM_run_ofCfg 0 (scanFold δ) scanKeep a₀ w d hd ((wordAt_iff d 0 w).mp hw)
  rw [scanResult_fold] at hrun
  have hpatch : (fun j q =>
      if j = 0 ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ)
        then FinTM.bufferTape w (q - d.workTapePos j) else d.workTapes j q) =
      d.workTapes := by
    funext j q
    by_cases hj : j = 0
    · subst j
      simpa only [wordPatch_apply, true_and] using
        congrFun (wordPatch_self (d.workTapes 0) (d.workTapePos 0) w
          ((wordAt_iff d 0 w).mp hw)) q
    · simp only [hj, false_and, if_false]
  simp only [hpatch] at hrun
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨2 * w.length + 2, by omega, ?_, ?_, hrun⟩
  · intro t ht
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
      And.intro (hcut t ht true) (hcut t ht false)
  · intro t ht j
    have hj := henv j t ht
    by_cases h : j = 0
    · subst j
      simp only [if_true, Finset.mem_Icc] at hj
      rw [abs_le]
      constructor <;> omega
    · simp only [h, if_false] at hj
      rw [hj, sub_self, abs_zero]
      positivity

/-- The overwrite fold of a word's bits is its most significant bit, with false for width zero. -/
private theorem bvBits_last_fold {W : ℕ} (u : BitVec W) :
    (bvBits u).foldl (fun _ b => b) false = u.msb := by
  cases W with
  | zero => simp [bvBits, BitVec.msb_zero_length]
  | succ W =>
    rw [bvBits_def, List.ofFn_succ_last, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    simpa only [Fin.val_last, Nat.add_sub_cancel] using (BitVec.msb_eq_getLsbD_last u).symm

/-- The Boolean disjunction fold records exactly whether a true cell has occurred. -/
private theorem wordAny_fold (w : List Bool) (b : Bool) :
    w.foldl (fun a c => a || c) b = (b || decide (true ∈ w)) := by
  induction w generalizing b with
  | nil => simp
  | cons a w ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, Bool.decide_or]
    cases a <;> cases b <;> simp

/-- A word has no true bit exactly when it is zero. -/
private theorem bvBits_no_true {W : ℕ} (u : BitVec W) :
    true ∉ bvBits u ↔ u = 0 := by
  constructor
  · intro h
    apply bvBits_injective
    rw [bvBits_def, bvBits_def]
    apply List.ofFn_inj.mpr
    funext i
    change u.getLsbD i = (0#W).getLsbD i
    rw [BitVec.getLsbD_zero]
    apply Bool.eq_false_iff.mpr
    intro hi
    exact h (List.mem_ofFn.mpr ⟨i, hi⟩)
  · rintro rfl
    simp [bvBits]

/-! ## Word layouts under composition -/





/-- Moving every bit down one position and repeating the sign bit is arithmetic halving.

**Proof sketch.** Compare list cells. Below the last cell, `List.getElem_tail` reads the next
source bit. The last cell reads the appended `msb`. `BitVec.getLsbD_sshiftRight` gives exactly
these two cases, with an empty result at width zero. -/
private theorem wordHalf_bits {W : ℕ} (u : BitVec W) :
    List.zipWith (fun (_ b : Bool) => b) (bvBits u) ((bvBits u).tail ++ [u.msb]) =
      bvBits (u.sshiftRight 1) := by
  apply List.ext_getElem
  · simp only [List.length_zipWith, bvBits_length, List.length_append, List.length_tail,
      List.length_singleton]
    omega
  · intro i hi hi'
    have hiW : i < W := by simpa only [bvBits_length] using hi'
    simp only [List.getElem_zipWith]
    by_cases hn : i + 1 < W
    · rw [List.getElem_append_left (by simp only [List.length_tail, bvBits_length]; omega),
        List.getElem_tail]
      simp only [bvBits_def, List.getElem_ofFn]
      rw [BitVec.getLsbD_sshiftRight]
      simp [hiW, hn, Nat.add_comm]
    · rw [List.getElem_append_right (by simp only [List.length_tail, bvBits_length]; omega)]
      simp only [List.getElem_singleton, bvBits_def, List.getElem_ofFn]
      rw [BitVec.getLsbD_sshiftRight]
      simp [hiW, hn, Nat.add_comm]


/-- The rows of arithmetic halving: copy, sign fold, and either sign-filled shift. -/
private def wordHalfRows (i : Fin 5) : MultiTapeTM 5 Bool (ScanPhase Bool) :=
  if i = 0 then wordLockTM 0 0 2 (fun (_ : Bool) b _ => (false, b)) false
  else if i = 1 then scanTM 5 0 (scanFold (fun _ b => b)) scanKeep false
  else scanTM 5 2 scanKeep (scanShift id (fun (_ b : Bool) => b)) (decide (i = 3))

/-- Halving dispatches the sign flag to the corresponding fixed-sign scan, then one exit. -/
private def wordHalfRed (i : Fin 5) : ScanPhase Bool → Option (Σ _ : Fin 5, ScanPhase Bool)
  | .done b =>
    if i = 0 then if b then none else some ⟨1, .fwd false⟩
    else if i = 1 then some ⟨if b then 3 else 2, .fwd b⟩
    else if i = 2 ∨ i = 3 then some ⟨4, .done false⟩ else none
  | _ => none

/-- Arithmetic halving composed from the framed copy and the catalog scans in a phase host. -/
private def wordHalfTM : MultiTapeTM 5 Bool (Σ _ : Fin 5, ScanPhase Bool) :=
  phaseHostTM wordHalfRows ⟨0, .fwd false⟩ wordHalfRed

/-- The arithmetic-shift program preserves every frame and returns all heads.

**Proof sketch.** Copy the source with `wordLock_run`, compute its sign with `wordFold_run`,
and dispatch to `scanResult_shiftLeft` with that fixed sign. `wordHalf_bits` identifies the
rewritten list. `wordPhase_segment` places the three rows in `phaseHostTM`; `Segment.trans`
composes their verified runs. Their heads return at each seam, and `wordWrite_twice` removes
the intermediate copy. The total time, including three dispatches, is at most `9 * (W + 1)`;
the general displacement-from-time bound supplies the same radius. -/
private theorem wordHalf_run {W : ℕ} {x : List Bool} (u : BitVec W) (w : List Bool)
    (d : Cfg 5 Bool (Σ _ : Fin 5, ScanPhase Bool) x)
    (hd : d.state = some ⟨0, .fwd false⟩) (hu : WordAt d 0 (bvBits u))
    (hw : WordAt d 2 w) (hlen : w.length = W) :
    ReachesWithin wordHalfTM d {some ⟨4, .done false⟩} (9 * (W + 1)) (9 * (W + 1))
      {d with state := some ⟨4, .done false⟩, workTapes := wordWrite d 2 (bvBits (u.sshiftRight 1))} := by
  let exit : Σ _ : Fin 5, ScanPhase Bool := ⟨4, .done false⟩
  let d₀ := d.mapState fun _ => (ScanPhase.fwd false)
  have hcopy := wordLock_run 0 0 2 (fun (_ : Bool) bit _ => (false, bit)) false
    (bvBits u) (bvBits u) (bvBits u) (fun _ => false) rfl rfl rfl (fun _ _ => rfl)
    d₀ (by simp only [d₀, Cfg.mapState_state, hd, Option.map_some])
    ((wordAt_mapState d _ 0 _).mpr hu) ((wordAt_mapState d _ 0 _).mpr hu)
  simp only [bvBits_length] at hcopy
  obtain ⟨t₀, ht₀, cut₀, _, run₀⟩ := (reachesWithin_iff _ _ _ _ _ _).mp hcopy
  let e₀ : Cfg 5 Bool (ScanPhase Bool) x := {d₀ with state := some (.done false), workTapes := wordWrite d₀ 2 (bvBits u)}
  let d₁ := { d with
    state := some (⟨1, .fwd false⟩ : Σ _ : Fin 5, ScanPhase Bool)
    workTapes := wordWrite d 2 (bvBits u)}
  have guard₀ : ∀ t < t₀, ∀ q,
      ((wordHalfRows 0).runFrom d₀ t).state = some q → wordHalfRed 0 q = none := by
    intro t ht q hq
    cases q with
    | fwd a => rfl
    | bwd a => rfl
    | done a =>
      cases a with
      | true => rfl
      | false =>
        apply False.elim
        apply cut₀ t ht
        simpa only [wordHalfRows, if_pos rfl, Set.mem_singleton_iff] using hq
  have seg₀ : Segment wordHalfTM {some exit} (fun _ => True) d d₁ (t₀ + 1) := by
    have hs := wordPhase_segment wordHalfRows ⟨0, .fwd false⟩ wordHalfRed 0 d₀ e₀ t₀
      (.done false) ⟨1, .fwd false⟩ exit (fun _ => True)
      (by simpa only [wordHalfRows, if_pos rfl] using run₀) rfl rfl guard₀
      (by decide) (fun _ _ => True.intro)
    have hstart : {d with state := some (⟨0, .fwd false⟩ : Σ _ : Fin 5, ScanPhase Bool)} = d := by
      rw [← hd]
    simpa only [wordHalfTM, d₀, e₀, d₁, Cfg.mapState_eq, hd, Option.map_some,
      wordWrite, hstart] using hs
  have hu₁ : WordAt d₁ 0 (bvBits u) := by
    simpa [d₁, wordAt_iff, wordWrite_apply] using hu
  have hw₁ : WordAt d₁ 2 (bvBits u) :=
    wordAt_write d 2 w (bvBits u) (by simp only [bvBits_length, hlen]) hw
  let c₁ := d₁.mapState fun _ => (ScanPhase.fwd false)
  let b := u.msb
  let p : Fin 5 := if b then 3 else 2
  have hsign := wordFold_run (fun _ bit => bit) false (bvBits u) c₁
    (by simp only [c₁, d₁, Cfg.mapState_state, Option.map_some])
    ((wordAt_mapState d₁ _ 0 _).mpr hu₁)
  simp only [bvBits_length, bvBits_last_fold] at hsign
  obtain ⟨t₁, ht₁, cut₁, _, run₁⟩ := (reachesWithin_iff _ _ _ _ _ _).mp hsign
  let e₁ : Cfg 5 Bool (ScanPhase Bool) x := {c₁ with state := some (.done b)}
  let d₂ := {d₁ with state := some (⟨p, .fwd b⟩ : Σ _ : Fin 5, ScanPhase Bool)}
  have guard₁ : ∀ t < t₁, ∀ q,
      ((wordHalfRows 1).runFrom c₁ t).state = some q → wordHalfRed 1 q = none := by
    intro t ht q hq
    cases q with
    | fwd a => rfl
    | bwd a => rfl
    | done a =>
      apply False.elim
      apply cut₁ t ht
      have hq' : ((scanTM 5 0 (scanFold (fun _ bit => bit)) scanKeep false).runFrom c₁ t).state =
          some (.done a) := by simpa [wordHalfRows] using hq
      rw [hq']
      cases a <;> simp
  have seg₁ : Segment wordHalfTM {some exit} (fun _ => True) d₁ d₂ (t₁ + 1) := by
    have hs := wordPhase_segment wordHalfRows ⟨0, .fwd false⟩ wordHalfRed 1 c₁ e₁ t₁
      (.done b) ⟨p, .fwd b⟩ exit (fun _ => True)
      (by simpa [wordHalfRows] using run₁) rfl (by simp [wordHalfRed, p]) guard₁
      (by decide) (fun _ _ => True.intro)
    simpa only [wordHalfTM, c₁, e₁, d₂, d₁, Cfg.mapState_eq, Option.map_some] using hs
  let c₂ := d₂.mapState fun _ => (ScanPhase.fwd b)
  have hw₂ : WordAt c₂ 2 (bvBits u) := by
    rw [wordAt_mapState]
    exact hw₁
  have hm₂ : wordHalfRows p =
      scanTM 5 2 scanKeep (scanShift id (fun (_ bit : Bool) => bit)) b := by
    cases hb : b <;> simp [wordHalfRows, p, hb]
  have hscan := scanTM_run_ofCfg 2 scanKeep (scanShift id (fun (_ bit : Bool) => bit)) b
    (bvBits u) c₂ (by simp only [c₂, d₂, Cfg.mapState_state, Option.map_some])
    ((wordAt_iff c₂ 2 _).mp hw₂)
  let flag := (bvBits u).head?.getD b
  let e₂ : Cfg 5 Bool (ScanPhase Bool) x := { c₂ with
    state := some (.done flag)
    workTapes := wordWrite c₂ 2 (bvBits (u.sshiftRight 1)) }
  have run₂ : (wordHalfRows p).runFrom c₂ (2 * W + 2) = e₂ := by
    rw [hm₂]
    have hs := hscan.1
    simp only [scanResult_shiftLeft, List.map_id, b, wordHalf_bits, bvBits_length] at hs
    apply hs.trans
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp only [e₂, wordWrite_apply, bvBits_length]
    · rfl
    · rfl
  have guard₂ : ∀ t < 2 * W + 2, ∀ q,
      ((wordHalfRows p).runFrom c₂ t).state = some q → wordHalfRed p q = none := by
    intro t ht q hq
    cases q with
    | fwd a => rfl
    | bwd a => rfl
    | done a =>
      apply False.elim
      have ht' : t < 2 * (bvBits u).length + 2 := by simpa only [bvBits_length] using ht
      apply hscan.2.1 t ht' a
      simpa only [hm₂] using hq
  have seg₂ : Segment wordHalfTM {some exit} (fun _ => True) d₂
      {d with state := some exit, workTapes := wordWrite d 2 (bvBits (u.sshiftRight 1))}
      (2 * W + 2 + 1) := by
    have hs := wordPhase_segment wordHalfRows ⟨0, .fwd false⟩ wordHalfRed p c₂ e₂
      (2 * W + 2) (.done flag) exit exit (fun _ => True) run₂ rfl
      (by cases hb : b <;> simp [wordHalfRed, p, hb, exit]) guard₂
      (by cases hb : b <;> simp [p, hb, exit]) (fun _ _ => True.intro)
    have hwrites : wordWrite d₂ 2 (bvBits (u.sshiftRight 1)) =
        wordWrite d 2 (bvBits (u.sshiftRight 1)) :=
      wordWrite_twice d 2 (bvBits u) (bvBits (u.sshiftRight 1)) (by simp only [bvBits_length])
    have hs' : Segment wordHalfTM {some exit} (fun _ => True) d₂
        {d₂ with state := some exit, workTapes := wordWrite d₂ 2 (bvBits (u.sshiftRight 1))}
        (2 * W + 2 + 1) := by
      simpa only [wordHalfTM, c₂, e₂, d₂, Cfg.mapState_eq, Option.map_some] using hs
    rw [hwrites] at hs'
    exact hs'
  have hs := (segment_iff _ _ _ _ _ _).mp ((seg₀.trans seg₁).trans seg₂)
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨(t₀ + 1 + (t₁ + 1)) + (2 * W + 2 + 1), by omega, hs.2.1, ?_, hs.1⟩
  intro t ht j
  have hp := wordHalfTM.workTapePos_runFrom_mem_Icc d t j
  rw [Finset.mem_Icc] at hp
  rw [abs_le]
  constructor <;> omega

/-- **The arithmetic shift right by one place.** From the entry, with `u` on tape `0`, a word of
`W` cells on tape `2` and blank scratch tapes, the row writes `u.sshiftRight 1` (that is,
`⌊u / 2⌋` read signed) on tape `2`, within `C·(W + 1)` steps and radius `C·(W + 1)`, tape `1`
untouched. [AB09, Exercise 1.9]

**Proof sketch.** `wordHalf_run` composes a framed copy, the catalog's sign fold, and its
left shift with the computed sign as fill. `wordHalf_bits` reads
`BitVec.getLsbD_sshiftRight` to identify the shifted word. Each catalog row returns its heads;
three stationary phase dispatches give time and radius at most `9 * (W + 1)`, also at width zero. -/
theorem exists_wordHalfTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 2 w → w.length = W →
        ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit, workTapes := wordWrite d 2 (bvBits (u.sshiftRight 1)) } := by
  refine ⟨(Σ _ : Fin 5, ScanPhase Bool), inferInstance, inferInstance,
    wordHalfTM, ⟨0, .fwd false⟩, ⟨4, .done false⟩, 9, ?_⟩
  intro x W u w d hd hu hw hlen _
  exact wordHalf_run u w d hd hu hw hlen

/-! ## Fixed head moves and sign extension -/



/-- Sign extension appends copies of the sign bit to the little-endian word.

**Proof sketch.** The first `W` list positions use the low bits of the source; the remaining
`a` positions use `List.getElem_replicate`. These are exactly the two cases of
`BitVec.getLsbD_signExtend`, including the zero-width source. -/
private theorem wordSignExtend_bits {W : ℕ} (u : BitVec W) (a : ℕ) :
    bvBits (u.signExtend (W + a)) = bvBits u ++ List.replicate a u.msb := by
  apply List.ext_getElem
  · simp only [bvBits_length, List.length_append, List.length_replicate]
  · intro i hi hi'
    have hin : i < W + a := by simpa only [bvBits_length] using hi
    by_cases hlow : i < W
    · rw [List.getElem_append_left (by simpa only [bvBits_length] using hlow)]
      simp only [bvBits_def, List.getElem_ofFn, BitVec.getLsbD_signExtend,
        hin, hlow, decide_true, Bool.true_and, if_true]
    · rw [List.getElem_append_right (by simp only [bvBits_length]; omega)]
      simp only [List.getElem_replicate, bvBits_def, List.getElem_ofFn,
        BitVec.getLsbD_signExtend, hin, hlow, decide_true, Bool.true_and, if_false]

/-- Writing at the end of a patched prefix joins the two words, for arbitrary other heads. -/
private theorem wordWrite_append {k : ℕ} {S : Type} {x : List Bool} (d : Cfg k Bool S x)
    (j : Fin k) (u v : List Bool) (heads : Fin k → ℤ)
    (hj : heads j = d.workTapePos j + (u.length : ℤ)) :
    wordWrite {d with workTapes := wordWrite d j u, workTapePos := heads} j v =
      wordWrite d j (u ++ v) := by
  funext r z
  by_cases hr : r = j
  · subst r
    simpa only [wordWrite_apply, wordPatch_apply, true_and, hj] using
      congrFun (wordPatch_append (d.workTapes j) (d.workTapePos j) u v) z
  · simp only [wordWrite_apply, hr, false_and, if_false]

/-- The finite sequence of existing rows used for sign extension. -/
private inductive WordExtStage where
  | sign | copy | walk | back | write | rewindSource | rewindDest | done
  deriving DecidableEq, Fintype

/-- A row's own state alphabet; the sign is carried by the phase index. -/
private def wordExtPh (a : ℕ) : WordExtStage × Bool → Type
  | (.write, b) => WritePhase (List.replicate a b).length
  | (.walk, _) => SeekPhase
  | (.rewindSource, _) | (.rewindDest, _) => RewindPhase
  | _ => ScanPhase Bool

/-- The sign-extension rows are finite for every fixed extension length. -/
private instance wordExtPh_fintype (a : ℕ) (p : WordExtStage × Bool) :
    Fintype (wordExtPh a p) := by
  rcases p with ⟨stage, b⟩
  cases stage <;> dsimp only [wordExtPh] <;> infer_instance

/-- Each sign-extension row has decidable state equality. -/
private instance wordExtPh_decidableEq (a : ℕ) (p : WordExtStage × Bool) :
    DecidableEq (wordExtPh a p) := by
  rcases p with ⟨stage, b⟩
  cases stage <;> dsimp only [wordExtPh] <;> infer_instance

/-- Sign extension uses the catalog's copy, walk, constant writer, and rewind rows. -/
private def wordExtRows (a : ℕ) : (p : WordExtStage × Bool) →
    MultiTapeTM 5 Bool (wordExtPh a p)
  | (.sign, _) => scanTM 5 0 (scanFold (fun _ b => b)) scanKeep false
  | (.copy, _) => wordLockTM 0 0 2 (fun (_ : Bool) bit _ => (false, bit)) false
  | (.walk, _) => walkTM 5 0 (fun j => j = 0 ∨ j = 2) 1
  | (.back, _) => wordMoveTM 0 2 2 (-1)
  | (.write, b) => writeConstTM 5 2 (List.replicate a b)
  | (.rewindSource, _) => rewindTM 5 0
  | (.rewindDest, _) => rewindTM 5 2
  | (.done, _) => wordMoveTM 2 2 2 0

/-- The finite dispatch table threads the computed sign through the extension rows. -/
private def wordExtRed (a : ℕ) : (p : WordExtStage × Bool) → wordExtPh a p →
    Option (Σ p : WordExtStage × Bool, wordExtPh a p)
  | (.sign, _), .done b => some ⟨(.copy, b), .fwd false⟩
  | (.copy, b), .done false => some ⟨(.walk, b), .run⟩
  | (.walk, b), .done => some ⟨(.back, b), .fwd false⟩
  | (.back, b), .done false => some ⟨(.write, b), .wr 0⟩
  | (.write, b), .done => some ⟨(.rewindSource, b), .start⟩
  | (.rewindSource, b), .done => some ⟨(.rewindDest, b), .start⟩
  | (.rewindDest, _), .done => some ⟨(.done, false), .done false⟩
  | _, _ => none

/-- The catalog-row program for sign extension; every loop belongs to an existing row. -/
private def wordExtTM (a : ℕ) : MultiTapeTM 5 Bool (Σ p : WordExtStage × Bool, wordExtPh a p) :=
  phaseHostTM (wordExtRows a) ⟨(.sign, false), .fwd false⟩ (wordExtRed a)

/-- Only catalog exits trigger a sign-extension dispatch. -/
private def wordExtExit (a : ℕ) : (p : WordExtStage × Bool) → Set (Option (wordExtPh a p))
  | (.sign, _) => {some (.done true), some (.done false)}
  | (.copy, _) | (.back, _) => {some (.done false)}
  | (.walk, _) => {some .done}
  | (.write, _) => {some .done}
  | (.rewindSource, _) | (.rewindDest, _) => {some .done}
  | (.done, _) => ∅

/-- A state outside a row's catalog exits cannot redirect the extension host. -/
private theorem wordExtRed_none (a : ℕ) (p : WordExtStage × Bool) (q : wordExtPh a p)
    (h : some q ∉ wordExtExit a p) : wordExtRed a p q = none := by
  rcases p with ⟨stage, b⟩
  cases stage <;> cases q <;> try rfl
  all_goals simp_all [wordExtExit, wordExtRed]
  rename_i flag
  cases flag <;> simp_all

/-- The source and destination head offsets of the extension program. -/
private def wordExtHeads {S : Type} {x : List Bool} (d : Cfg 5 Bool S x)
    (src dst : ℤ) : Fin 5 → ℤ :=
  fun j => d.workTapePos j + if j = 0 then src else if j = 2 then dst else 0

/-- A framed extension configuration after the source has been copied, in any phase type. -/
private def wordExtCfg {S T : Type} {x : List Bool} (d : Cfg 5 Bool S x)
    (out : List Bool) (src dst : ℤ) (q : T) : Cfg 5 Bool T x where
  state := some q
  inputPos := d.inputPos
  workTapes := wordWrite d 2 out
  workTapePos := wordExtHeads d src dst
  output := d.output

/-- Tagging an extension configuration changes only its phase state. -/
private theorem wordExtCfg_mapState {S T U : Type} {x : List Bool} (d : Cfg 5 Bool S x)
    (out : List Bool) (src dst : ℤ) (q : T) (f : T → U) :
    (wordExtCfg d out src dst q).mapState f = wordExtCfg d out src dst (f q) := by
  rw [Cfg.mapState_eq]
  rfl

/-- Moving both selected heads by one common offset adds it to their frame coordinates. -/
private theorem wordExtHeads_add {S : Type} {x : List Bool} (d : Cfg 5 Bool S x)
    (src dst z : ℤ) :
    (fun j => wordExtHeads d src dst j + if j = 0 ∨ j = 2 then z else 0) =
      wordExtHeads d (src + z) (dst + z) := by
  funext j
  by_cases h₀ : j = 0 <;> by_cases h₂ : j = 2 <;>
    simp [wordExtHeads, h₀, h₂, add_assoc]

/-- Updating either selected head sets its coordinate and preserves the other. -/
private theorem wordExtHeads_update {S : Type} {x : List Bool} (d : Cfg 5 Bool S x)
    (src dst v : ℤ) (i : Fin 5) (hi : i = 0 ∨ i = 2) :
    Function.update (wordExtHeads d src dst) i (d.workTapePos i + v) =
      wordExtHeads d (if i = 0 then v else src) (if i = 2 then v else dst) := by
  rcases hi with rfl | rfl
  all_goals
    funext j
    by_cases h₀ : j = 0 <;> by_cases h₂ : j = 2 <;>
      simp [Function.update_apply, wordExtHeads, h₀, h₂]

/-- A rewind may read the copied prefix even when sign bits occupy its right boundary.

**Proof sketch.** The left blank is unchanged by `wordWrite`. Inside the prefix the patch
reads the concatenated word, whose prefix cells are supplied by `FinTM.bufferTape_take`
and `List.take_left`. No assertion about the cell at the prefix's right boundary is needed. -/
private theorem wordExtCfg_prefix {S T : Type} {x : List Bool} (d : Cfg 5 Bool S x)
    (u v : List Bool) (src dst : ℤ) (q : T)
    (hleft : d.workTapes 2 (d.workTapePos 2 - 1) = none) (p : ℤ)
    (hlo : -1 ≤ p) (hhi : p < (u.length : ℤ)) :
    (wordExtCfg d (u ++ v) src dst q).workTapes 2 (d.workTapePos 2 + p) =
      FinTM.bufferTape u p := by
  dsimp only [wordExtCfg]
  rw [wordWrite_apply]
  by_cases hp : 0 ≤ p
  · rw [if_pos (by
      refine ⟨rfl, by omega, ?_⟩
      simp only [List.length_append]
      omega), add_sub_cancel_left]
    simpa only [List.take_left] using (FinTM.bufferTape_take (u ++ v) u.length hhi).symm
  · have hp' : p = -1 := by omega
    subst p
    rw [if_neg (by omega), FinTM.bufferTape_left]
    simpa only [sub_eq_add_neg] using hleft

/-- The sign fold and framed copy enter the extension's walk row with the original word.

**Proof sketch.** The catalog's sign fold returns the source head and identifies its flag
with `msb`. The framed lockstep copy then writes the low word without inspecting the old
destination. Two applications of the phase segment adapter compose these returning runs;
their four sweeps and two dispatches cost at most `6 * (W + 1)`. -/
private theorem wordExt_sign_copy (a : ℕ) {W : ℕ} {x : List Bool} (u : BitVec W)
    (d : Cfg 5 Bool (Σ p : WordExtStage × Bool, wordExtPh a p) x)
    (hd : d.state = some ⟨(.sign, false), .fwd false⟩) (hu : WordAt d 0 (bvBits u)) :
    ∃ t ≤ 6 * (W + 1), Segment (wordExtTM a) {some ⟨(.done, false), .done false⟩}
      (fun _ => True) d (wordExtCfg d (bvBits u) 0 0 ⟨(.walk, u.msb), .run⟩) t := by
  let exit : Σ p : WordExtStage × Bool, wordExtPh a p := ⟨(.done, false), .done false⟩
  let c₀ := d.mapState fun _ => (ScanPhase.fwd false)
  have hsign := wordFold_run (fun _ b => b) false (bvBits u) c₀
    (by simp only [c₀, Cfg.mapState_state, hd, Option.map_some])
    ((wordAt_mapState d _ 0 _).mpr hu)
  simp only [bvBits_length, bvBits_last_fold] at hsign
  obtain ⟨t₀, ht₀, cut₀, _, run₀⟩ := (reachesWithin_iff _ _ _ _ _ _).mp hsign
  let e₀ : Cfg 5 Bool (ScanPhase Bool) x := {c₀ with state := some (.done u.msb)}
  let d₁ := {d with state := some (⟨(.copy, u.msb), .fwd false⟩ : Σ p, wordExtPh a p)}
  have guard₀ := wordPhase_guard (wordExtRows a) (wordExtRed a) (.sign, false) c₀ t₀
    (wordExtExit a (.sign, false)) cut₀ (wordExtRed_none a (.sign, false))
  have seg₀ : Segment (wordExtTM a) {some exit} (fun _ => True) d d₁ (t₀ + 1) := by
    have hs := wordPhase_segment (wordExtRows a) ⟨(.sign, false), .fwd false⟩ (wordExtRed a)
      (.sign, false) c₀ e₀ t₀ (.done u.msb) ⟨(.copy, u.msb), .fwd false⟩ exit
      (fun _ => True) run₀ rfl rfl guard₀
      (by intro h; cases (congrArg Prod.fst h)) (fun _ _ => True.intro)
    have hstart : {d with state := some (⟨(.sign, false), .fwd false⟩ : Σ p, wordExtPh a p)} = d := by
      rw [← hd]
    simpa only [wordExtTM, c₀, e₀, d₁, Cfg.mapState_eq, hd, Option.map_some, hstart] using hs
  let c₁ := d₁.mapState fun _ => (ScanPhase.fwd false)
  have hu₁ : WordAt c₁ 0 (bvBits u) := (wordAt_mapState d₁ _ 0 _).mpr hu
  have hcopy := wordLock_run 0 0 2 (fun (_ : Bool) bit _ => (false, bit)) false
    (bvBits u) (bvBits u) (bvBits u) (fun _ => false) rfl rfl rfl (fun _ _ => rfl)
    c₁ (by simp only [c₁, d₁, Cfg.mapState_state, Option.map_some]) hu₁ hu₁
  simp only [bvBits_length] at hcopy
  obtain ⟨t₁, ht₁, cut₁, _, run₁⟩ := (reachesWithin_iff _ _ _ _ _ _).mp hcopy
  let e₁ : Cfg 5 Bool (ScanPhase Bool) x :=
    {c₁ with state := some (.done false), workTapes := wordWrite c₁ 2 (bvBits u)}
  have guard₁ := wordPhase_guard (wordExtRows a) (wordExtRed a) (.copy, u.msb) c₁ t₁
    (wordExtExit a (.copy, u.msb)) cut₁ (wordExtRed_none a (.copy, u.msb))
  have seg₁ : Segment (wordExtTM a) {some exit} (fun _ => True) d₁
      (wordExtCfg d (bvBits u) 0 0 ⟨(.walk, u.msb), .run⟩) (t₁ + 1) := by
    have hs := wordPhase_segment (wordExtRows a) ⟨(.sign, false), .fwd false⟩ (wordExtRed a)
      (.copy, u.msb) c₁ e₁ t₁ (.done false) ⟨(.walk, u.msb), .run⟩ exit
      (fun _ => True) run₁ rfl rfl guard₁
      (by intro h; cases (congrArg Prod.fst h)) (fun _ _ => True.intro)
    have hheads : wordExtHeads d 0 0 = d.workTapePos := by
      funext j
      simp only [wordExtHeads, ite_self, add_zero]
    simpa only [wordExtTM, c₁, e₁, d₁, Cfg.mapState_eq, Option.map_some,
      wordExtCfg, hheads] using hs
  exact ⟨t₀ + 1 + (t₁ + 1), by omega, seg₀.trans seg₁⟩

/-- Walking to the source boundary, stepping back, and writing the fixed sign suffix.

**Proof sketch.** The catalog walk moves source and destination together across the source
and its right blank. A single common move places both heads at offset `W`. The constant
writer appends the sign suffix there, returning to the same offset. The framed append lemma
identifies its tape with the full extended word; each catalog exit redirects to the next row. -/
private theorem wordExt_walk_write (a : ℕ) {W : ℕ} {x : List Bool} (u : BitVec W)
    (d : Cfg 5 Bool (Σ p : WordExtStage × Bool, wordExtPh a p) x)
    (hu : WordAt d 0 (bvBits u)) :
    Segment (wordExtTM a) {some ⟨(.done, false), .done false⟩} (fun _ => True)
      (wordExtCfg d (bvBits u) 0 0 ⟨(.walk, u.msb), .run⟩)
      (wordExtCfg d (bvBits u ++ List.replicate a u.msb) W W ⟨(.rewindSource, u.msb), .start⟩)
      (W + 2 * a + 7) := by
  let exit : Σ p : WordExtStage × Bool, wordExtPh a p := ⟨(.done, false), .done false⟩
  let c₀ := wordExtCfg d (bvBits u) 0 0 SeekPhase.run
  let e₀ := wordExtCfg d (bvBits u) ((W : ℤ) + 1) ((W : ℤ) + 1) SeekPhase.done
  have hwalk := walkTM_run_ofCfg 0 (fun j : Fin 5 => j = 0 ∨ j = 2) (Or.inl rfl) 1
    (bvBits u) c₀ rfl (by
      intro p hp
      have h := (wordAt_iff d 0 _).mp hu p (by omega) (by exact_mod_cast hp)
      simpa [c₀, wordExtCfg, wordExtHeads, wordWrite_apply] using h)
  have run₀ : (wordExtRows a (.walk, u.msb)).runFrom c₀ (W + 1) = e₀ := by
    have hr := hwalk.1
    simp only [bvBits_length] at hr
    apply hr.trans
    apply Cfg.ext <;> try rfl
    simpa only [c₀, e₀, wordExtCfg, bvBits_length, SignType.coe_one, one_mul,
      Nat.cast_add, Nat.cast_one, zero_add] using wordExtHeads_add d 0 0 ((W : ℤ) + 1)
  have guard₀ := wordPhase_guard (wordExtRows a) (wordExtRed a) (.walk, u.msb) c₀ (W + 1)
    (wordExtExit a (.walk, u.msb))
    (by intro t ht h; exact hwalk.2.1 t (by simpa only [bvBits_length] using ht) h)
    (wordExtRed_none a (.walk, u.msb))
  have seg₀ := wordPhase_segment (wordExtRows a) ⟨(.sign, false), .fwd false⟩ (wordExtRed a)
    (.walk, u.msb) c₀ e₀ (W + 1) .done ⟨(.back, u.msb), .fwd false⟩ exit
    (fun _ => True) run₀ rfl rfl guard₀
    (by intro h; cases (congrArg Prod.fst h)) (fun _ _ => True.intro)
  simp only [c₀, e₀, wordExtCfg_mapState] at seg₀
  let c₁ := wordExtCfg d (bvBits u) ((W : ℤ) + 1) ((W : ℤ) + 1) (ScanPhase.fwd false)
  let e₁ := wordExtCfg d (bvBits u) W W (ScanPhase.done false)
  have hback := wordMove_run 0 2 2 (-1) c₁ rfl
  obtain ⟨t₁, ht₁, cut₁, _, run₁'⟩ := (reachesWithin_iff _ _ _ _ _ _).mp hback
  have ht₁' : t₁ = 1 := by
    by_contra hn
    have ht : t₁ = 0 := by omega
    have h := congrArg Cfg.state run₁'
    simp only [ht, MultiTapeTM.runFrom_zero, c₁, wordExtCfg] at h
    cases h
  subst t₁
  have run₁ : (wordExtRows a (.back, u.msb)).runFrom c₁ 1 = e₁ := by
    apply run₁'.trans
    apply Cfg.ext <;> try rfl
    simpa only [c₁, e₁, wordExtCfg, SignType.coe_neg, SignType.coe_one,
      or_self, add_neg_cancel_right] using wordExtHeads_add d ((W : ℤ) + 1) ((W : ℤ) + 1) (-1)
  have guard₁ := wordPhase_guard (wordExtRows a) (wordExtRed a) (.back, u.msb) c₁ 1
    (wordExtExit a (.back, u.msb)) cut₁ (wordExtRed_none a (.back, u.msb))
  have seg₁ := wordPhase_segment (wordExtRows a) ⟨(.sign, false), .fwd false⟩ (wordExtRed a)
    (.back, u.msb) c₁ e₁ 1 (.done false) ⟨(.write, u.msb), .wr 0⟩ exit
    (fun _ => True) run₁ rfl rfl guard₁
    (by intro h; cases (congrArg Prod.fst h)) (fun _ _ => True.intro)
  simp only [c₁, e₁, wordExtCfg_mapState] at seg₁
  let c₂ := wordExtCfg d (bvBits u) W W (WritePhase.wr (n := (List.replicate a u.msb).length) 0)
  let e₂ := wordExtCfg d (bvBits u ++ List.replicate a u.msb) W W
    (WritePhase.done (n := (List.replicate a u.msb).length))
  have hwrite := writeConstTM_run_ofCfg 2 (List.replicate a u.msb) c₂ rfl
  have run₂ : (wordExtRows a (.write, u.msb)).runFrom c₂ (2 * a + 2) = e₂ := by
    have hr := hwrite.1
    simp only [List.length_replicate] at hr
    apply hr.trans
    apply Cfg.ext <;> try rfl
    have hwrites : wordWrite c₂ 2 (List.replicate a u.msb) =
        wordWrite d 2 (bvBits u ++ List.replicate a u.msb) :=
      wordWrite_append d 2 (bvBits u) (List.replicate a u.msb) (wordExtHeads d W W)
        (by simp [wordExtHeads, bvBits_length])
    funext j z
    simpa only [wordWrite_apply, e₂, wordExtCfg, List.length_replicate] using
      congrFun (congrFun hwrites j) z
  have guard₂ := wordPhase_guard (wordExtRows a) (wordExtRed a) (.write, u.msb) c₂ (2 * a + 2)
    (wordExtExit a (.write, u.msb))
    (by intro t ht h; exact hwrite.2.1 t (by simpa only [List.length_replicate] using ht) h)
    (wordExtRed_none a (.write, u.msb))
  have seg₂ := wordPhase_segment (wordExtRows a) ⟨(.sign, false), .fwd false⟩ (wordExtRed a)
    (.write, u.msb) c₂ e₂ (2 * a + 2) .done ⟨(.rewindSource, u.msb), .start⟩ exit
    (fun _ => True) run₂ rfl rfl guard₂
    (by intro h; cases (congrArg Prod.fst h)) (fun _ _ => True.intro)
  simp only [c₂, e₂, wordExtCfg_mapState] at seg₂
  have hs := (seg₀.trans seg₁).trans seg₂
  have htime : W + 1 + 1 + (1 + 1) + (2 * a + 2 + 1) = W + 2 * a + 7 := by omega
  simpa only [wordExtTM, htime] using hs

/-- Two catalog rewinds return the source and destination heads without changing the word.

**Proof sketch.** Both heads begin at offset `W`. The source rewind reads the unchanged
source prefix; the destination rewind reads the copied prefix, using `wordExtCfg_prefix`.
The rewind contract deliberately permits an arbitrary current cell, so the sign suffix
need not be crossed. Two returning rows and their dispatches take `2 * W + 6` steps. -/
private theorem wordExt_rewind (a : ℕ) {W : ℕ} {x : List Bool} (u : BitVec W)
    (d : Cfg 5 Bool (Σ p : WordExtStage × Bool, wordExtPh a p) x)
    (hu : WordAt d 0 (bvBits u)) (hleft : d.workTapes 2 (d.workTapePos 2 - 1) = none) :
    Segment (wordExtTM a) {some ⟨(.done, false), .done false⟩} (fun _ => True)
      (wordExtCfg d (bvBits u ++ List.replicate a u.msb) W W ⟨(.rewindSource, u.msb), .start⟩)
      (wordExtCfg d (bvBits u ++ List.replicate a u.msb) 0 0 ⟨(.done, false), .done false⟩)
      (2 * W + 6) := by
  let exit : Σ p : WordExtStage × Bool, wordExtPh a p := ⟨(.done, false), .done false⟩
  let out := bvBits u ++ List.replicate a u.msb
  let c₀ := wordExtCfg d out W W RewindPhase.start
  let e₀ := wordExtCfg d out 0 W RewindPhase.done
  have hsource := rewindTM_run_ofCfg 0 (bvBits u) W (by simp [bvBits_length]) c₀ rfl (by
    intro p hlo hhi
    have h := (wordAt_iff d 0 _).mp hu p hlo (by simp only [bvBits_length]; omega)
    simpa [c₀, wordExtCfg, wordExtHeads, wordWrite_apply] using h)
  have run₀ : (wordExtRows a (.rewindSource, u.msb)).runFrom c₀ (W + 2) = e₀ := by
    apply hsource.1.trans
    apply Cfg.ext <;> try rfl
    change Function.update (wordExtHeads d W W) 0 (wordExtHeads d W W 0 - W) = wordExtHeads d 0 W
    have hz : wordExtHeads d W W 0 - W = d.workTapePos 0 + 0 := by simp [wordExtHeads]
    rw [hz]
    simpa using wordExtHeads_update d W W 0 0 (Or.inl rfl)
  have guard₀ := wordPhase_guard (wordExtRows a) (wordExtRed a) (.rewindSource, u.msb) c₀ (W + 2)
    (wordExtExit a (.rewindSource, u.msb)) hsource.2.1 (wordExtRed_none a (.rewindSource, u.msb))
  have seg₀ := wordPhase_segment (wordExtRows a) ⟨(.sign, false), .fwd false⟩ (wordExtRed a)
    (.rewindSource, u.msb) c₀ e₀ (W + 2) .done ⟨(.rewindDest, u.msb), .start⟩ exit
    (fun _ => True) run₀ rfl rfl guard₀
    (by intro h; cases (congrArg Prod.fst h)) (fun _ _ => True.intro)
  simp only [c₀, e₀, wordExtCfg_mapState] at seg₀
  let c₁ := wordExtCfg d out 0 W RewindPhase.start
  let e₁ := wordExtCfg d out 0 0 RewindPhase.done
  have hdest := rewindTM_run_ofCfg 2 (bvBits u) W (by simp [bvBits_length]) c₁ rfl (by
    intro p hlo hhi
    have h := wordExtCfg_prefix d (bvBits u) (List.replicate a u.msb) 0 W RewindPhase.start
      hleft p hlo (by simpa only [bvBits_length] using hhi)
    simpa [c₁, out, wordExtCfg, wordExtHeads] using h)
  have run₁ : (wordExtRows a (.rewindDest, u.msb)).runFrom c₁ (W + 2) = e₁ := by
    apply hdest.1.trans
    apply Cfg.ext <;> try rfl
    change Function.update (wordExtHeads d 0 W) 2 (wordExtHeads d 0 W 2 - W) = wordExtHeads d 0 0
    have hz : wordExtHeads d 0 W 2 - W = d.workTapePos 2 + 0 := by simp [wordExtHeads]
    rw [hz]
    simpa using wordExtHeads_update d 0 W 0 2 (Or.inr rfl)
  have guard₁ := wordPhase_guard (wordExtRows a) (wordExtRed a) (.rewindDest, u.msb) c₁ (W + 2)
    (wordExtExit a (.rewindDest, u.msb)) hdest.2.1 (wordExtRed_none a (.rewindDest, u.msb))
  have seg₁ := wordPhase_segment (wordExtRows a) ⟨(.sign, false), .fwd false⟩ (wordExtRed a)
    (.rewindDest, u.msb) c₁ e₁ (W + 2) .done exit exit (fun _ => True) run₁ rfl rfl guard₁
    (by intro h; cases (congrArg Prod.fst h)) (fun _ _ => True.intro)
  simp only [c₁, e₁, wordExtCfg_mapState] at seg₁
  have hs := seg₀.trans seg₁
  have htime : W + 2 + 1 + (W + 2 + 1) = 2 * W + 6 := by omega
  simpa only [wordExtTM, out, htime] using hs

/-- **Sign extension by `a` places.** From the entry, with `u` on tape `0`, a word of `W + a`
cells on tape `2` and blank scratch tapes, the row writes `u.signExtend (W + a)` on tape `2`,
within `C·(W + 1)` steps and radius `C·(W + 1)`, tape `1` untouched. The constant `C` depends on
`a`. [AB09, Exercise 1.9]

**Proof sketch.** `wordExt_sign_copy` computes the sign and copies the low word;
`wordExt_walk_write` positions the two heads and appends the fixed sign suffix;
`wordExt_rewind` returns both heads across the copied prefix. The public phase host and
`Segment.trans` compose all seven catalog rows. `wordSignExtend_bits` identifies the result,
and total time bounds displacement. The constant `2 * a + 20` covers width zero as well. -/
theorem exists_wordSignExtendTM (a : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → WordAt d 2 w → w.length = W + a →
        ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit,
                   workTapes := wordWrite d 2 (bvBits (u.signExtend (W + a))) } := by
  refine ⟨(Σ p : WordExtStage × Bool, wordExtPh a p), inferInstance, inferInstance,
    wordExtTM a, ⟨(.sign, false), .fwd false⟩, ⟨(.done, false), .done false⟩, 2 * a + 20, ?_⟩
  intro x W u w d hd hu hw _ _
  have hleft : d.workTapes 2 (d.workTapePos 2 - 1) = none := by
    have h := (wordAt_iff d 2 w).mp hw (-1) le_rfl (by omega)
    simpa only [sub_eq_add_neg, FinTM.bufferTape_left] using h
  obtain ⟨t, ht, hcopy⟩ := wordExt_sign_copy a u d hd hu
  have hs := (segment_iff _ _ _ _ _ _).mp
    ((hcopy.trans (wordExt_walk_write a u d hu)).trans (wordExt_rewind a u d hu hleft))
  have hbound : t + (W + 2 * a + 7) + (2 * W + 6) ≤ (2 * a + 20) * (W + 1) := by
    nlinarith [Nat.zero_le (a * W)]
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t + (W + 2 * a + 7) + (2 * W + 6), hbound, hs.2.1, ?_, ?_⟩
  · intro s hst j
    have hp := (wordExtTM a).workTapePos_runFrom_mem_Icc d s j
    rw [Finset.mem_Icc] at hp
    rw [abs_le]
    constructor <;> omega
  · apply hs.1.trans
    apply Cfg.ext <;> try rfl
    · rw [wordSignExtend_bits]
      rfl
    · funext j
      simp only [wordExtCfg, wordExtHeads, ite_self, add_zero]

/-! ## Finite-state constant words -/

/-- The constant writer counts only up to its fixed table length, then saturates. -/
private def wordConstIndex (n r : ℕ) : Fin (n + 1) := ⟨min r n, by omega⟩

/-- A saturated table emits a natural number's bits, optionally complemented for negatives. -/
private def wordConstStep (n : ℕ) (neg : Bool) (q : Fin (n + 1)) (_ _ : Bool) :
    Fin (n + 1) × Bool :=
  (wordConstIndex n (q.val + 1), if neg then !(n.testBit q.val) else n.testBit q.val)

/-- Saturating the bit table is exact because every bit at or above `n` of `n` is false.

**Proof sketch.** Below the saturation point the counter is the actual cell index. Above it,
`Nat.testBit_lt_two_pow` and `Nat.lt_two_pow_self` make both table and actual bits false.
Core's `getLsbD_ofNat` and `getLsbD_not` then identify the optionally complemented output. -/
private theorem wordConstStep_cell (n : ℕ) (neg : Bool) {N : ℕ} (r : ℕ) (hr : r < N)
    (a b : Bool) :
    wordConstStep n neg (wordConstIndex n r) a b =
      (wordConstIndex n (r + 1),
        (if neg then ~~~(BitVec.ofNat N n) else BitVec.ofNat N n).getLsbD r) := by
  have hbit : n.testBit (min r n) = n.testBit r := by
    by_cases h : r ≤ n
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right (by omega),
        Nat.testBit_lt_two_pow (Nat.lt_two_pow_self (n := n)),
        Nat.testBit_lt_two_pow (lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := r)))]
  apply Prod.ext
  · apply Fin.ext
    simp only [wordConstStep, wordConstIndex, Fin.val_mk]
    omega
  · cases neg
    · change n.testBit (min r n) = (BitVec.ofNat N n).getLsbD r
      rw [hbit, BitVec.getLsbD_ofNat]
      simp only [hr, decide_true, Bool.true_and]
    · change Bool.not (n.testBit (min r n)) = (~~~(BitVec.ofNat N n)).getLsbD r
      rw [hbit, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
      simp only [hr, decide_true, Bool.true_and]

/-- The constant table is one instance of the alias-safe framed sweep, using only tape two.

**Proof sketch.** Use the old destination as both guide and input, and emit the table bit
independently of its symbol. `wordConstStep_cell` gives every transducer cell equation.
The common lockstep run returns the overwritten guide head and preserves every other cell. -/
private theorem wordConst_run (n : ℕ) (neg : Bool) {N : ℕ} {x : List Bool}
    (w : List Bool) (hlen : w.length = N) (d : Cfg 5 Bool (ScanPhase (Fin (n + 1))) x)
    (hd : d.state = some (.fwd (wordConstIndex n 0))) (hw : WordAt d 2 w) :
    ReachesWithin (wordLockTM 2 2 2 (wordConstStep n neg) (wordConstIndex n 0)) d
      {some (.done (wordConstIndex n 0))} (2 * (N + 1)) (2 * (N + 1))
      {d with
        state := some (.done (wordConstIndex n 0))
        workTapes := wordWrite d 2 (bvBits (if neg then ~~~(BitVec.ofNat N n) else BitVec.ofNat N n))} := by
  have h := wordLock_run 2 2 2 (wordConstStep n neg) (wordConstIndex n 0)
    w w (bvBits (if neg then ~~~(BitVec.ofNat N n) else BitVec.ofNat N n)) (wordConstIndex n)
    rfl (by simpa only [bvBits_length] using hlen.symm) rfl
    (by
      intro r hr
      simpa only [bvBits_def, List.getElem_ofFn] using
        wordConstStep_cell n neg (N := N) r (by omega) w[r] w[r]) d hd hw hw
  simpa only [hlen] using h

/-- **The word of an integer constant.** For an integer `c` and `a ≥ 0`: from the entry, with a
word of `W + a` cells on tape `2` and blank scratch tapes, the row writes `BitVec.ofInt (W + a) c`
over it, within `C·(W + 1)` steps and radius `C·(W + 1)`, tapes `0` and `1` untouched. The
constant `C` depends on `c` and `a`. With `a = 0` and `c = 1` this writes the word `1`.
[AB09, Exercise 1.9]

**Proof sketch.** Write `c` as a natural `n` or as `Int.negSucc n`. Core's integer conversion
equations reduce these to `ofNat n` or its complement. `wordConst_run` emits their bits using
the shared alias-safe sweep and the finite saturated table `wordConstStep`; bits at or above
`n` are zero before complementing. The old destination delimits the sweep, which restores its
head. The constant `2 * (a + 1)` covers its `2 * (W + a + 1)` steps and radius. -/
theorem exists_wordIntTM (c : ℤ) (a : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S) (entry exit : S)
      (C : ℕ),
      ∀ {x : List Bool} {W : ℕ} (w : List Bool) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 2 w → w.length = W + a → ScratchBlank d →
        ReachesWithin R d {some exit} (C * (W + 1)) (C * (W + 1))
          { d with state := some exit,
                   workTapes := wordWrite d 2 (bvBits (BitVec.ofInt (W + a) c)) } := by
  obtain ⟨n, neg, hc⟩ : ∃ (n : ℕ) (neg : Bool), ∀ N,
      BitVec.ofInt N c = if neg then ~~~(BitVec.ofNat N n) else BitVec.ofNat N n := by
    cases c with
    | ofNat n => exact ⟨n, false, fun N => BitVec.ofInt_natCast N n⟩
    | negSucc n => exact ⟨n, true, fun _ => BitVec.ofInt_negSucc_eq_not_ofNat⟩
  refine ⟨ScanPhase (Fin (n + 1)), inferInstance, inferInstance,
    wordLockTM 2 2 2 (wordConstStep n neg) (wordConstIndex n 0),
    .fwd (wordConstIndex n 0), .done (wordConstIndex n 0), 2 * (a + 1), ?_⟩
  intro x W w d hd hw hlen _
  have h := wordConst_run n neg w hlen d hd hw
  rw [← hc] at h
  obtain ⟨t, ht, cut, radius, run⟩ := (reachesWithin_iff _ _ _ _ _ _).mp h
  have hbound : 2 * (W + a + 1) ≤ 2 * (a + 1) * (W + 1) := by
    nlinarith [Nat.zero_le (a * W)]
  apply (reachesWithin_iff _ _ _ _ _ _).mpr
  refine ⟨t, ht.trans hbound, cut, ?_, run⟩
  intro s hs j
  exact (radius s hs j).trans (by exact_mod_cast hbound)

/-! ## Tests -/

/-- **The sign test.** From the entry, with `u` on tape `0` and blank scratch tapes, the row stops
at `yes` if `u` is negative read signed (`u.toInt < 0`) and at `no` otherwise, within `C·(W + 1)`
steps and radius `C·(W + 1)`, writing nothing. [AB09, Exercise 1.9]

**Proof sketch.** `wordFold_run` instantiates `scanTM_run_ofCfg` and `scanResult_fold` with
the overwrite fold, preserving the word and returning the head. `bvBits_last_fold` identifies
the verdict with `u.msb`, and `BitVec.msb_eq_toInt` identifies it with the signed comparison.
The initial false flag covers width zero; the catalog's bounds give the constant `2`. -/
theorem exists_wordSignTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S)
      (entry yes no : S) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → ScratchBlank d →
        ReachesWithin R d {some yes, some no} (C * (W + 1)) (C * (W + 1))
          { d with state := some (if u.toInt < 0 then yes else no) } := by
  refine ⟨ScanPhase Bool, inferInstance, inferInstance,
    scanTM 5 0 (scanFold (fun _ b => b)) scanKeep false,
    .fwd false, .done true, .done false, 2, (by intro h; cases h), ?_⟩
  intro x W u d hd hw _
  have h := wordFold_run (fun _ b => b) false (bvBits u) d hd hw
  by_cases hneg : u.toInt < 0 <;>
    simpa only [bvBits_length, bvBits_last_fold, BitVec.msb_eq_toInt, hneg,
      decide_true, decide_false, if_true, if_false] using h

/-- **The zero test.** From the entry, with `u` on tape `0` and blank scratch tapes, the row stops
at `yes` if `u ≠ 0` and at `no` otherwise, within `C·(W + 1)` steps and radius `C·(W + 1)`,
writing nothing. [AB09, Exercise 1.9]

**Proof sketch.** `wordFold_run` applies the read-only `scanTM` fold to Boolean disjunction.
`wordAny_fold` identifies the flag with membership of true, and `bvBits_no_true`, using
`bvBits_injective`, identifies its false case with the zero word. The empty fold is false,
and the same catalog bounds give the constant `2`. -/
theorem exists_wordNonzeroTM :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (R : MultiTapeTM 5 Bool S)
      (entry yes no : S) (C : ℕ), yes ≠ no ∧
      ∀ {x : List Bool} {W : ℕ} (u : BitVec W) (d : Cfg 5 Bool S x),
        d.state = some entry → WordAt d 0 (bvBits u) → ScratchBlank d →
        ReachesWithin R d {some yes, some no} (C * (W + 1)) (C * (W + 1))
          { d with state := some (if u ≠ 0 then yes else no) } := by
  refine ⟨ScanPhase Bool, inferInstance, inferInstance,
    scanTM 5 0 (scanFold (fun a b => a || b)) scanKeep false,
    .fwd false, .done true, .done false, 2, (by intro h; cases h), ?_⟩
  intro x W u d hd hw _
  have hmem : true ∈ bvBits u ↔ u ≠ 0 := by
    simpa only [not_not] using not_congr (bvBits_no_true u)
  have h := wordFold_run (fun a b => a || b) false (bvBits u) d hd hw
  simp only [bvBits_length, wordAny_fold, Bool.false_or, hmem] at h
  by_cases hz : u = (0#W) <;> simpa [hz] using h

end Turing
