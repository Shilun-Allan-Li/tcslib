/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.Sigma.Basic
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Sweep
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to one work tape

[AB09, Claim 1.6]: `k` work tapes are simulated by a single work tape with a quadratic
slowdown.

## Deviations from [AB09]

* [AB09]'s Claim 1.6 merges input, work, *and output* into one single tape (the
  standard model of Sipser's text). Our model structurally always has a separate
  read-only input tape and write-only output tape, so the faithful in-model rendering
  is **one work tape**: the interesting content — interleaving `k` tapes on one, with
  marked head positions and full sweeps — is identical, while the merged-single-tape
  model itself is out of scope (it is a different structure, not an instance of
  `MultiTapeTM`).
* [AB09] states the slowdown as `5k T(n)²`; we existentialize the constant and use
  `(T n + 1)²`.
* The retained structure is a genuinely different model from [AB09]'s merged one, not
  a notational variant: with a separate input tape, palindromes are decidable in
  linear time (`TCSlib.Complexity.ClassP.Examples`), while the merged single-tape
  model has an `Ω(n²)` lower bound for them ([AB09], chapter notes, citing Maass).
  Accordingly, the theorems below are *in-model analogues* of Claim 1.6, and no
  identification with the merged model is claimed anywhere in this development
  (phase-2 audit, finding 5).

## Main results

* `Turing.FinTM.one_work_tape` — [AB09, Claim 1.6] over an enlarged alphabet.
* `Turing.FinTM.one_work_tape_binary` — combined with alphabet reduction
  ([AB09, Claim 1.5]): one work tape *and* binary alphabet, still quadratic.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.6, p. 17; Remark 1.7.)
-/

namespace Turing.FinTM


/-- Add one unused work tape to a machine with no work tapes. -/
private def unusedTapeTM {Γ : Type} (M : FinTM Γ) (hk : M.k = 0) : FinTM Γ where
  k := 1
  State := M.State
  tm :=
    { q₀ := M.tm.q₀
      tr := fun q inp _ =>
        let a := M.tm.tr q inp (fun i => (Fin.cast hk i).elim0)
        ⟨a.inputTape, fun _ => (none, 0), a.output, a.state⟩ }

/-- The unused tape is blank and its head stays at the origin. -/
private def unusedTapeCfg {Γ : Type} (M : FinTM Γ) {x : List Γ}
    (c : Cfg M.k Γ M.State x) : Cfg 1 Γ M.State x :=
  ⟨c.state, c.inputPos, fun _ _ => none, fun _ => 0, c.output⟩

/-- The zero-tape embedding commutes with a single transition, including halt. -/
private lemma unusedTape_step {Γ : Type} (M : FinTM Γ) (hk : M.k = 0)
    {x : List Γ} (c : Cfg M.k Γ M.State x) :
    (unusedTapeTM M hk).tm.step (unusedTapeCfg M c) =
      unusedTapeCfg M (M.tm.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp only [unusedTapeCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (Fin.cast hk i).elim0) = c.workTapeSymbols := by
      funext i
      exact (Fin.cast hk i).elim0
    dsimp only [unusedTapeCfg]
    rw [hs]
    dsimp only [unusedTapeTM]
    rw [hw]
    apply Cfg.ext <;> rfl

/-- The zero-tape path is a lockstep simulation; no sweep or initialization is needed. -/
private lemma unusedTape_computes {Γ : Type} (M : FinTM Γ) (hk : M.k = 0)
    (f : List Γ → List Γ) (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    (unusedTapeTM M hk).ComputesFunInTime f T := by
  intro x
  have hr := MultiTapeTM.runFrom_comm_of_step (unusedTapeCfg M)
    (unusedTape_step M hk) (M.tm.initCfg x) (T x.length)
  have hi : unusedTapeCfg M (M.tm.initCfg x) = (unusedTapeTM M hk).tm.initCfg x := rfl
  rw [hi] at hr
  obtain ⟨hs, ho⟩ := (computesInTime_iff M x (f x) (T x.length)).mp (hM x)
  apply (computesInTime_iff _ _ _ _).mpr
  rw [hr]
  exact ⟨hs, ho⟩

/-- A cell stores a tape index, an optional payload, the head flag, and the
left-neighbor head flag recorded by the forward sweep. -/
private abbrev SweepCell (Γ : Type) (k : ℕ) := Fin k × (Option Γ × Bool × Bool)

/-- The forward rule reads marked payloads and records the preceding head flag. -/
private def readVisit {Γ : Type} {k : ℕ} :
    (Fin k → Option Γ × Bool) → SweepCell Γ k →
      (Fin k → Option Γ × Bool) × SweepCell Γ k :=
  indexedVisit fun _ s a => ((if a.2.1 then a.1 else s.1, a.2.1),
    (a.1, a.2.1, s.2))

/-- The return rule writes the old head's payload and determines the new head
from the old flags at its left, current, and right neighbors. -/
private def writeVisit {Γ S : Type} {k : ℕ} (act : Action k Γ S) :
    (Fin k → Bool) → SweepCell Γ k → (Fin k → Bool) × SweepCell Γ k :=
  indexedVisit fun i right a =>
    (a.2.1, (if a.2.1 then (act.workTapes i).1.getD a.1 else a.1,
      (match (act.workTapes i).2 with
        | .neg => right
        | .zero => a.2.1
        | .pos => a.2.2), false))

/-- The ghost head flag at a source coordinate. -/
private def headAt {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (i : Fin k) (j : ℤ) : Bool := decide (c.workTapePos i = j)

/-- One interleaved block; `read = true` includes the recorded left flag. -/
private def tapeRow {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (read : Bool) : List (SweepCell Γ k) :=
  (List.finRange k).map fun i =>
    (i, c.workTapes i j, headAt c i j, if read then headAt c i (j - 1) else false)

/-- The forward control immediately before reading block `j`. -/
private def readState {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) : Fin k → Option Γ × Bool := fun i =>
  (if c.workTapePos i < j then c.workTapeSymbols i else none, headAt c i (j - 1))

/-- Reading a whole block advances the control invariant by one coordinate. -/
private lemma read_row {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) :
    sweepFold readVisit (readState c j) (tapeRow c j false) =
      (readState c (j + 1), tapeRow c j true) := by
  unfold readVisit tapeRow
  rw [indexedFold_block]
  apply Prod.ext
  · funext i
    dsimp only [readState]
    apply Prod.ext
    · dsimp only
      by_cases he : c.workTapePos i = j
      · simp [headAt, he, Cfg.workTapeSymbols]
      · have hlt : c.workTapePos i < j + 1 ↔ c.workTapePos i < j := by omega
        simp [headAt, he, hlt]
    · simp [headAt]
  · rfl

/-- A return-sweep block performs exactly the source action on that coordinate.
**Proof sketch.** A payload changes only at its old head. A new head at `j`
comes from `j+1`, `j`, or `j-1`, according to its movement; these are exactly
the right-control, current-cell, and stored-left flags. -/
private lemma write_row {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (act : Action k Γ S) (j : ℤ) :
    sweepFold (writeVisit act) (fun i => headAt c i (j + 1)) (tapeRow c j true).reverse =
      (fun i => headAt c i j, (tapeRow (act.apply c) j false).reverse) := by
  unfold writeVisit tapeRow
  rw [indexedFold_block_reverse]
  apply Prod.ext
  · rfl
  · dsimp only
    congr 1
    apply List.map_congr_left
    intro i _
    refine Prod.ext (by rfl) ?_
    apply Prod.ext
    · dsimp only
      by_cases he : c.workTapePos i = j
      · cases hw : (act.workTapes i).1 <;>
          simp [headAt, he, Action.apply, hw, Function.update_apply]
      · have he' : j ≠ c.workTapePos i := Ne.symm he
        cases hw : (act.workTapes i).1 <;> simp [headAt, he, he', Action.apply, hw]
    · dsimp only
      refine Prod.ext ?_ (by rfl)
      dsimp only
      cases hm : (act.workTapes i).2 <;>
        simp only [headAt, Action.apply, hm, SignType.cast]
      all_goals simp only [↓reduceIte, decide_eq_decide]; omega

/-- Consecutive interleaved blocks, in ascending coordinate order. -/
private def tapeZone {C : Type} (row : ℤ → List C) (j : ℤ) : ℕ → List C
  | 0 => []
  | n + 1 => row j ++ tapeZone row (j + 1) n

/-- The forward sweep processes any consecutive block interval. -/
private lemma read_zone {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (n : ℕ) :
    sweepFold readVisit (readState c j) (tapeZone (fun z => tapeRow c z false) j n) =
      (readState c (j + n), tapeZone (fun z => tapeRow c z true) j n) := by
  induction n generalizing j with
  | zero => simp [tapeZone, sweepFold]
  | succ n ih =>
    simp only [tapeZone, sweepFold_append, read_row, ih]
    congr 2
    omega

/-- The return sweep processes the same interval in reverse order. -/
private lemma write_zone {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (act : Action k Γ S) (j : ℤ) (n : ℕ) :
    sweepFold (writeVisit act) (fun i => headAt c i (j + n))
      (tapeZone (fun z => tapeRow c z true) j n).reverse =
      (fun i => headAt c i j,
        (tapeZone (fun z => tapeRow (act.apply c) z false) j n).reverse) := by
  induction n generalizing j with
  | zero => simp [tapeZone, sweepFold]
  | succ n ih =>
    have he : j + (n + 1 : ℕ) = j + 1 + n := by omega
    simp only [tapeZone, List.reverse_append, sweepFold_append, he, ih]
    rw [write_row]

/-- An enlarged symbol is input/output data, an internal cell, or a boundary. -/
private abbrev SweepAlphabet (Γ : Type) (k : ℕ) := Γ ⊕ Option (SweepCell Γ k)

/-- Encode a source symbol as an unmarked data symbol. -/
private def sweepEmbed (Γ : Type) (k : ℕ) : Γ ↪ SweepAlphabet Γ k :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- A nonblank internal boundary, distinct from every payload (including blank). -/
private def sweepBoundary {Γ : Type} {k : ℕ} : SweepAlphabet Γ k := .inr none

/-- Tag a complete internal cell. -/
private def sweepSymbol {Γ : Type} {k : ℕ} (c : SweepCell Γ k) : SweepAlphabet Γ k :=
  .inr (some c)

/-- Interpret the unchanged native input alphabet. -/
private def sweepInput {Γ : Type} {k : ℕ} : Option (SweepAlphabet Γ k) → Option Γ
  | some (.inl a) => some a
  | _ => none

/-- Finite controller phases; unbounded coordinates never enter the state. -/
private inductive SweepState (Γ S : Type) (k : ℕ) where
  | init : Fin (k + 1) → SweepState Γ S k
  | back : SweepState Γ S k
  | growLeft : S → Fin (k + 1) → SweepState Γ S k
  | read : S → (Fin k → Option Γ × Bool) → SweepState Γ S k
  | growRight : S → (Fin k → Option Γ × Bool) → Fin (k + 1) → SweepState Γ S k
  | write : S → Option Γ → (Fin k → Option Γ) → (Fin k → Bool) → SweepState Γ S k

/-- Enumerate the finite control through its finite sum/product representation. -/
private instance sweepStateFintype (Γ S : Type) [Fintype Γ] [Fintype S] (k : ℕ) :
    Fintype (SweepState Γ S k) := derive_fintype% _

/-- Equality of controller states is decidable through the same representation. -/
private instance sweepStateDecidableEq (Γ S : Type) [DecidableEq Γ] [DecidableEq S] (k : ℕ) :
    DecidableEq (SweepState Γ S k) :=
  -- The nested sum/sigma representation exceeds the default instance-size bound.
  set_option synthInstance.maxSize 8192 in
  (proxy_equiv% (SweepState Γ S k)).symm.decidableEq

/-- A stationary-input/output action that preserves the cell it scans. -/
private def sweepMove {A S : Type} (q : Option S) (d : SignType) : Action 1 A S :=
  ⟨0, fun _ => (none, d), none, q⟩

/-- The finite controller for the two sweeps and their boundary extensions.
The forward sweep records left-neighbor flags in the cells. The backward sweep
keeps right-neighbor flags in its control, so it needs no extra scan. -/
private def sweepTM {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) : FinTM (SweepAlphabet Γ M.k) where
  k := 1
  State := SweepState Γ M.State M.k
  tm :=
    { q₀ := .init 0
      tr := fun q inp work =>
        match q with
        | .init i =>
          if h : i.val < M.k then
            sweepAct (.init ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨i.val, h⟩, none, true, false))) .pos
          else
            sweepAct .back (some sweepBoundary) .neg
        | .back =>
          match work 0 with
          | none => sweepAct (.growLeft M.tm.q₀ 0) (some sweepBoundary) .zero
          | some a => sweepAct .back (some a) .neg
        | .growLeft q i =>
          if h : i.val < M.k then
            sweepAct (.growLeft q ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨M.k - 1 - i.val, by omega⟩, none, false, false))) .neg
          else
            sweepAct (.read q (fun _ => (none, false))) (some sweepBoundary) .pos
        | .read q s =>
          match work 0 with
          | some (.inr (some c)) =>
            let v := readVisit s c
            sweepAct (.read q v.1) (some (sweepSymbol v.2)) .pos
          | _ => sweepMove (some (.growRight q s 0)) .zero
        | .growRight q s i =>
          if h : i.val < M.k then
            sweepAct (.growRight q s ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨i.val, h⟩, none, false, (s ⟨i.val, h⟩).2))) .pos
          else
            let a := M.tm.tr q (sweepInput inp) (fun i => (s i).1)
            ⟨a.inputTape, fun _ => (some (some sweepBoundary), .neg),
              a.output.map Sum.inl,
              some (.write q (sweepInput inp) (fun i => (s i).1) (fun _ => false))⟩
        | .write q inp reads right =>
          let a := M.tm.tr q inp reads
          match work 0 with
          | some (.inr (some c)) =>
            let v := writeVisit a right c
            sweepAct (.write q inp reads v.1) (some (sweepSymbol v.2)) .neg
          | _ => sweepMove (a.state.map (fun q => .growLeft q 0)) .zero }

/-- The initialized interleaving has `k` marked blank cells. -/
private def blankRow {Γ : Type} (k : ℕ) (mark : Bool) : List (SweepCell Γ k) :=
  (List.finRange k).map fun i => (i, none, mark, false)

/-- A row outside both the source heads and the written support is blank. -/
private lemma tapeRow_blank {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (hp : ∀ i, c.workTapePos i ≠ j)
    (ht : ∀ i, c.workTapes i j = none) :
    tapeRow c j false = blankRow k false := by
  unfold tapeRow blankRow
  apply List.map_congr_left
  intro i _
  simp [headAt, hp i, ht i]

/-- The size of each block is the number of source tapes. -/
private lemma tapeRow_length {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (b : Bool) : (tapeRow c j b).length = k := by
  simp [tapeRow]

/-- Zone length is the block count times the source tape count. -/
private lemma tapeZone_length {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (n : ℕ) (b : Bool) :
    (tapeZone (fun z => tapeRow c z b) j n).length = n * k := by
  induction n generalizing j with
  | zero => simp [tapeZone]
  | succ n ih =>
    simp only [tapeZone, List.length_append, tapeRow_length, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- Split a zone at a block boundary. -/
private lemma tapeZone_append {C : Type} (row : ℤ → List C) (j : ℤ) (n m : ℕ) :
    tapeZone row j (n + m) = tapeZone row j n ++ tapeZone row (j + n) m := by
  induction n generalizing j with
  | zero => simp [tapeZone]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [tapeZone, ih, List.append_assoc]
    rw [show j + 1 + (n : ℤ) = j + (n + 1 : ℕ) by omega]

/-- The native input position is unchanged numerically by symbol embedding. -/
private def sweepPos {Γ : Type} {x : List Γ} (k : ℕ) (p : Fin (x.length + 2)) :
    Fin ((x.map (sweepEmbed Γ k)).length + 2) :=
  ⟨p.val, by simpa only [List.length_map] using p.isLt⟩

/-- Input-head movement commutes with the unchanged-length symbol embedding. -/
private lemma sweepPos_move {Γ : Type} {x : List Γ} (k : ℕ)
    (p : Fin (x.length + 2)) (d : SignType) :
    moveInputPos (sweepPos k p) d = sweepPos k (moveInputPos p d) := by
  apply Fin.ext
  simp only [moveInputPos, sweepPos, List.length_map]
  split <;> rfl

/-- The input read by an encoded configuration is the encoded source read. -/
private lemma sweepInput_read {Γ S S' : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (d : Cfg 1 (SweepAlphabet Γ k) S' (x.map (sweepEmbed Γ k)))
    (hp : d.inputPos = sweepPos k c.inputPos) :
    sweepInput d.inputSymbol = c.inputSymbol := by
  have hzero : sweepPos k c.inputPos = 0 ↔ c.inputPos = 0 := by
    simp only [Fin.ext_iff, sweepPos, Fin.val_zero]
  have hv : (sweepPos k c.inputPos).val = c.inputPos.val := rfl
  simp only [Cfg.inputSymbol, hp, hzero, hv, List.length_map]
  split
  · rfl
  · split
    · rfl
    · simp only [List.getElem_map, sweepEmbed, Function.Embedding.coeFn_mk, sweepInput]

/-- Canonical configurations at the left boundary between simulated steps. -/
private def sweepStart {Γ : Type} [Fintype Γ] [DecidableEq Γ] (M : FinTM Γ)
    {x : List Γ} (c : Cfg M.k Γ M.State x) (j : ℤ) (n : ℕ) (z : ℤ) :
    Cfg 1 (SweepAlphabet Γ M.k) (SweepState Γ M.State M.k)
      (x.map (sweepEmbed Γ M.k)) :=
  sweepRevCfg (c.state.map (fun q => .growLeft q 0)) (sweepPos M.k c.inputPos) z
    ((tapeZone (fun j => tapeRow c j false) j n).map (fun a => some (sweepSymbol a)) ++
      [some sweepBoundary]) [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k))

/-- Replacing the current cell preserves both tails of the zipper. -/
private lemma sweepTape_write {A : Type} (z : ℤ) (l r : List (Option A)) (b : Option A) :
    Function.update (sweepTape z l r) z b = sweepTape z l (b :: r.tail) := by
  funext p
  by_cases hp : p = z
  · subst p
    simp [sweepTape_read]
  · rw [Function.update_of_ne hp]
    by_cases h : p < z
    · simp only [sweepTape, if_pos h]
    · have he : (p - z).toNat = (p - z - 1).toNat + 1 := by omega
      simp only [sweepTape, if_neg h, he, List.getElem?_cons_succ]
      cases r <;> rfl

/-- Write a boundary and turn from a forward scan into a backward scan. -/
private lemma sweep_turn_left {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b emit : Option A) (di : SignType) :
    (⟨di, fun _ => (some b, .neg), emit, q'⟩ : Action 1 A S).apply
      (sweepCfg q p z l r out) =
    sweepRevCfg q' (moveInputPos p di) (z - 1) (b :: r.tail) l (out ++ emit.toList) := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i w
  change Function.update (sweepTape z l r) z b w = _
  rw [sweepTape_write, sweepTape_turn]
  rfl

/-- Write the left boundary and turn toward the first forward-scan cell. -/
private lemma sweep_turn_right {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .pos).apply (sweepRevCfg q p z l r out) =
      sweepCfg (some q') p (z + 1) (b :: r.tail) l out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ rfl (List.append_nil _)
  funext i w
  have h := congrFun (sweepTape_write (-z) l r b) (-w)
  have ht := congrFun (sweepTape_turn (z + 1) (b :: r.tail) l) w
  have he : z + 1 - 1 = z := by omega
  rw [he] at ht
  change Function.update (fun w => sweepTape (-z) l r (-w)) z b w =
    sweepTape (z + 1) (b :: r.tail) l w
  rw [ht]
  simpa only [Function.update_apply, neg_inj] using h

/-- Initialization writes the marked origin block in exactly `k` steps. -/
private lemma sweep_init_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepCfg (some (.init 0)) p z l r out) M.k =
      sweepCfg (some (.init ⟨M.k, by omega⟩)) p (z + M.k)
        (((blankRow M.k true).map (fun a => some (sweepSymbol a))).reverse ++ l)
        (r.drop M.k) out := by
  let w := (blankRow (Γ := Γ) M.k true).map sweepSymbol
  have hw : w.length = M.k := by simp [w, blankRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepCfg (some (.init ⟨i.val, by simpa [hw] using i.isLt⟩)) p z l r out)
    1 (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_map] using h
  · have hik : i < M.k := by omega
    change (sweepTM M).tm.step (sweepCfg (some (.init ⟨i, by omega⟩)) p z l r out) = _
    change ((sweepTM M).tm.tr (.init ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨i, hik⟩, none, true, false) := by
      simp [w, blankRow]
    rw [he]
    exact sweepCfg_right_any _ _ p z l r out _

/-- Growing the left boundary writes exactly one reversed blank block. -/
private lemma sweep_grow_left_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (q : M.State) {x : List (SweepAlphabet Γ M.k)}
    (p : Fin (x.length + 2)) (out : List (SweepAlphabet Γ M.k))
    (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepRevCfg (some (.growLeft q 0)) p z l r out) M.k =
      sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
        ((blankRow M.k false).map (fun a => some (sweepSymbol a)) ++ l)
        (r.drop M.k) out := by
  let w := ((blankRow (Γ := Γ) M.k false).map sweepSymbol).reverse
  have hw : w.length = M.k := by simp [w, blankRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepRevCfg (some (.growLeft q ⟨i.val, by simpa [hw] using i.isLt⟩))
      p z l r out) (-1) (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_reverse, List.map_map, sub_eq_add_neg] using h
  · have hik : i < M.k := by omega
    change (sweepTM M).tm.step (sweepRevCfg (some (.growLeft q ⟨i, by omega⟩)) p z l r out) = _
    change ((sweepTM M).tm.tr (.growLeft q ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨M.k - 1 - i, by omega⟩, none, false, false) := by
      simp [w, blankRow, List.getElem_reverse]
    rw [he]
    exact sweepRevCfg_left_any _ _ p z l r out _

/-- The right guard block records the flags from the last scanned block. -/
private def rightRow {Γ : Type} {k : ℕ} (s : Fin k → Option Γ × Bool) :
    List (SweepCell Γ k) := (List.finRange k).map fun i => (i, none, false, (s i).2)

/-- Growing the right boundary writes one guard block, retaining the collected reads. -/
private lemma sweep_grow_right_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (q : M.State) (s : Fin M.k → Option Γ × Bool)
    {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepCfg (some (.growRight q s 0)) p z l r out) M.k =
      sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        (((rightRow s).map (fun a => some (sweepSymbol a))).reverse ++ l)
        (r.drop M.k) out := by
  let w := (rightRow s).map sweepSymbol
  have hw : w.length = M.k := by simp [w, rightRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepCfg (some (.growRight q s ⟨i.val, by simpa [hw] using i.isLt⟩))
      p z l r out) 1 (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_map] using h
  · have hik : i < M.k := by omega
    change ((sweepTM M).tm.tr (.growRight q s ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨i, hik⟩, none, false, (s ⟨i, hik⟩).2) := by
      simp [w, rightRow]
    rw [he]
    exact sweepCfg_right_any _ _ p z l r out _

/-- A sweep with the identity rule only changes the physical scan frontier. -/
private lemma sweepFold_id {R C : Type} (s : R) (as : List C) :
    sweepFold (fun s a => (s, a)) s as = (s, as) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [sweepFold, ih]

/-- Writing without moving in a backward-facing zipper. -/
private lemma sweepRevCfg_write {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .zero).apply (sweepRevCfg q p z l r out) =
      sweepRevCfg (some q') p z l (b :: r.tail) out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i w
    have h := congrFun (sweepTape_write (-z) l r b) (-w)
    change Function.update (fun w => sweepTape (-z) l r (-w)) z b w = _
    simpa only [Function.update_apply, neg_inj] using h
  · funext i
    exact add_zero z

/-- Initialization builds the marked origin block and both boundaries.
**Proof sketch.** Write `k` marked blank cells, write the right boundary and
turn left, traverse the same `k` cells without altering them, then write the
left boundary. All four phases preserve the native input and output. -/
private lemma sweep_init {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List Γ) :
    (sweepTM M).tm.runFrom ((sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k))) (2 * M.k + 2) =
      sweepStart M (M.tm.initCfg x) 0 1 (-1) := by
  let p := sweepPos M.k (M.tm.initCfg x).inputPos
  let B := (blankRow (Γ := Γ) M.k true).map (fun a => some (sweepSymbol a))
  have hlen : (blankRow (Γ := Γ) M.k true).length = M.k := by simp [blankRow]
  have hp : p = 1 := by apply Fin.ext; simp [p, sweepPos]
  have hinit : (sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k)) =
      sweepCfg (some (.init 0)) p 0 [] [] [] := by
    refine Cfg.ext rfl hp.symm ?_ rfl rfl
    funext i z
    simp [sweepCfg, sweepTape]
  have hturn : (sweepTM M).tm.step
      (sweepCfg (some (.init ⟨M.k, by omega⟩)) p M.k B.reverse [] []) =
      sweepRevCfg (some .back) p ((M.k : ℤ) - 1) [some sweepBoundary] B.reverse [] := by
    change ((sweepTM M).tm.tr (.init ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    simpa only [sweepAct, SignType.zero_eq_zero, moveInputPos_zero, List.tail_nil,
      Option.toList_none, List.append_nil] using
      sweep_turn_left (S := SweepState Γ M.State M.k)
        (some (.init ⟨M.k, by omega⟩)) (some .back) p (M.k : ℤ)
        B.reverse [] [] (some sweepBoundary) none .zero
  have hback := sweep_run_reverse (sweepTM M).tm (fun _ : Unit => SweepState.back)
    sweepSymbol (fun s a => (s, a)) (by intro s a inp; rfl) p []
    (blankRow (Γ := Γ) M.k true).reverse () ((M.k : ℤ) - 1) [some sweepBoundary] []
  have hback' : (sweepTM M).tm.runFrom
      (sweepRevCfg (some .back) p ((M.k : ℤ) - 1) [some sweepBoundary] B.reverse []) M.k =
      sweepRevCfg (some .back) p (-1) (B ++ [some sweepBoundary]) [] [] := by
    simpa [B, List.map_reverse, hlen, sweepFold_id] using hback
  have hlast : (sweepTM M).tm.step
      (sweepRevCfg (some .back) p (-1) (B ++ [some sweepBoundary]) [] []) =
      sweepRevCfg (some (.growLeft M.tm.q₀ 0)) p (-1)
        (B ++ [some sweepBoundary]) [some sweepBoundary] [] := by
    have hr : (sweepRevCfg (some (SweepState.back (Γ := Γ) (S := M.State) (k := M.k)))
        p (-1) (B ++ [some sweepBoundary]) [] []).workTapeSymbols = fun _ => none := by
      funext i
      simp [Cfg.workTapeSymbols, sweepRevCfg, sweepTape]
    change ((sweepTM M).tm.tr .back _ _).apply _ = _
    rw [hr]
    exact sweepRevCfg_write _ _ _ _ _ _ _ _
  rw [show 2 * M.k + 2 = (M.k + 1) + M.k + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step', hinit, sweep_init_block]
  simp only [zero_add, List.append_nil, List.drop_nil]
  rw [hturn, hback', hlast]
  congr 1
  simp [tapeZone, tapeRow, blankRow, headAt, B]

/-- A stationary phase change preserves a forward-facing tape. -/
private lemma sweepCfg_stay {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepMove q' .zero).apply (sweepCfg q p z l r out) = sweepCfg q' p z l r out := by
  apply Cfg.ext <;> simp [sweepMove, sweepCfg, Action.apply]

/-- A stationary phase change preserves a backward-facing tape. -/
private lemma sweepRevCfg_stay {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepMove q' .zero).apply (sweepRevCfg q p z l r out) = sweepRevCfg q' p z l r out := by
  apply Cfg.ext <;> simp [sweepMove, sweepRevCfg, Action.apply]

/-- The first half of a simulated step grows the left guard and collects all
marked source symbols. Its exact cost includes both phase changes.
**Proof sketch.** The head lower bound makes the new left block blank and gives
the empty initial read table. Write that block, place the new boundary, and turn.
The forward transduction processes all blocks through the old right edge,
recording the marked symbols and left-neighbor flags. A stationary boundary
transition enters the right-extension phase. Concatenate these four runs. -/
private lemma sweep_prepare {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (hs : c.state = some q) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, a ≤ c.workTapePos i)
    (hl : ∀ i, c.workTapes i (a - 1) = none) :
    (sweepTM M).tm.runFrom (sweepStart M c a n z)
      (M.k + 1 + (n + 1) * M.k + 1) =
    sweepCfg (some (.growRight q (readState c (a + n)) 0)) (sweepPos M.k c.inputPos)
      (z - M.k + 1 + ((n + 1) * M.k : ℕ))
      (((tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)).map
        (fun b => some (sweepSymbol b))).reverse ++ [some sweepBoundary])
      [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)) := by
  let p := sweepPos M.k c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let D := (tapeZone (fun j => tapeRow c j false) a n).map (fun b => some (sweepSymbol b))
  let F := tapeZone (fun j => tapeRow c j false) (a - 1) (n + 1)
  let R := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)
  have hf : F = blankRow M.k false ++ tapeZone (fun j => tapeRow c j false) a n := by
    dsimp [F]
    rw [tapeZone, show a - 1 + 1 = a by omega,
      tapeRow_blank c (a - 1) (fun i => by have := hp i; omega) hl]
  have hr0 : readState c (a - 1) = fun _ => (none, false) := by
    funext i
    have h := hp i
    simp only [readState, headAt]
    rw [if_neg (by omega)]
    simp [show c.workTapePos i ≠ a - 1 - 1 by omega]
  have hdrop : ([some (sweepBoundary (Γ := Γ) (k := M.k))] : List _).drop M.k = [] := by
    apply List.drop_eq_nil_of_le
    simpa using hk
  have hturn : (sweepTM M).tm.step
      (sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
        ((blankRow M.k false).map (fun b => some (sweepSymbol b)) ++ (D ++ [some sweepBoundary]))
        [] out) =
      sweepCfg (some (.read q (readState c (a - 1)))) p (z - M.k + 1)
        [some sweepBoundary] (F.map (fun b => some (sweepSymbol b)) ++ [some sweepBoundary]) out := by
    change ((sweepTM M).tm.tr (.growLeft q ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    rw [sweep_turn_right]
    simp only [hr0, hf, List.map_append, List.append_assoc, D, List.tail_nil]
  have hread := sweep_run (sweepTM M).tm (fun s => SweepState.read q s) sweepSymbol readVisit
    (by intro s b inp; rfl) p out F (readState c (a - 1)) (z - M.k + 1)
    [some sweepBoundary] [some sweepBoundary]
  have hfold : sweepFold readVisit (readState c (a - 1)) F =
      (readState c (a + n), R) := by
    simpa [F, R, show a - 1 + (n + 1 : ℕ) = a + n by omega] using
      read_zone c (a - 1) (n + 1)
  have hflen : F.length = (n + 1) * M.k := tapeZone_length c _ _ _
  rw [hfold, hflen] at hread
  have hend : (sweepTM M).tm.step
      (sweepCfg (some (.read q (readState c (a + n)))) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out) =
      sweepCfg (some (.growRight q (readState c (a + n)) 0)) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out := by
    have hsym : (sweepCfg (some (SweepState.read q (readState c (a + n)))) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out).workTapeSymbols = fun _ => some sweepBoundary := by
      funext i
      exact sweepTape_read _ _ _
    change ((sweepTM M).tm.tr (.read q (readState c (a + n))) _ _).apply _ = _
    rw [hsym]
    exact sweepCfg_stay _ _ _ _ _ _ _
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step']
  unfold sweepStart
  rw [hs]
  dsimp only [Option.map]
  rw [sweep_grow_left_block, hdrop]
  change (sweepTM M).tm.step ((sweepTM M).tm.runFrom
    ((sweepTM M).tm.step (sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
      ((blankRow M.k false).map (fun b => some (sweepSymbol b)) ++ (D ++ [some sweepBoundary]))
      [] out)) ((n + 1) * M.k)) = _
  rw [hturn, hread]
  exact hend

/-- The second half grows the right guard, executes the native input/output
action once, rewrites the zone, and enters the next boundary configuration.
**Proof sketch.** The head upper bound identifies the completed read table with
the source's scanned symbols. Append a blank right block carrying the last
block's head flags, then place its boundary and perform the source input/output
action while turning left. The reverse transduction applies the source action
to every block. At the left boundary, install the next source state (or halt),
and identify the resulting zipper with the enlarged canonical zone. -/
private lemma sweep_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, c.workTapePos i < a + n)
    (hr : ∀ i, c.workTapes i (a + n) = none) :
    (sweepTM M).tm.runFrom
      (sweepCfg (some (.growRight q (readState c (a + n)) 0)) (sweepPos M.k c.inputPos) z
        (((tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)).map
          (fun b => some (sweepSymbol b))).reverse ++ [some sweepBoundary])
        [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)))
      (M.k + 1 + (n + 2) * M.k + 1) =
    sweepStart M ((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c) (a - 1) (n + 2)
      (z + M.k - 1 - ((n + 2) * M.k : ℕ)) := by
  let act := M.tm.tr q c.inputSymbol c.workTapeSymbols
  let p := sweepPos M.k c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let s := readState c (a + n)
  let R := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)
  let W := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 2)
  let V := tapeZone (fun j => tapeRow (act.apply c) j false) (a - 1) (n + 2)
  let put : SweepCell Γ M.k → Option (SweepAlphabet Γ M.k) := fun b => some (sweepSymbol b)
  let p' := sweepPos M.k (act.apply c).inputPos
  let out' := (act.apply c).output.map (sweepEmbed Γ M.k)
  have hrs : (fun i => (s i).1) = c.workTapeSymbols := by
    funext i
    simp only [s, readState, if_pos (hp i)]
  have hrow : rightRow s = tapeRow c (a + n) true := by
    unfold rightRow tapeRow
    apply List.map_congr_left
    intro i _
    have hh : c.workTapePos i ≠ a + n := by have := hp i; omega
    simp [s, readState, hr i, headAt, hh]
  have hwhole : W = R ++ rightRow s := by
    rw [hrow]
    dsimp [W, R]
    rw [show n + 2 = (n + 1) + 1 by omega, tapeZone_append]
    simp only [tapeZone, List.append_nil]
    rw [show a - 1 + (n + 1 : ℕ) = a + n by omega]
  have hbuf : (((rightRow s).map put).reverse.append ((R.map put).reverse ++ [some sweepBoundary])) =
      (W.map put).reverse ++ [some sweepBoundary] := by
    rw [hwhole]
    simp [List.map_append, List.reverse_append, List.append_assoc]
  have hdrop : ([some (sweepBoundary (Γ := Γ) (k := M.k))] : List _).drop M.k = [] := by
    apply List.drop_eq_nil_of_le
    simpa using hk
  have hturn : (sweepTM M).tm.step
      (sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        ((W.map put).reverse ++ [some sweepBoundary]) [] out) =
      sweepRevCfg (some (.write q c.inputSymbol c.workTapeSymbols (fun _ => false)))
        p' (z + M.k - 1) [some sweepBoundary] ((W.map put).reverse ++ [some sweepBoundary]) out' := by
    have hin := sweepInput_read c
      (sweepCfg (some (SweepState.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        ((W.map put).reverse ++ [some sweepBoundary]) [] out) rfl
    change ((sweepTM M).tm.tr (.growRight q s ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    rw [hin, hrs]
    change (⟨act.inputTape, fun _ => (some (some sweepBoundary), .neg),
      act.output.map Sum.inl, some (.write q c.inputSymbol c.workTapeSymbols (fun _ => false))⟩ :
      Action 1 (SweepAlphabet Γ M.k) (SweepState Γ M.State M.k)).apply _ = _
    rw [sweep_turn_left]
    have hm : moveInputPos p act.inputTape = p' := sweepPos_move _ _ _
    rw [hm]
    have ho : out ++ (act.output.map Sum.inl).toList = out' := by
      dsimp [out, out', Action.apply]
      cases act.output <;> simp [sweepEmbed, List.map_append]
    rw [ho]
    rfl
  have hzero : (fun i => headAt c i (a - 1 + (n + 2 : ℕ))) = fun _ => false := by
    funext i
    have hh : c.workTapePos i ≠ a - 1 + (n + 2 : ℕ) := by have := hp i; omega
    simpa only [headAt, decide_eq_false_iff_not] using hh
  have hfold : sweepFold (writeVisit act) (fun _ => false) W.reverse =
      (fun i => headAt c i (a - 1), V.reverse) := by
    have h := write_zone c act (a - 1) (n + 2)
    rw [hzero] at h
    exact h
  have hwlen : W.length = (n + 2) * M.k := tapeZone_length c _ _ _
  have hwrite := sweep_run_reverse (sweepTM M).tm
    (fun right => SweepState.write q c.inputSymbol c.workTapeSymbols right)
    sweepSymbol (writeVisit act) (by intro right b inp; rfl) p' out'
    W.reverse (fun _ => false) (z + M.k - 1) [some sweepBoundary] [some sweepBoundary]
  simp only [List.length_reverse, hwlen, hfold, List.map_reverse, List.reverse_reverse] at hwrite
  have hlast : (sweepTM M).tm.step
      (sweepRevCfg (some (.write q c.inputSymbol c.workTapeSymbols (fun i => headAt c i (a - 1))))
        p' (z + M.k - 1 - ((n + 2) * M.k : ℕ))
        (V.map put ++ [some sweepBoundary]) [some sweepBoundary] out') =
      sweepStart M (act.apply c) (a - 1) (n + 2)
        (z + M.k - 1 - ((n + 2) * M.k : ℕ)) := by
    have hsym : (sweepRevCfg
        (some (SweepState.write q c.inputSymbol c.workTapeSymbols (fun i => headAt c i (a - 1))))
        p' (z + M.k - 1 - ((n + 2) * M.k : ℕ))
        (V.map put ++ [some sweepBoundary]) [some sweepBoundary] out').workTapeSymbols =
        fun _ => some sweepBoundary := by
      funext i
      exact sweepTape_read _ _ _
    change ((sweepTM M).tm.tr (.write q c.inputSymbol c.workTapeSymbols _) _ _).apply _ = _
    rw [hsym]
    exact sweepRevCfg_stay _ _ _ _ _ _ _
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step', sweep_grow_right_block, hdrop]
  change (sweepTM M).tm.step ((sweepTM M).tm.runFrom
    ((sweepTM M).tm.step (sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
      ((rightRow s).map put |>.reverse |>.append ((R.map put).reverse ++ [some sweepBoundary]))
      [] out)) ((n + 2) * M.k)) = _
  rw [hbuf, hturn, hwrite]
  exact hlast

/-- One source transition is one bounded burst, preserving the complete zone
shape and growing it by one block at each end. -/
private lemma sweep_step {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (hs : c.state = some q) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, a ≤ c.workTapePos i ∧ c.workTapePos i < a + n)
    (hl : ∀ i, c.workTapes i (a - 1) = none)
    (hr : ∀ i, c.workTapes i (a + n) = none) :
    (sweepTM M).tm.runFrom (sweepStart M c a n z) ((2 * n + 5) * M.k + 4) =
      sweepStart M (M.tm.step c) (a - 1) (n + 2) (z - M.k) := by
  rw [show (2 * n + 5) * M.k + 4 =
    (M.k + 1 + (n + 1) * M.k + 1) + (M.k + 1 + (n + 2) * M.k + 1) by ring,
    MultiTapeTM.runFrom_add, sweep_prepare M hk c q hs a n z (fun i => (hp i).1) hl,
    sweep_finish M hk c q a n _ (fun i => (hp i).2) hr]
  have hz : z - M.k + 1 + ((n + 1) * M.k : ℕ) + M.k - 1 - ((n + 2) * M.k : ℕ) =
      z - M.k := by push_cast; ring
  rw [hz]
  simp only [MultiTapeTM.step, hs]

/-- Exact transition count after a given number of source steps. -/
private def sweepTime (k : ℕ) : ℕ → ℕ
  | 0 => 2 * k + 2
  | t + 1 => sweepTime k t + ((4 * t + 7) * k + 4)

/-- Summing the exact per-step costs gives a quadratic polynomial. -/
private lemma sweepTime_eq (k t : ℕ) :
    sweepTime k t = 2 * k * t ^ 2 + (5 * k + 4) * t + (2 * k + 2) := by
  induction t with
  | zero => simp [sweepTime]
  | succ t ih => rw [sweepTime, ih]; ring

/-- A single constant bounds initialization and all sweeps, at every input size. -/
private lemma sweepTime_le (k t : ℕ) : sweepTime k t ≤ (9 * k + 6) * (t + 1) ^ 2 := by
  have hpow : 1 ≤ (t + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  have ht : t ≤ (t + 1) ^ 2 :=
    (Nat.le_succ _).trans (by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have ht2 : t ^ 2 ≤ (t + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) _
  rw [sweepTime_eq]
  calc
    2 * k * t ^ 2 + (5 * k + 4) * t + (2 * k + 2)
        ≤ 2 * k * (t + 1) ^ 2 + (5 * k + 4) * (t + 1) ^ 2 +
          (2 * k + 2) * (t + 1) ^ 2 := by
            exact Nat.add_le_add
              (Nat.add_le_add (Nat.mul_le_mul_left _ ht2) (Nat.mul_le_mul_left _ ht))
              (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * k + 2) hpow)
    _ = (9 * k + 6) * (t + 1) ^ 2 := by ring

/-- Up to the source's first halt, initialized runs agree at every macro boundary.
**Proof sketch.** Initialization gives time zero. At each live source state,
the elapsed-time support bound justifies fresh blank guards; the macro-step
lemma advances both the source configuration and the zone radius by one. -/
private lemma sweep_run_to_halt {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) (x : List Γ) (τ : ℕ)
    (hlive : ∀ t < τ, (M.tm.runFrom (M.tm.initCfg x) t).state ≠ none) :
    ∀ t ≤ τ,
      (sweepTM M).tm.runFrom ((sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k))) (sweepTime M.k t) =
        sweepStart M (M.tm.runFrom (M.tm.initCfg x) t) (-(t : ℤ)) (2 * t + 1)
          (-(t : ℤ) * M.k - 1) := by
  intro t
  induction t with
  | zero => intro _; simpa [sweepTime] using sweep_init M x
  | succ t ih =>
    intro ht
    obtain ⟨q, hs⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
    obtain ⟨hp, hc⟩ := source_bounds M x t
    have hpos : ∀ i, -(t : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
        (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i < -(t : ℤ) + (2 * t + 1 : ℕ) := by
      intro i
      have := hp i
      constructor <;> omega
    have hleft : ∀ i, (M.tm.runFrom (M.tm.initCfg x) t).workTapes i (-(t : ℤ) - 1) = none := by
      intro i
      exact hc i _ (by left; omega)
    have hright : ∀ i, (M.tm.runFrom (M.tm.initCfg x) t).workTapes i
        (-(t : ℤ) + (2 * t + 1 : ℕ)) = none := by
      intro i
      exact hc i _ (by right; omega)
    rw [sweepTime, MultiTapeTM.runFrom_add, ih (by omega)]
    rw [show (4 * t + 7) * M.k + 4 = (2 * (2 * t + 1) + 5) * M.k + 4 by ring]
    rw [sweep_step M hk _ q hs _ _ _ hpos hleft hright,
      ← MultiTapeTM.runFrom_succ_eq_step']
    have ha : -(t : ℤ) - 1 = -(t + 1 : ℕ) := by omega
    have hn : 2 * t + 1 + 2 = 2 * (t + 1) + 1 := by omega
    have hz : -(t : ℤ) * M.k - 1 - M.k = -(t + 1 : ℕ) * M.k - 1 := by push_cast; ring
    rw [ha, hn, hz]

/-- **One work tape suffices** [AB09, Claim 1.6]: a `Γ`-machine computing `f` within
`T` is simulated by a machine with a single work tape, over an enlarged finite
alphabet, within `c · (T n + 1)²`.

**Proof sketch.** For `k = 0`, simulate `M` directly with one unused work tape.
For `k ≥ 1`, the single work tape of `M'` stores the `k` tapes of `M` interleaved:
cell `j·k + i` of the simulated layout holds cell `j` of tape `i` (centered at `0` in
both directions). The alphabet is enlarged to cells carrying a *tagged payload*
`Option Γ` — so a marked blank is representable, which a bare `Γ × flag` product
would miss — together with a "head here" flag and zone-boundary tags; `Γ` embeds via
`e` as an unmarked non-blank payload. To simulate one step of `M`, `M'` sweeps its work tape once
left-to-right across the visited zone recording the `k` marked symbols in its state,
computes `M`'s transition, and sweeps back right-to-left updating the marked cells and
moving the marks. After `t` steps of `M` the visited zone spans `O(k · (t + 1))`
cells, so each simulated step costs `O(k · (T n + 1))` and the total is
`c · (T n + 1)²`. Input reads and output emissions pass through unchanged.

**Implementation note.** The forward pass records the preceding block's head
flags in the cells; the return pass carries the following block's flags in its
finite control. This implements both movement directions using exactly the two
stated sweeps. Each macro-step extends the zone by one blank block at each end.
For positive `k`, initialization costs `2k + 2` transitions and source step `t`
costs `(4t + 7)k + 4`; `sweepTime_le` supplies the constant `9k + 6`.
The zero-tape branch is a separate lockstep embedding with constant `1`. -/
theorem one_work_tape {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) ^ 2 := by
  by_cases hk : M.k = 0
  · refine ⟨Γ, inferInstance, inferInstance, Function.Embedding.refl Γ,
      unusedTapeTM M hk, 1, rfl, ?_⟩
    intro x
    simpa only [Function.Embedding.coe_refl, List.map_id, one_mul] using
      ((unusedTape_computes M hk f T hM) x).mono
        (show T x.length ≤ (T x.length + 1) ^ 2 from
          (Nat.le_succ _).trans (by
            rw [pow_two]
            exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  · refine ⟨SweepAlphabet Γ M.k, inferInstance, inferInstance, sweepEmbed Γ M.k,
      sweepTM M, 9 * M.k + 6, rfl, ?_⟩
    intro x
    obtain ⟨hhalt, hout⟩ := (computesInTime_iff M x (f x) (T x.length)).mp (hM x)
    have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T x.length, hhalt⟩
    let τ := Nat.find hex
    have hτ : (M.tm.runFrom (M.tm.initCfg x) τ).state = none := Nat.find_spec hex
    have ht : τ ≤ T x.length := Nat.find_min' hex hhalt
    have hlive : ∀ t < τ, (M.tm.runFrom (M.tm.initCfg x) t).state ≠ none :=
      fun _ h => Nat.find_min hex h
    have hrun := sweep_run_to_halt M (Nat.pos_of_ne_zero hk) x τ hlive τ (le_refl _)
    have houtτ : (M.tm.runFrom (M.tm.initCfg x) τ).output = f x := by
      have h := M.tm.runFrom_output_eq_of_halt (M.tm.initCfg x) ht hτ
      exact h.symm.trans hout
    have hc : (sweepTM M).ComputesInTime (x.map (sweepEmbed Γ M.k))
        ((f x).map (sweepEmbed Γ M.k)) (sweepTime M.k τ) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [hrun]
      constructor
      · change (M.tm.runFrom (M.tm.initCfg x) τ).state.map (fun q => SweepState.growLeft q 0) = none
        rw [hτ]
        rfl
      · change (M.tm.runFrom (M.tm.initCfg x) τ).output.map (sweepEmbed Γ M.k) = _
        rw [houtτ]
    exact hc.mono ((sweepTime_le M.k τ).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right ht 1) 2)))

/-- One work tape and the binary alphabet suffice simultaneously: the composition of
[AB09, Claim 1.6] with [AB09, Claim 1.5], possible because alphabet reduction
preserves the number of work tapes.

**Proof sketch.** Apply `Turing.FinTM.one_work_tape` to `M` with `Γ = Bool`,
obtaining a one-work-tape machine over some `Γ'` that computes `f` via an embedding
`Bool ↪ Γ'` within `c₁ · (T n + 1)²` — exactly the hypothesis of
`Turing.FinTM.alphabet_reduction`, which keeps `k = 1` and returns to the binary
alphabet within `c₂ · (c₁ · (T n + 1)² + 1) ≤ c · (T n + 1)²`. -/
theorem one_work_tape_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTime f fun n => c * (T n + 1) ^ 2 := by
  obtain ⟨Γ', instF, instD, e, M₁, c₁, hk₁, h₁⟩ := one_work_tape M f T hM
  haveI := instF
  haveI := instD
  obtain ⟨c₂, M₂, hk₂, h₂⟩ :=
    alphabet_reduction e M₁ f (fun n => c₁ * (T n + 1) ^ 2) h₁
  refine ⟨M₂, c₂ * (c₁ + 1), by rw [hk₂, hk₁], fun x => (h₂ x).mono ?_⟩
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc c₂ * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ c₂ * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl c₂) (Nat.add_le_add_left hpow _)
    _ = c₂ * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

end Turing.FinTM

/-! ### Space annotation (§13 Z4; additive, shared-file mechanism, flagged
for the A-S2 audit) -/

namespace Turing.FinTM

/-- Every horizon of the zero-tape embedding visits exactly its stationary origin.
**Proof sketch.** The existing lockstep configuration map always puts the unused
head at zero; its complete visited image is therefore the singleton `{0}`. -/
private lemma dg_unused_space {Γ : Type} (M : FinTM Γ) (hk : M.k = 0)
    (x : List Γ) (t : ℕ) :
    (unusedTapeTM M hk).tm.spaceUsed ((unusedTapeTM M hk).tm.initCfg x) t = 1 := by
  have hr (u : ℕ) := MultiTapeTM.runFrom_comm_of_step (unusedTapeCfg M)
    (unusedTape_step M hk) (M.tm.initCfg x) u
  have hp (u : ℕ) :
      ((unusedTapeTM M hk).tm.runFrom ((unusedTapeTM M hk).tm.initCfg x) u).workTapePos =
        fun _ => 0 := by
    change ((unusedTapeTM M hk).tm.runFrom (unusedTapeCfg M (M.tm.initCfg x)) u).workTapePos = _
    rw [hr]
    rfl
  simp only [MultiTapeTM.spaceUsed, MultiTapeTM.spaceUsedByTape,
    MultiTapeTM.visitedByTapeHead, hp]
  rw [Finset.image_const (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero t))]
  simp [unusedTapeTM]

/-- Internal input symbols are read as one fixed source symbol. This retraction
is used in finite control; no work tape holds a copy of the retracted word. -/
private def dgRetract {Γ : Type} {k : ℕ} (a₀ : Γ) : SweepAlphabet Γ k → Γ :=
  Sum.elim id (fun _ => a₀)

/-- Retraction fixes every genuine input symbol. -/
private lemma dgRetract_embed {Γ : Type} {k : ℕ} (a₀ a : Γ) :
    dgRetract (k := k) a₀ (sweepEmbed Γ k a) = a := rfl

/-- A source position on the same-length retracted input is a native position. -/
private def dgPos {Γ : Type} {k : ℕ} (a₀ : Γ) {x : List (SweepAlphabet Γ k)}
    (p : Fin ((x.map (dgRetract a₀)).length + 2)) : Fin (x.length + 2) :=
  ⟨p.val, by simpa only [List.length_map] using p.isLt⟩

/-- Native head movement commutes with the same-length retraction. -/
private lemma dgPos_move {Γ : Type} {k : ℕ} (a₀ : Γ) {x : List (SweepAlphabet Γ k)}
    (p : Fin ((x.map (dgRetract a₀)).length + 2)) (d : SignType) :
    moveInputPos (dgPos a₀ p) d = dgPos a₀ (moveInputPos p d) := by
  apply Fin.ext
  simp only [moveInputPos, dgPos, List.length_map]
  split <;> rfl

/-- Retraction is performed on the symbol currently read, including both
native input boundaries. -/
private lemma dgInput_read {Γ Q R : Type} {k : ℕ} (a₀ : Γ)
    {x : List (SweepAlphabet Γ k)} (c : Cfg k Γ Q (x.map (dgRetract a₀)))
    (d : Cfg 1 (SweepAlphabet Γ k) R x) (hp : d.inputPos = dgPos a₀ c.inputPos) :
    d.inputSymbol.map (dgRetract a₀) = c.inputSymbol := by
  have hz : dgPos a₀ c.inputPos = 0 ↔ c.inputPos = 0 := by
    simp only [Fin.ext_iff, dgPos, Fin.val_zero]
  have hv : (dgPos a₀ c.inputPos).val = c.inputPos.val := rfl
  simp only [Cfg.inputSymbol, hp, hz, hv, List.length_map]
  split
  · rfl
  · split
    · rfl
    · simp only [Option.map_some, List.getElem_map]

/-- The new states are only the left-boundary writer. Every other phase uses
the received controller state type. -/
private abbrev DGState (Γ Q : Type) (k : ℕ) :=
  SweepState Γ Q k ⊕ (Option Q × (Fin k → Bool) × Fin (k + 1))

/-- A boundary is crossed exactly when one of its old heads moves outward. -/
private def dgCross {Γ Q : Type} {k : ℕ} (a : Action k Γ Q)
    (h : Fin k → Bool) (d : SignType) : Bool :=
  decide (∃ i, h i = true ∧ (a.workTapes i).2 = d)

/-- Boundary control for the demand-grown simulator [AB09, Claim 1.6].
The shared sweep layer has no conditional extension controller. This wrapper
delegates initialization, read/write cell transitions, and right-row generation
to `sweepTM`; it changes only the boundary transitions and adds the missing
left-row writer. The old witness is never used as a space witness.

The read pass retains its last row's head flags, and the reverse pass brings
its first row's old flags to the left boundary. Thus each boundary test uses
exactly the boundary-head flags recorded by the shared transduction, together
with the pending source movement. Retraction affects native input reads only. -/
private def dgTM {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) : FinTM (SweepAlphabet Γ M.k) where
  k := 1
  State := DGState Γ M.State M.k
  tm :=
    { q₀ := .inl (.init 0)
      tr := fun q inp work =>
        let native := inp.map (fun b => Sum.inl (dgRetract a₀ b))
        let old := fun q => ((sweepTM M).tm.tr q native work).mapState Sum.inl
        match q with
        | .inl (.growLeft q _) =>
          sweepAct (.inl (.read q (fun _ => (none, false)))) (some sweepBoundary) .pos
        | .inl (.read q s) =>
          match work 0 with
          | some (.inr (some _)) => old (.read q s)
          | _ =>
            let a := M.tm.tr q (inp.map (dgRetract a₀)) (fun i => (s i).1)
            if dgCross a (fun i => (s i).2) .pos then
              sweepMove (some (.inl (.growRight q s 0))) .zero
            else old (.growRight q s ⟨M.k, by omega⟩)
        | .inl (.write q inp reads right) =>
          match work 0 with
          | some (.inr (some _)) => old (.write q inp reads right)
          | _ =>
            let a := M.tm.tr q inp reads
            if dgCross a right .neg then
              sweepMove (some (.inr (a.state,
                fun i => right i && decide ((a.workTapes i).2 = .neg), 0))) .zero
            else sweepMove (a.state.map (fun q => .inl (.growLeft q 0))) .zero
        | .inl q => old q
        | .inr (q, heads, i) =>
          if h : i.val < M.k then
            let j : Fin M.k := ⟨M.k - 1 - i.val, by omega⟩
            sweepAct (.inr (q, heads, ⟨i.val + 1, by omega⟩))
              (some (sweepSymbol (j, none, heads j, false))) .neg
          else
            ⟨0, fun _ => (some (some sweepBoundary), .zero), none,
              q.map (fun q => .inl (.growLeft q 0))⟩ }

/-- A complete read phase cites the unchanged source-zone transduction. -/
private lemma dg_read {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) {y : List Γ} (c : Cfg M.k Γ M.State y)
    (q : M.State) (a z : ℤ) (n : ℕ) {x : List (SweepAlphabet Γ M.k)}
    (p : Fin (x.length + 2)) (out : List (SweepAlphabet Γ M.k))
    (l r : List (Option (SweepAlphabet Γ M.k))) :
    (dgTM M a₀).tm.runFrom
      (sweepCfg (some (.inl (.read q (readState c a)))) p z l
        ((tapeZone (fun j => tapeRow c j false) a n).map
          (fun b => some (sweepSymbol b)) ++ r) out) (n * M.k) =
      sweepCfg (some (.inl (.read q (readState c (a + n))))) p (z + n * M.k)
        (((tapeZone (fun j => tapeRow c j true) a n).map
          (fun b => some (sweepSymbol b))).reverse ++ l) r out := by
  have h := sweep_run (dgTM M a₀).tm (fun s => Sum.inl (SweepState.read q s))
    sweepSymbol readVisit (by intro s b inp; rfl) p out
    (tapeZone (fun j => tapeRow c j false) a n) (readState c a) z l r
  simpa only [read_zone, tapeZone_length, Int.natCast_mul] using h

/-- A complete return phase cites the unchanged source-zone transduction. -/
private lemma dg_write {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) {y : List Γ} (c : Cfg M.k Γ M.State y)
    (q : M.State) (inp : Option Γ) (reads : Fin M.k → Option Γ)
    (a z : ℤ) (n : ℕ) {x : List (SweepAlphabet Γ M.k)}
    (p : Fin (x.length + 2)) (out : List (SweepAlphabet Γ M.k))
    (l r : List (Option (SweepAlphabet Γ M.k))) :
    (dgTM M a₀).tm.runFrom
      (sweepRevCfg (some (.inl (.write q inp reads (fun i => headAt c i (a + n)))))
        p z l ((tapeZone (fun j => tapeRow c j true) a n).reverse.map
          (fun b => some (sweepSymbol b)) ++ r) out) (n * M.k) =
      sweepRevCfg (some (.inl (.write q inp reads (fun i => headAt c i a))))
        p (z - n * M.k)
        ((tapeZone (fun j => tapeRow ((M.tm.tr q inp reads).apply c) j false) a n).map
          (fun b => some (sweepSymbol b)) ++ l) r out := by
  have h := sweep_run_reverse (dgTM M a₀).tm
    (fun s => Sum.inl (SweepState.write q inp reads s)) sweepSymbol
    (writeVisit (M.tm.tr q inp reads)) (by intro s b inp'; rfl) p out
    (tapeZone (fun j => tapeRow c j true) a n).reverse
    (fun i => headAt c i (a + n)) z l r
  simpa only [write_zone, List.length_reverse, tapeZone_length,
    List.map_reverse, List.reverse_reverse, Int.natCast_mul] using h

/-- The generic forward sweep's head position at every prefix, obtained by
applying `sweep_run` to a prefix and leaving the suffix in the zipper. -/
private lemma dg_sweep_prefix {A Q R C : Type} (tm : MultiTapeTM 1 A Q)
    (state : R → Q) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .pos)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A))
    (u : ℕ) (hu : u ≤ as.length) :
    (tm.runFrom (sweepCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) u).workTapePos 0 = z + u := by
  have h := sweep_run tm state symbol visit htr p out (as.take u) s z l
    ((as.drop u).map (fun a => some (symbol a)) ++ r)
  rw [← List.append_assoc, ← List.map_append, List.take_append_drop] at h
  simpa only [List.length_take, Nat.min_eq_left hu, sweepCfg] using
    congrArg (fun c => c.workTapePos 0) h

/-- The return sweep's entire trajectory follows from its generic API on
prefixes, rather than from an estimate of its final position. -/
private lemma dg_sweep_reverse_prefix {A Q R C : Type} (tm : MultiTapeTM 1 A Q)
    (state : R → Q) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s a inp, tm.tr (state s) inp (fun _ => some (symbol a)) =
      sweepAct (state (visit s a).1) (some (symbol (visit s a).2)) .neg)
    {x : List A} (p : Fin (x.length + 2)) (out : List A)
    (as : List C) (s : R) (z : ℤ) (l r : List (Option A))
    (u : ℕ) (hu : u ≤ as.length) :
    (tm.runFrom (sweepRevCfg (some (state s)) p z l
      (as.map (fun a => some (symbol a)) ++ r) out) u).workTapePos 0 = z - u := by
  have h := sweep_run_reverse tm state symbol visit htr p out (as.take u) s z l
    ((as.drop u).map (fun a => some (symbol a)) ++ r)
  rw [← List.append_assoc, ← List.map_append, List.take_append_drop] at h
  simpa only [List.length_take, Nat.min_eq_left hu, sweepRevCfg] using
    congrArg (fun c => c.workTapePos 0) h

/-- A finite run together with containment at all its prefixes. The endpoints
are physical coordinates, and both are counted. -/
private def DGSpan {A Q : Type} {x : List A} (tm : MultiTapeTM 1 A Q)
    (c d : Cfg 1 A Q x) (t : ℕ) (lo hi : ℤ) : Prop :=
  tm.runFrom c t = d ∧ ∀ u ≤ t,
    lo ≤ (tm.runFrom c u).workTapePos 0 ∧ (tm.runFrom c u).workTapePos 0 ≤ hi

/-- Concatenating contained runs preserves containment at every physical time.
**Proof sketch.** A prefix ends either in the first run or at a uniquely
specified offset in the second; the equality at the join handles the latter. -/
private lemma dgSpan_add {A Q : Type} {x : List A} {tm : MultiTapeTM 1 A Q}
    {c d e : Cfg 1 A Q x} {s t : ℕ} {lo hi : ℤ}
    (h₁ : DGSpan tm c d s lo hi) (h₂ : DGSpan tm d e t lo hi) :
    DGSpan tm c e (s + t) lo hi := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h₁.1, h₂.1], ?_⟩
  intro u hu
  by_cases h : u ≤ s
  · exact h₁.2 u h
  · have he : u = s + (u - s) := by omega
    rw [he, MultiTapeTM.runFrom_add, h₁.1]
    exact h₂.2 (u - s) (by omega)

/-- A single transition has only its two endpoints as prefixes. -/
private lemma dgSpan_one {A Q : Type} {x : List A} {tm : MultiTapeTM 1 A Q}
    {c d : Cfg 1 A Q x} {lo hi : ℤ} (h : tm.step c = d)
    (hc : lo ≤ c.workTapePos 0 ∧ c.workTapePos 0 ≤ hi)
    (hd : lo ≤ d.workTapePos 0 ∧ d.workTapePos 0 ≤ hi) :
    DGSpan tm c d 1 lo hi := by
  have hr : tm.runFrom c 1 = d := by simpa using h
  refine ⟨hr, ?_⟩
  intro u hu
  have he : u = 0 ∨ u = 1 := by omega
  rcases he with rfl | rfl
  · simpa using hc
  · rw [hr]
    exact hd

/-- The canonical boundary configuration uses the received interleaved zone,
with the source read position interpreted on the native, unretracted input. -/
private def dgStart {Γ : Type} [Fintype Γ] [DecidableEq Γ] (M : FinTM Γ)
    (a₀ : Γ) {x : List (SweepAlphabet Γ M.k)}
    (c : Cfg M.k Γ M.State (x.map (dgRetract a₀))) (a : ℤ) (n : ℕ) (z : ℤ) :
    Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
  sweepRevCfg (c.state.map (fun q => .inl (.growLeft q 0))) (dgPos a₀ c.inputPos) z
    ((tapeZone (fun j => tapeRow c j false) a n).map (fun b => some (sweepSymbol b)) ++
      [some sweepBoundary]) [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k))

/-- Mapping a native read into the data summand makes the received decoder
implement the total retraction, including the absent boundary symbol. -/
private lemma dg_native {Γ : Type} {k : ℕ} (a₀ : Γ) (inp : Option (SweepAlphabet Γ k)) :
    sweepInput (k := k) (inp.map (fun b => Sum.inl (dgRetract a₀ b))) =
      inp.map (dgRetract a₀) := by
  cases inp <;> rfl

/-- A fixed forward writer has an exact endpoint and visits only the segment
between its initial and final heads. This adds prefix containment to the
existing `sweep_generate` API, without another generation induction. -/
private lemma dgSpan_generate_right {A Q : Type} {x : List A}
    (tm : MultiTapeTM 1 A Q) (w : List A) (state : Fin (w.length + 1) → Q)
    (htr : ∀ (i : ℕ) (hi : i < w.length) inp work,
      tm.tr (state ⟨i, by omega⟩) inp work =
        sweepAct (state ⟨i + 1, by omega⟩) (some w[i]) .pos)
    (p : Fin (x.length + 2)) (out : List A) (z : ℤ)
    (l r : List (Option A)) (n : ℕ) (hn : n ≤ w.length) :
    DGSpan tm (sweepCfg (some (state 0)) p z l r out)
      (sweepCfg (some (state ⟨n, by omega⟩)) p (z + n)
        ((w.take n).map some |>.reverse |>.append l) (r.drop n) out) n z (z + n) := by
  let cfg := fun i z l r => sweepCfg (some (state i)) p z l r out
  have hr (u : ℕ) (hu : u ≤ w.length) := sweep_generate tm w cfg 1
    (fun i hi z l r => by
      change (tm.tr (state ⟨i, by omega⟩) _ _).apply _ = _
      rw [htr i hi]
      exact sweepCfg_right_any _ _ p z l r out _) z l r u hu
  refine ⟨by simpa only [cfg, one_mul] using hr n hn, ?_⟩
  intro u hu
  have hp := congrArg (fun c => c.workTapePos 0) (hr u (hu.trans hn))
  change (tm.runFrom (sweepCfg (some (state 0)) p z l r out) u).workTapePos 0 = z + 1 * u at hp
  rw [hp]
  constructor <;> omega

/-- The same prefix containment wrapper for a fixed leftward writer. -/
private lemma dgSpan_generate_left {A Q : Type} {x : List A}
    (tm : MultiTapeTM 1 A Q) (w : List A) (state : Fin (w.length + 1) → Q)
    (htr : ∀ (i : ℕ) (hi : i < w.length) inp work,
      tm.tr (state ⟨i, by omega⟩) inp work =
        sweepAct (state ⟨i + 1, by omega⟩) (some w[i]) .neg)
    (p : Fin (x.length + 2)) (out : List A) (z : ℤ)
    (l r : List (Option A)) (n : ℕ) (hn : n ≤ w.length) :
    DGSpan tm (sweepRevCfg (some (state 0)) p z l r out)
      (sweepRevCfg (some (state ⟨n, by omega⟩)) p (z - n)
        ((w.take n).map some |>.reverse |>.append l) (r.drop n) out) n (z - n) z := by
  let cfg := fun i z l r => sweepRevCfg (some (state i)) p z l r out
  have hr (u : ℕ) (hu : u ≤ w.length) := sweep_generate tm w cfg (-1)
    (fun i hi z l r => by
      change (tm.tr (state ⟨i, by omega⟩) _ _).apply _ = _
      rw [htr i hi]
      simpa only [sub_eq_add_neg] using sweepRevCfg_left_any _ _ p z l r out _)
    z l r u hu
  refine ⟨by simpa only [cfg, neg_one_mul, sub_eq_add_neg] using hr n hn, ?_⟩
  intro u hu
  have hp := congrArg (fun c => c.workTapePos 0) (hr u (hu.trans hn))
  change (tm.runFrom (sweepRevCfg (some (state 0)) p z l r out) u).workTapePos 0 = z + -1 * u at hp
  rw [hp]
  constructor <;> omega

/-- A containing interval can be enlarged without changing a certified run. -/
private lemma dgSpan_mono {A Q : Type} {x : List A} {tm : MultiTapeTM 1 A Q}
    {c d : Cfg 1 A Q x} {t : ℕ} {lo hi lo' hi' : ℤ}
    (h : DGSpan tm c d t lo hi) (hl : lo' ≤ lo) (hr : hi ≤ hi') :
    DGSpan tm c d t lo' hi' :=
  ⟨h.1, fun u hu => ⟨hl.trans (h.2 u hu).1, (h.2 u hu).2.trans hr⟩⟩

/-- Initialization on every native input stays in the origin block and its
two boundary cells. It uses the generic writer and reverse-sweep APIs.
**Proof sketch.** Generate the marked origin row, turn at its right boundary,
scan that fixed row backward, and install its left boundary. Each of these
four runs carries all-prefix containment before they are concatenated. -/
private lemma dg_init {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) (x : List (SweepAlphabet Γ M.k)) :
    DGSpan (dgTM M a₀).tm ((dgTM M a₀).tm.initCfg x)
      (dgStart M a₀ (M.tm.initCfg (x.map (dgRetract a₀))) 0 1 (-1))
      (2 * M.k + 2) (-1) M.k := by
  let B := blankRow (Γ := Γ) M.k true
  let w := B.map sweepSymbol
  let L := w.map some
  have hw : w.length = M.k := by simp [w, B, blankRow]
  have hb : B.length = M.k := by simp [B, blankRow]
  let st : Fin (w.length + 1) → DGState Γ M.State M.k :=
    fun i => .inl (.init ⟨i.val, by simpa only [hw] using i.isLt⟩)
  have gen := dgSpan_generate_right (dgTM M a₀).tm w st
    (fun i hi inp work => by
      have hik : i < M.k := by omega
      have he : w[i] = sweepSymbol (⟨i, hik⟩, none, true, false) := by
        simp [w, B, blankRow]
      simp only [st, dgTM, sweepTM, dif_pos hik, Action.mapState, sweepAct, Option.map_some]
      rw [he]) (1 : Fin (x.length + 2)) [] 0 [] [] M.k (by omega)
  have htake : w.take M.k = w := List.take_of_length_le (le_of_eq hw)
  have hgen : DGSpan (dgTM M a₀).tm ((dgTM M a₀).tm.initCfg x)
      (sweepCfg (some (.inl (.init ⟨M.k, by omega⟩))) 1 M.k L.reverse [] [])
      M.k (-1) M.k := by
    have hinit : (dgTM M a₀).tm.initCfg x =
        sweepCfg (some (st 0)) 1 0 [] [] [] := by
      apply Cfg.ext <;> try rfl
      funext i z
      simp [sweepCfg, sweepTape]
    rw [hinit]
    simpa [htake, st, L] using dgSpan_mono (lo' := -1) (hi' := M.k) gen (by omega) (by omega)
  let c₁ : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepCfg (some (.inl (.init ⟨M.k, by omega⟩))) 1 M.k L.reverse [] []
  let c₂ : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepRevCfg (some (.inl .back)) 1 ((M.k : ℤ) - 1) [some sweepBoundary] L.reverse []
  have turn : (dgTM M a₀).tm.step c₁ = c₂ := by
    change ((dgTM M a₀).tm.tr (.inl (.init ⟨M.k, by omega⟩)) _ _).apply _ = _
    simp only [dgTM, sweepTM, lt_self_iff_false, ↓reduceDIte, Action.mapState,
      sweepAct, Option.map_some]
    simpa only [c₁, c₂, SignType.zero_eq_zero, moveInputPos_zero, List.tail_nil, Option.toList_none,
      List.append_nil] using
      sweep_turn_left (some (Sum.inl (SweepState.init ⟨M.k, by omega⟩)))
        (some (Sum.inl (SweepState.back (Γ := Γ) (S := M.State) (k := M.k))))
        (1 : Fin (x.length + 2)) (M.k : ℤ) L.reverse [] [] (some sweepBoundary) none .zero
  have hturn : DGSpan (dgTM M a₀).tm c₁ c₂ 1 (-1) M.k :=
    dgSpan_one turn (by dsimp [c₁, sweepCfg]; omega) (by dsimp [c₂, sweepRevCfg]; omega)
  let c₃ : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepRevCfg (some (.inl .back)) 1 (-1) (L ++ [some sweepBoundary]) [] []
  have hback : DGSpan (dgTM M a₀).tm c₂ c₃ M.k (-1) M.k := by
    constructor
    · have h := sweep_run_reverse (dgTM M a₀).tm
        (fun _ : Unit => Sum.inl SweepState.back) sweepSymbol (fun s b => (s, b))
        (by intro s b inp; rfl) (1 : Fin (x.length + 2)) [] B.reverse ()
        ((M.k : ℤ) - 1) [some sweepBoundary] []
      simpa [c₂, c₃, L, w, List.map_map, List.map_reverse, sweepFold_id, hb] using h
    · intro u hu
      have h := dg_sweep_reverse_prefix (dgTM M a₀).tm
        (fun _ : Unit => Sum.inl SweepState.back) sweepSymbol (fun s b => (s, b))
        (by intro s b inp; rfl) (1 : Fin (x.length + 2)) [] B.reverse ()
        ((M.k : ℤ) - 1) [some sweepBoundary] [] u (by simpa [hb] using hu)
      have hp : ((dgTM M a₀).tm.runFrom c₂ u).workTapePos (0 : Fin 1) = (M.k : ℤ) - 1 - u := by
        simpa [c₂, L, w, List.map_map, List.map_reverse] using h
      rw [hp]
      constructor <;> omega
  have last : (dgTM M a₀).tm.step c₃ =
      dgStart M a₀ (M.tm.initCfg (x.map (dgRetract a₀))) 0 1 (-1) := by
    have hw₃ : c₃.workTapeSymbols = fun _ => none := by
      funext i
      simp [c₃, Cfg.workTapeSymbols, sweepRevCfg, sweepTape]
    change ((dgTM M a₀).tm.tr (.inl .back) _ _).apply _ = _
    rw [hw₃]
    change (sweepAct (Sum.inl (SweepState.growLeft M.tm.q₀ 0))
      (some sweepBoundary) .zero).apply c₃ = _
    rw [show c₃ = sweepRevCfg (some (.inl .back)) 1 (-1)
      (L ++ [some sweepBoundary]) [] [] from rfl, sweepRevCfg_write]
    congr 1
    simp [tapeZone, tapeRow, headAt, L, w, B, blankRow, List.map_map]
  have hlast := dgSpan_one last (by dsimp [c₃, sweepRevCfg]; omega)
    (show (-1 : ℤ) ≤ (dgStart M a₀ (M.tm.initCfg (x.map (dgRetract a₀))) 0 1 (-1)).workTapePos 0 ∧
      (dgStart M a₀ (M.tm.initCfg (x.map (dgRetract a₀))) 0 1 (-1)).workTapePos 0 ≤ M.k by
        dsimp [dgStart, sweepRevCfg]; omega)
  have h := dgSpan_add (dgSpan_add (dgSpan_add hgen hturn) hback) hlast
  simpa only [show M.k + 1 + M.k + 1 = 2 * M.k + 2 by omega] using h

/-- The delegated right-row writer has the exact generic prefix ledger. -/
private lemma dg_right_span {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) (q : M.State) (s : Fin M.k → Option Γ × Bool)
    {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ)
    (l r : List (Option (SweepAlphabet Γ M.k))) :
    DGSpan (dgTM M a₀).tm
      (sweepCfg (some (.inl (.growRight q s 0))) p z l r out)
      (sweepCfg (some (.inl (.growRight q s ⟨M.k, by omega⟩))) p (z + M.k)
        (((rightRow s).map (fun b => some (sweepSymbol b))).reverse ++ l)
        (r.drop M.k) out) M.k z (z + M.k) := by
  let w := (rightRow s).map sweepSymbol
  have hw : w.length = M.k := by simp [w, rightRow]
  have h := dgSpan_generate_right (dgTM M a₀).tm w
    (fun i => Sum.inl (SweepState.growRight q s ⟨i.val, by simpa [hw] using i.isLt⟩))
    (fun i hi inp work => by
      have hik : i < M.k := by omega
      have he : w[i] = sweepSymbol (⟨i, hik⟩, none, false, (s ⟨i, hik⟩).2) := by
        simp [w, rightRow]
      simp only [dgTM, sweepTM, dif_pos hik, Action.mapState, sweepAct, Option.map_some]
      rw [he]) p out z l r M.k (by omega)
  have htake : w.take M.k = w := List.take_of_length_le (le_of_eq hw)
  simpa only [htake, w, List.map_map, Function.comp_def] using h

/-- A newly crossed left coordinate is a received blank row with exactly the
incoming heads marked. -/
private def dgLeftRow {Γ : Type} {k : ℕ} (heads : Fin k → Bool) : List (SweepCell Γ k) :=
  (blankRow k false).map fun b => (b.1, b.2.1, heads b.1, false)

/-- The new left-row writer stays within exactly the newly allocated block.
**Proof sketch.** Instantiate the generic leftward writer with the reversed
marked blank row. Its all-prefix ledger accounts for the new boundary too. -/
private lemma dg_left_span {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) (q : Option M.State) (heads : Fin M.k → Bool)
    {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ)
    (l r : List (Option (SweepAlphabet Γ M.k))) :
    DGSpan (dgTM M a₀).tm
      (sweepRevCfg (some (.inr (q, heads, 0))) p z l r out)
      (sweepRevCfg (some (.inr (q, heads, ⟨M.k, by omega⟩))) p (z - M.k)
        ((dgLeftRow heads).map (fun b => some (sweepSymbol b)) ++ l)
        (r.drop M.k) out) M.k (z - M.k) z := by
  let w := (dgLeftRow (Γ := Γ) heads).reverse.map sweepSymbol
  have hw : w.length = M.k := by simp [w, dgLeftRow, blankRow]
  have h := dgSpan_generate_left (dgTM M a₀).tm w
    (fun i => Sum.inr (q, heads, ⟨i.val, by simpa [hw] using i.isLt⟩))
    (fun i hi inp work => by
      have hik : i < M.k := by omega
      have he : w[i] = sweepSymbol
          (⟨M.k - 1 - i, by omega⟩, none, heads ⟨M.k - 1 - i, by omega⟩, false) := by
        simp [w, dgLeftRow, blankRow, List.getElem_reverse]
      simp only [dgTM, dif_pos hik]
      rw [he]) p out z l r M.k (by omega)
  have htake : w.take M.k = w := List.take_of_length_le (le_of_eq hw)
  rw [htake] at h
  simpa only [w, List.map_map, Function.comp_def,
    List.map_reverse, List.reverse_reverse] using h

/-- Entering the read phase does not allocate a left block. The complete
forward run and all its prefixes stay between the current boundary cells.
**Proof sketch.** Turn right without changing the zone, then apply the received
read transduction and the generic prefix-position theorem. -/
private lemma dg_collect {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) {x : List (SweepAlphabet Γ M.k)}
    (c : Cfg M.k Γ M.State (x.map (dgRetract a₀)))
    (q : M.State) (hs : c.state = some q) (a z : ℤ) (n : ℕ)
    (hp : ∀ i, a ≤ c.workTapePos i) :
    DGSpan (dgTM M a₀).tm (dgStart M a₀ c a n z)
      (sweepCfg (some (.inl (.read q (readState c (a + n)))))
        (dgPos a₀ c.inputPos) (z + 1 + n * M.k)
        (((tapeZone (fun j => tapeRow c j true) a n).map
          (fun b => some (sweepSymbol b))).reverse ++ [some sweepBoundary])
        [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)))
      (1 + n * M.k) z (z + 1 + n * M.k) := by
  let F := tapeZone (fun j => tapeRow c j false) a n
  let p := dgPos a₀ c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let d : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepCfg (some (.inl (.read q (readState c a)))) p (z + 1) [some sweepBoundary]
      (F.map (fun b => some (sweepSymbol b)) ++ [some sweepBoundary]) out
  have hr : readState c a = fun _ => (none, false) := by
    funext i
    have h := hp i
    simp [readState, headAt, show ¬c.workTapePos i < a by omega,
      show c.workTapePos i ≠ a - 1 by omega]
  have step : (dgTM M a₀).tm.step (dgStart M a₀ c a n z) = d := by
    simp only [dgStart, MultiTapeTM.step, sweepRevCfg, hs, Option.map_some]
    change (sweepAct (Sum.inl (SweepState.read q (fun _ => (none, false))))
      (some sweepBoundary) .pos).apply
        (sweepRevCfg (some (.inl (.growLeft q 0))) p z
          (F.map (fun b => some (sweepSymbol b)) ++ [some sweepBoundary])
          [some sweepBoundary] out) = d
    rw [sweep_turn_right]
    simp only [d, hr, List.tail_cons]
  have hnk : 0 ≤ (n : ℤ) * M.k := by exact_mod_cast (Nat.zero_le (n * M.k))
  have first : DGSpan (dgTM M a₀).tm (dgStart M a₀ c a n z) d 1 z (z + 1 + n * M.k) :=
    dgSpan_one step (by dsimp [dgStart, sweepRevCfg]; constructor <;> omega)
      (by dsimp [d, sweepCfg]; constructor <;> omega)
  have scan : DGSpan (dgTM M a₀).tm d
      (sweepCfg (some (.inl (.read q (readState c (a + n))))) p (z + 1 + n * M.k)
        (((tapeZone (fun j => tapeRow c j true) a n).map
          (fun b => some (sweepSymbol b))).reverse ++ [some sweepBoundary])
        [some sweepBoundary] out) (n * M.k) z (z + 1 + n * M.k) := by
    refine ⟨dg_read M a₀ c q a (z + 1) n p out _ _, ?_⟩
    intro u hu
    have h := dg_sweep_prefix (dgTM M a₀).tm
      (fun s => Sum.inl (SweepState.read q s)) sweepSymbol readVisit
      (by intro s b inp; rfl) p out F (readState c a) (z + 1)
      [some sweepBoundary] [some sweepBoundary] u (by simpa [F, tapeZone_length] using hu)
    change ((dgTM M a₀).tm.runFrom d u).workTapePos (0 : Fin 1) = z + 1 + u at h
    rw [h]
    have hu' : (u : ℤ) ≤ (n : ℤ) * M.k := by exact_mod_cast hu
    constructor <;> omega
  exact dgSpan_add first scan

/-- The delegated right-boundary turn performs precisely one native source
input/output action. Retraction is used for the scanned symbol only.
**Proof sketch.** Decode the current native read using `dgInput_read`, then
apply the received write-and-turn zipper identity and commute the symbol map
with the optional output append. -/
private lemma dg_turn {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) {x : List (SweepAlphabet Γ M.k)}
    (c : Cfg M.k Γ M.State (x.map (dgRetract a₀))) (q : M.State)
    (s : Fin M.k → Option Γ × Bool) (hs : (fun i => (s i).1) = c.workTapeSymbols)
    (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (dgTM M a₀).tm.step
      (sweepCfg (some (.inl (.growRight q s ⟨M.k, by omega⟩))) (dgPos a₀ c.inputPos) z
        l r (c.output.map (sweepEmbed Γ M.k))) =
      sweepRevCfg (some (.inl (.write q c.inputSymbol c.workTapeSymbols (fun _ => false))))
        (dgPos a₀ ((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c).inputPos) (z - 1)
        (some sweepBoundary :: r.tail) l
        (((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c).output.map (sweepEmbed Γ M.k)) := by
  let d : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepCfg (some (.inl (.growRight q s ⟨M.k, by omega⟩))) (dgPos a₀ c.inputPos) z
      l r (c.output.map (sweepEmbed Γ M.k))
  let act := M.tm.tr q c.inputSymbol c.workTapeSymbols
  have hi : sweepInput (k := M.k) (d.inputSymbol.map (fun b => Sum.inl (dgRetract a₀ b))) =
      c.inputSymbol := (dg_native a₀ d.inputSymbol).trans (dgInput_read a₀ c d rfl)
  change ((dgTM M a₀).tm.tr (.inl (.growRight q s ⟨M.k, by omega⟩))
    d.inputSymbol d.workTapeSymbols).apply d = _
  simp only [dgTM, sweepTM, lt_self_iff_false, ↓reduceDIte]
  rw [hi, hs]
  change (⟨act.inputTape, fun _ => (some (some sweepBoundary), .neg), act.output.map Sum.inl,
    some (.inl (.write q c.inputSymbol c.workTapeSymbols (fun _ => false)))⟩ :
    Action 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k)).apply
      (sweepCfg (some (.inl (.growRight q s ⟨M.k, by omega⟩))) (dgPos a₀ c.inputPos) z
        l r (c.output.map (sweepEmbed Γ M.k))) = _
  rw [sweep_turn_left, dgPos_move]
  have ho : c.output.map (sweepEmbed Γ M.k) ++ (act.output.map Sum.inl).toList =
      (act.apply c).output.map (sweepEmbed Γ M.k) := by
    cases he : act.output <;> simp [Action.apply, he, List.map_append, sweepEmbed]
  rw [ho]
  rfl

/-- The right-boundary test either enters the delegated generator or turns
immediately. The table equality is independent of any run invariant. -/
private lemma dg_read_boundary {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) (q : M.State) (s : Fin M.k → Option Γ × Bool)
    (inp : Option (SweepAlphabet Γ M.k)) :
    (dgTM M a₀).tm.tr (.inl (.read q s)) inp (fun _ => some sweepBoundary) =
      if dgCross (M.tm.tr q (inp.map (dgRetract a₀)) (fun i => (s i).1))
          (fun i => (s i).2) .pos then
        sweepMove (some (.inl (.growRight q s 0))) .zero
      else (dgTM M a₀).tm.tr (.inl (.growRight q s ⟨M.k, by omega⟩)) inp
        (fun _ => some sweepBoundary) := rfl

/-- A negative right-boundary crossing test turns in one step and allocates
no cell. All prefixes stay at the boundary or the cell immediately to its left. -/
private lemma dg_turn_without_growth {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) {x : List (SweepAlphabet Γ M.k)}
    (c : Cfg M.k Γ M.State (x.map (dgRetract a₀))) (q : M.State)
    (s : Fin M.k → Option Γ × Bool) (hs : (fun i => (s i).1) = c.workTapeSymbols)
    (hc : dgCross (M.tm.tr q c.inputSymbol c.workTapeSymbols) (fun i => (s i).2) .pos = false)
    (z : ℤ) (l : List (Option (SweepAlphabet Γ M.k))) :
    DGSpan (dgTM M a₀).tm
      (sweepCfg (some (.inl (.read q s))) (dgPos a₀ c.inputPos) z l
        [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)))
      (sweepRevCfg (some (.inl (.write q c.inputSymbol c.workTapeSymbols (fun _ => false))))
        (dgPos a₀ ((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c).inputPos) (z - 1)
        [some sweepBoundary] l
        (((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c).output.map (sweepEmbed Γ M.k)))
      1 (z - 1) z := by
  let d : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepCfg (some (.inl (.read q s))) (dgPos a₀ c.inputPos) z l
      [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k))
  have hw : d.workTapeSymbols = fun _ => some sweepBoundary := by
    funext i
    exact sweepTape_read z l _
  have he := dg_read_boundary M a₀ q s d.inputSymbol
  rw [dgInput_read a₀ c d rfl, hs, hc] at he
  simp only [Bool.false_eq_true, ↓reduceIte] at he
  have ht := dg_turn M a₀ c q s hs z l [some sweepBoundary]
  change ((dgTM M a₀).tm.tr (.inl (.growRight q s ⟨M.k, by omega⟩))
    d.inputSymbol d.workTapeSymbols).apply _ = _ at ht
  rw [hw] at ht
  apply dgSpan_one ?_ (by dsimp [sweepCfg]; constructor <;> omega)
    (by dsimp [sweepRevCfg]; constructor <;> omega)
  change ((dgTM M a₀).tm.tr (.inl (.read q s)) d.inputSymbol d.workTapeSymbols).apply d = _
  rw [hw]
  exact (congrArg (fun act => act.apply d) he).trans ht

/-- A positive crossing test allocates exactly one right row, then performs
the source action. Every prefix stays within the new right boundary.
**Proof sketch.** Compose a stationary dispatch, the delegated row writer,
and the already checked source input/output turn. -/
private lemma dg_turn_with_growth {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) (a₀ : Γ) {x : List (SweepAlphabet Γ M.k)}
    (c : Cfg M.k Γ M.State (x.map (dgRetract a₀))) (q : M.State)
    (s : Fin M.k → Option Γ × Bool) (hs : (fun i => (s i).1) = c.workTapeSymbols)
    (hc : dgCross (M.tm.tr q c.inputSymbol c.workTapeSymbols) (fun i => (s i).2) .pos = true)
    (z : ℤ) (l : List (Option (SweepAlphabet Γ M.k))) :
    DGSpan (dgTM M a₀).tm
      (sweepCfg (some (.inl (.read q s))) (dgPos a₀ c.inputPos) z l
        [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)))
      (sweepRevCfg (some (.inl (.write q c.inputSymbol c.workTapeSymbols (fun _ => false))))
        (dgPos a₀ ((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c).inputPos) (z + M.k - 1)
        [some sweepBoundary]
        (((rightRow s).map (fun b => some (sweepSymbol b))).reverse ++ l)
        (((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c).output.map (sweepEmbed Γ M.k)))
      (M.k + 2) (z - 1) (z + M.k) := by
  let p := dgPos a₀ c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let d : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepCfg (some (.inl (.read q s))) p z l [some sweepBoundary] out
  let e : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepCfg (some (.inl (.growRight q s 0))) p z l [some sweepBoundary] out
  have hw : d.workTapeSymbols = fun _ => some sweepBoundary := by
    funext i
    exact sweepTape_read z l _
  have he := dg_read_boundary M a₀ q s d.inputSymbol
  rw [dgInput_read a₀ c d rfl, hs, hc] at he
  simp only [↓reduceIte] at he
  have step : (dgTM M a₀).tm.step d = e := by
    change ((dgTM M a₀).tm.tr (.inl (.read q s)) d.inputSymbol d.workTapeSymbols).apply d = e
    rw [hw]
    exact (congrArg (fun act => act.apply d) he).trans (sweepCfg_stay _ _ _ _ _ _ _)
  have h₁ : DGSpan (dgTM M a₀).tm d e 1 (z - 1) (z + M.k) :=
    dgSpan_one step (by dsimp [d, sweepCfg]; constructor <;> omega)
      (by dsimp [e, sweepCfg]; constructor <;> omega)
  have hdrop : ([some (sweepBoundary (Γ := Γ) (k := M.k))] : List _).drop M.k = [] :=
    List.drop_eq_nil_of_le (by simpa using hk)
  have h₂ := dgSpan_mono (lo' := z - 1) (hi' := z + M.k)
    (dg_right_span M a₀ q s p out z l [some sweepBoundary]) (by omega) (by omega)
  rw [hdrop] at h₂
  have ht := dg_turn M a₀ c q s hs (z + M.k)
    (((rightRow s).map (fun b => some (sweepSymbol b))).reverse ++ l) []
  have h₃ := dgSpan_one ht
    (show z - 1 ≤ z + (M.k : ℤ) ∧ z + (M.k : ℤ) ≤ z + M.k by omega)
    (show z - 1 ≤ z + (M.k : ℤ) - 1 ∧ z + (M.k : ℤ) - 1 ≤ z + M.k by omega)
  have h := dgSpan_add (dgSpan_add h₁ h₂) h₃
  simpa only [show 1 + M.k + 1 = M.k + 2 by omega, List.tail_nil] using h

/-- The received stationary write identity also permits a halted successor.
Only its state field changes; every other field is cited from that identity. -/
private lemma dgRev_write_optional {A Q : Type} {x : List A}
    (dummy : Q) (q q' : Option Q) (p : Fin (x.length + 2)) (z : ℤ)
    (l r : List (Option A)) (out : List A) (b : Option A) :
    (⟨0, fun _ => (some b, .zero), none, q'⟩ : Action 1 A Q).apply
      (sweepRevCfg q p z l r out) = sweepRevCfg q' p z l (b :: r.tail) out := by
  have h := sweepRevCfg_write q dummy p z l r out b
  have hp := congrArg (fun (c : Cfg 1 A Q x) => c.inputPos) h
  have hw := congrArg (fun (c : Cfg 1 A Q x) => c.workTapes) h
  have hz := congrArg (fun (c : Cfg 1 A Q x) => c.workTapePos) h
  have ho := congrArg (fun (c : Cfg 1 A Q x) => c.output) h
  exact Cfg.ext rfl hp hw hz ho

/-- When no head crosses the left boundary, the return phase ends there,
including when the source action halts. No extra block is written. -/
private lemma dg_end_without_growth {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (a₀ : Γ) (q : M.State) (inp : Option Γ)
    (reads : Fin M.k → Option Γ) (right : Fin M.k → Bool)
    (hc : dgCross (M.tm.tr q inp reads) right .neg = false)
    {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ)
    (l : List (Option (SweepAlphabet Γ M.k))) :
    DGSpan (dgTM M a₀).tm
      (sweepRevCfg (some (.inl (.write q inp reads right))) p z l [some sweepBoundary] out)
      (sweepRevCfg ((M.tm.tr q inp reads).state.map (fun q => .inl (.growLeft q 0)))
        p z l [some sweepBoundary] out) 1 z z := by
  refine dgSpan_one ?_ (by change z ≤ z ∧ z ≤ z; omega)
    (by change z ≤ z ∧ z ≤ z; omega)
  let d : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepRevCfg (some (.inl (.write q inp reads right))) p z l [some sweepBoundary] out
  have hw : d.workTapeSymbols = fun _ => some sweepBoundary := by
    funext i
    exact sweepTape_read (-z) l _
  change ((dgTM M a₀).tm.tr (.inl (.write q inp reads right)) d.inputSymbol d.workTapeSymbols).apply d = _
  rw [hw]
  simp only [dgTM, sweepBoundary, hc, Bool.false_eq_true, ↓reduceIte]
  exact sweepRevCfg_stay _ _ _ _ _ _ _

/-- A left crossing creates exactly one marked blank row and moves the boundary
by its width. The endpoint may halt; containment includes the final boundary.
**Proof sketch.** Dispatch without moving, use the new left-row writer, and
write the new boundary with the optional successor state. -/
private lemma dg_end_with_growth {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) (a₀ : Γ) (q : M.State) (inp : Option Γ)
    (reads : Fin M.k → Option Γ) (right : Fin M.k → Bool)
    (hc : dgCross (M.tm.tr q inp reads) right .neg = true)
    {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ)
    (l : List (Option (SweepAlphabet Γ M.k))) :
    DGSpan (dgTM M a₀).tm
      (sweepRevCfg (some (.inl (.write q inp reads right))) p z l [some sweepBoundary] out)
      (sweepRevCfg ((M.tm.tr q inp reads).state.map (fun q => .inl (.growLeft q 0)))
        p (z - M.k)
        ((dgLeftRow (fun i => right i && decide (((M.tm.tr q inp reads).workTapes i).2 = .neg))).map
          (fun b => some (sweepSymbol b)) ++ l) [some sweepBoundary] out)
      (M.k + 2) (z - M.k) z := by
  let act := M.tm.tr q inp reads
  let heads := fun i => right i && decide ((act.workTapes i).2 = .neg)
  let d : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepRevCfg (some (.inl (.write q inp reads right))) p z l [some sweepBoundary] out
  let e : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepRevCfg (some (.inr (act.state, heads, 0))) p z l [some sweepBoundary] out
  have step : (dgTM M a₀).tm.step d = e := by
    have hw : d.workTapeSymbols = fun _ => some sweepBoundary := by
      funext i
      exact sweepTape_read (-z) l _
    change ((dgTM M a₀).tm.tr (.inl (.write q inp reads right)) d.inputSymbol d.workTapeSymbols).apply d = e
    rw [hw]
    simp only [dgTM, sweepBoundary, hc, ↓reduceIte]
    exact sweepRevCfg_stay _ _ _ _ _ _ _
  have h₁ : DGSpan (dgTM M a₀).tm d e 1 (z - M.k) z :=
    dgSpan_one step (by dsimp [d, sweepRevCfg]; constructor <;> omega)
      (by dsimp [e, sweepRevCfg]; constructor <;> omega)
  have hdrop : ([some (sweepBoundary (Γ := Γ) (k := M.k))] : List _).drop M.k = [] :=
    List.drop_eq_nil_of_le (by simpa using hk)
  have h₂ := dg_left_span M a₀ act.state heads p out z l [some sweepBoundary]
  rw [hdrop] at h₂
  let L := (dgLeftRow (Γ := Γ) heads).map (fun b => some (sweepSymbol b)) ++ l
  have last : (dgTM M a₀).tm.step
      (sweepRevCfg (some (.inr (act.state, heads, ⟨M.k, by omega⟩))) p (z - M.k) L [] out) =
      sweepRevCfg (act.state.map (fun q => .inl (.growLeft q 0))) p (z - M.k) L [some sweepBoundary] out := by
    change ((dgTM M a₀).tm.tr (.inr (act.state, heads, ⟨M.k, by omega⟩)) _ _).apply _ = _
    simp only [dgTM, lt_self_iff_false, ↓reduceDIte]
    exact dgRev_write_optional (Sum.inl SweepState.back) _ _ _ _ _ _ _ _
  have h₃ := dgSpan_one last
    (show z - (M.k : ℤ) ≤ z - M.k ∧ z - (M.k : ℤ) ≤ z by omega)
    (show z - (M.k : ℤ) ≤ z - M.k ∧ z - (M.k : ℤ) ≤ z by omega)
  have h := dgSpan_add (dgSpan_add h₁ h₂) h₃
  simpa only [show 1 + M.k + 1 = M.k + 2 by omega] using h

/-- The demand-grown left row is precisely the next source row. Its payloads
are blank and its marked heads are exactly the old boundary heads moving left.
**Proof sketch.** A source write occurs inside the old interval. At the newly
crossed coordinate only a left-moving old boundary head can arrive. -/
private lemma dg_new_left_row {Γ Q : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ Q x) (act : Action k Γ Q) (a : ℤ)
    (hp : ∀ i, a ≤ c.workTapePos i) (ht : ∀ i, c.workTapes i (a - 1) = none) :
    dgLeftRow (fun i => headAt c i a && decide ((act.workTapes i).2 = .neg)) =
      tapeRow (act.apply c) (a - 1) false := by
  unfold dgLeftRow blankRow tapeRow
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  have hi := hp i
  have hne : a - 1 ≠ c.workTapePos i := by omega
  dsimp only [Function.comp_def]
  refine Prod.ext rfl ?_
  apply Prod.ext
  · cases hw : (act.workTapes i).1 <;>
      simp [Action.apply, hw, Function.update_of_ne hne, ht i]
  · refine Prod.ext ?_ rfl
    cases hm : (act.workTapes i).2 <;> simp [headAt, Action.apply, hm, SignType.cast] <;> omega

/-- Exact cost of the conditional five-phase simulation cycle. -/
private def dgCost (k n : ℕ) (left right : Bool) : ℕ :=
  (1 + n * k) + (1 + right.toNat * (k + 1)) +
    (n + right.toNat) * k + (1 + left.toNat * (k + 1))

/-- One live source transition, with optional growth at each crossed boundary.
This includes every prefix of all five phases, even when the final state halts.
**Proof sketch.** Collect the current row interval, conditionally append its
right neighbor, apply the unchanged reverse transduction, and conditionally
prepend the new left row. Compose the five all-prefix ledgers. The ordinary
cell semantics are solely the received `read_zone` and `write_zone` facts. -/
private lemma dg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) (a₀ : Γ) {x : List (SweepAlphabet Γ M.k)}
    (c : Cfg M.k Γ M.State (x.map (dgRetract a₀)))
    (q : M.State) (hs : c.state = some q) (a z : ℤ) (n : ℕ)
    (hp : ∀ i, a ≤ c.workTapePos i ∧ c.workTapePos i < a + n)
    (hl : ∀ i, c.workTapes i (a - 1) = none)
    (hr : ∀ i, c.workTapes i (a + n) = none)
    (left right : Bool)
    (hleft : dgCross (M.tm.tr q c.inputSymbol c.workTapeSymbols)
      (fun i => headAt c i a) .neg = left)
    (hright : dgCross (M.tm.tr q c.inputSymbol c.workTapeSymbols)
      (fun i => headAt c i (a + n - 1)) .pos = right) :
    DGSpan (dgTM M a₀).tm (dgStart M a₀ c a n z)
      (dgStart M a₀ (M.tm.step c) (a - left.toNat) (n + right.toNat + left.toNat)
        (z - left.toNat * M.k))
      (dgCost M.k n left right) (z - left.toNat * M.k)
        (z + 1 + (n + right.toNat) * M.k) := by
  let act := M.tm.tr q c.inputSymbol c.workTapeSymbols
  let s := readState c (a + n)
  let p := dgPos a₀ c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let p' := dgPos a₀ (act.apply c).inputPos
  let out' := (act.apply c).output.map (sweepEmbed Γ M.k)
  let put : SweepCell Γ M.k → Option (SweepAlphabet Γ M.k) := fun b => some (sweepSymbol b)
  let F := tapeZone (fun j => tapeRow c j true) a n
  let W := tapeZone (fun j => tapeRow c j true) a (n + right.toNat)
  let V := tapeZone (fun j => tapeRow (act.apply c) j false) a (n + right.toNat)
  let lo := z - (left.toNat : ℤ) * M.k
  let hi := z + 1 + ((n + right.toNat : ℕ) : ℤ) * M.k
  let collected : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepCfg (some (.inl (.read q s))) p (z + 1 + n * M.k)
      ((F.map put).reverse ++ [some sweepBoundary]) [some sweepBoundary] out
  let writing : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepRevCfg (some (.inl (.write q c.inputSymbol c.workTapeSymbols (fun _ => false))))
      p' (z + ((n + right.toNat : ℕ) : ℤ) * M.k) [some sweepBoundary]
      (W.reverse.map put ++ [some sweepBoundary]) out'
  let written : Cfg 1 (SweepAlphabet Γ M.k) (DGState Γ M.State M.k) x :=
    sweepRevCfg (some (.inl (.write q c.inputSymbol c.workTapeSymbols (fun i => headAt c i a))))
      p' z (V.map put ++ [some sweepBoundary]) [some sweepBoundary] out'
  have hn0 : 0 ≤ (n : ℤ) * M.k := by exact_mod_cast (Nat.zero_le (n * M.k))
  have hl0 : 0 ≤ (left.toNat : ℤ) * M.k := by exact_mod_cast (Nat.zero_le (left.toNat * M.k))
  have hr0 : 0 ≤ (right.toNat : ℤ) * M.k := by exact_mod_cast (Nat.zero_le (right.toNat * M.k))
  have hsum : ((n + right.toNat : ℕ) : ℤ) * M.k = (n : ℤ) * M.k + (right.toNat : ℤ) * M.k := by
    push_cast
    ring
  have hcollect : DGSpan (dgTM M a₀).tm (dgStart M a₀ c a n z) collected
      (1 + n * M.k) lo hi :=
    dgSpan_mono (dg_collect M a₀ c q hs a z n (fun i => (hp i).1))
      (by dsimp [lo]; omega) (by dsimp [hi]; rw [add_mul]; omega)
  have hreads : (fun i => (s i).1) = c.workTapeSymbols := by
    funext i
    exact if_pos (hp i).2
  have hrtest : dgCross act (fun i => (s i).2) .pos = right := hright
  have hrow : rightRow s = tapeRow c (a + n) true := by
    unfold rightRow tapeRow
    apply List.map_congr_left
    intro i _
    have hn : c.workTapePos i ≠ a + n := by have := (hp i).2; omega
    simp [s, readState, headAt, hr i, hn]
  have hdispatch : DGSpan (dgTM M a₀).tm collected writing
      (1 + right.toNat * (M.k + 1)) lo hi := by
    cases right with
    | false =>
      have h := dg_turn_without_growth M a₀ c q s hreads hrtest (z + 1 + n * M.k)
        ((F.map put).reverse ++ [some sweepBoundary])
      have h := dgSpan_mono (lo' := lo) (hi' := hi) h
        (by dsimp [lo]; omega) (by dsimp [hi]; omega)
      have hz : z + 1 + (n : ℤ) * M.k - 1 = z + n * M.k := by omega
      simpa only [collected, writing, W, F, Bool.toNat_false, Nat.add_zero,
        Nat.zero_mul, hz, List.map_reverse] using h
    | true =>
      have h := dg_turn_with_growth M hk a₀ c q s hreads hrtest (z + 1 + n * M.k)
        ((F.map put).reverse ++ [some sweepBoundary])
      have he : tapeZone (fun j => tapeRow c j true) a (n + 1) = F ++ rightRow s := by
        rw [tapeZone_append, hrow]
        simp only [tapeZone, List.append_nil]
        rfl
      have hh : z + 1 + (n : ℤ) * M.k + M.k = hi := by
        dsimp [hi]
        ring
      have hz : z + 1 + (n : ℤ) * M.k + M.k - 1 = z + ((n + 1 : ℕ) : ℤ) * M.k := by
        push_cast
        ring
      have h := dgSpan_mono (lo' := lo) (hi' := hi) h
        (by dsimp [lo]; omega) (le_of_eq hh)
      simpa [collected, writing, W, put, p, p', out, out', act, Bool.toNat_true, he, List.map_append,
        List.reverse_append, List.map_reverse, List.append_assoc, hz,
        show 1 + (M.k + 1) = M.k + 2 by omega] using h
  have hzero : (fun i => headAt c i (a + (n + right.toNat : ℕ))) = fun _ => false := by
    funext i
    have h := (hp i).2
    simp only [headAt, decide_eq_false_iff_not]
    omega
  have hwrite : DGSpan (dgTM M a₀).tm writing written ((n + right.toNat) * M.k) lo hi := by
    constructor
    · have h := dg_write M a₀ c q c.inputSymbol c.workTapeSymbols a
        (z + ((n + right.toNat : ℕ) : ℤ) * M.k) (n + right.toNat) p' out'
        [some sweepBoundary] [some sweepBoundary]
      rw [hzero] at h
      simpa only [writing, written, W, V, put, act, add_sub_cancel_right] using h
    · intro u hu
      have h := dg_sweep_reverse_prefix (dgTM M a₀).tm
        (fun r => Sum.inl (SweepState.write q c.inputSymbol c.workTapeSymbols r))
        sweepSymbol (writeVisit act) (by intro r b inp; rfl) p' out' W.reverse
        (fun _ => false) (z + ((n + right.toNat : ℕ) : ℤ) * M.k)
        [some sweepBoundary] [some sweepBoundary] u
        (by simpa only [W, List.length_reverse, tapeZone_length] using hu)
      change ((dgTM M a₀).tm.runFrom writing u).workTapePos (0 : Fin 1) =
        z + ((n + right.toNat : ℕ) : ℤ) * M.k - u at h
      rw [h]
      have hu' : (u : ℤ) ≤ ((n + right.toNat : ℕ) : ℤ) * M.k := by exact_mod_cast hu
      simp only [Int.natCast_add] at h hu'
      dsimp [lo, hi]
      constructor <;> omega
  have hfinish : DGSpan (dgTM M a₀).tm written
      (dgStart M a₀ (act.apply c) (a - left.toNat) (n + right.toNat + left.toNat)
        (z - left.toNat * M.k)) (1 + left.toNat * (M.k + 1)) lo hi := by
    cases left with
    | false =>
      have h := dg_end_without_growth M a₀ q c.inputSymbol c.workTapeSymbols
        (fun i => headAt c i a) hleft p' out' z (V.map put ++ [some sweepBoundary])
      have h := dgSpan_mono (lo' := lo) (hi' := hi) h
        (by dsimp [lo]; simp) (by dsimp [hi]; rw [add_mul]; omega)
      simpa only [written, dgStart, V, put, act, Bool.toNat_false, Nat.zero_mul,
        Int.natCast_zero, zero_mul, sub_zero, Nat.add_zero] using h
    | true =>
      have h := dg_end_with_growth M hk a₀ q c.inputSymbol c.workTapeSymbols
        (fun i => headAt c i a) hleft p' out' z (V.map put ++ [some sweepBoundary])
      have he := dg_new_left_row c act a (fun i => (hp i).1) hl
      rw [he] at h
      have h := dgSpan_mono (lo' := lo) (hi' := hi) h
        (by dsimp [lo]; simp) (by dsimp [hi]; rw [add_mul]; omega)
      simpa only [written, dgStart, Bool.toNat_true, Nat.one_mul, Int.natCast_one,
        one_mul, tapeZone, show a - 1 + 1 = a by omega, List.map_append,
        List.append_assoc, V, put, act, show 1 + (M.k + 1) = M.k + 2 by omega] using h
  have h := dgSpan_add (dgSpan_add (dgSpan_add hcollect hdispatch) hwrite) hfinish
  simpa only [dgCost, MultiTapeTM.step, hs, act] using h

/-- The represented coordinate interval contains the source heads and support,
and every represented coordinate has really been visited by some source head.
The `size` field is a separate elapsed-time bound used only for the time ledger. -/
private structure DGWindow {Γ : Type} (M : FinTM Γ) (x : List Γ)
    (t : ℕ) (a : ℤ) (n : ℕ) : Prop where
  positive : 0 < n
  heads : ∀ i, a ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
    (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i < a + n
  blank : ∀ i j, j < a ∨ a + n ≤ j →
    (M.tm.runFrom (M.tm.initCfg x) t).workTapes i j = none
  visited : ∀ j, a ≤ j → j < a + n → ∃ i u, u ≤ t ∧
    (M.tm.runFrom (M.tm.initCfg x) u).workTapePos i = j
  size : n ≤ 2 * t + 1
  history : ∀ i u, u ≤ t → a ≤ (M.tm.runFrom (M.tm.initCfg x) u).workTapePos i ∧
    (M.tm.runFrom (M.tm.initCfg x) u).workTapePos i < a + n

/-- Positive tape count makes the origin a genuinely visited coordinate. -/
private lemma dgWindow_init {Γ : Type} (M : FinTM Γ) (hk : 0 < M.k) (x : List Γ) :
    DGWindow M x 0 0 1 := by
  refine ⟨by omega, ?_, ?_, ?_, by omega, ?_⟩
  · intro i
    simp
  · intro i j hj
    rfl
  · intro j hj₁ hj₂
    refine ⟨⟨0, hk⟩, 0, le_refl _, ?_⟩
    simp only [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg, Cfg.init]
    omega
  · intro i u hu
    have he : u = 0 := by omega
    subst u
    simp

/-- Conditional growth preserves the exact visited-coordinate cover.
**Proof sketch.** Unit-speed source movement stays in the enlarged interval.
A write cannot escape the old interval. Any new coordinate is one of its two
neighbors, and its crossing flag supplies a source head at that coordinate
at the next time. Both ends grow by at most one, giving the size recurrence. -/
private lemma dgWindow_step {Γ : Type} (M : FinTM Γ) (x : List Γ)
    (t : ℕ) (a : ℤ) (n : ℕ) (w : DGWindow M x t a n)
    (act : Action M.k Γ M.State)
    (hstep : M.tm.runFrom (M.tm.initCfg x) (t + 1) =
      act.apply (M.tm.runFrom (M.tm.initCfg x) t))
    (left right : Bool)
    (hleft : dgCross act (fun i => headAt (M.tm.runFrom (M.tm.initCfg x) t) i a) .neg = left)
    (hright : dgCross act (fun i => headAt (M.tm.runFrom (M.tm.initCfg x) t) i (a + n - 1)) .pos = right) :
    DGWindow M x (t + 1) (a - left.toNat) (n + right.toNat + left.toNat) := by
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have hl : left.toNat ≤ 1 := by cases left <;> decide
  have hr : right.toNat ≤ 1 := by cases right <;> decide
  have hL (i : Fin M.k) (hi : c.workTapePos i = a) (hd : (act.workTapes i).2 = .neg) : left = true := by
    rw [← hleft]
    simp only [dgCross, decide_eq_true_eq]
    exact ⟨i, by simp only [headAt, show (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i = a from hi,
      decide_true], hd⟩
  have hR (i : Fin M.k) (hi : c.workTapePos i = a + n - 1) (hd : (act.workTapes i).2 = .pos) : right = true := by
    rw [← hright]
    simp only [dgCross, decide_eq_true_eq]
    exact ⟨i, by simp only [headAt, show (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i = a + n - 1 from hi,
      decide_true], hd⟩
  have hheads : ∀ i, a - left.toNat ≤ (M.tm.runFrom (M.tm.initCfg x) (t + 1)).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) (t + 1)).workTapePos i <
        a - left.toNat + (n + right.toNat + left.toNat : ℕ) := by
    intro i
    rw [hstep]
    have hp := w.heads i
    change a ≤ c.workTapePos i ∧ c.workTapePos i < a + n at hp
    change a - left.toNat ≤ (act.apply c).workTapePos i ∧
      (act.apply c).workTapePos i < a - left.toNat + (n + right.toNat + left.toNat : ℕ)
    cases hm : (act.workTapes i).2 with
    | neg =>
      have h : c.workTapePos i = a → left.toNat = 1 := fun he => by rw [hL i he hm]; rfl
      simp only [Action.apply, hm, SignType.cast]
      constructor <;> omega
    | zero =>
      simp only [Action.apply, hm, SignType.cast]
      constructor <;> omega
    | pos =>
      have h : c.workTapePos i = a + n - 1 → right.toNat = 1 := fun he => by rw [hR i he hm]; rfl
      simp only [Action.apply, hm, SignType.cast]
      constructor <;> omega
  refine ⟨by have := w.positive; omega, hheads, ?_, ?_, by have := w.size; omega, ?_⟩
  · intro i j hj
    rw [hstep]
    have hout : j < a ∨ a + n ≤ j := by omega
    have hjnone : c.workTapes i j = none := w.blank i j hout
    have hp := w.heads i
    have hne : j ≠ c.workTapePos i := by
      change a ≤ c.workTapePos i ∧ c.workTapePos i < a + n at hp
      omega
    change (act.apply c).workTapes i j = none
    cases hw : (act.workTapes i).1 <;>
      simp [Action.apply, hw, Function.update_of_ne hne, hjnone]
  · intro j hj₁ hj₂
    by_cases hjlo : a ≤ j
    · by_cases hjhi : j < a + n
      · obtain ⟨i, u, hu, he⟩ := w.visited j hjlo hjhi
        exact ⟨i, u, by omega, he⟩
      · have he : j = a + n := by omega
        have ht : right = true := by cases right <;> simp_all only [Bool.toNat_false, Bool.toNat_true] <;> omega
        have hit : ∃ i, c.workTapePos i = a + n - 1 ∧ (act.workTapes i).2 = .pos := by
          have h := hright.trans ht
          simpa only [dgCross, headAt, decide_eq_true_eq] using h
        obtain ⟨i, hi, hd⟩ := hit
        refine ⟨i, t + 1, le_refl _, ?_⟩
        rw [hstep]
        change (act.apply c).workTapePos i = j
        simp only [Action.apply, hd, SignType.cast]
        omega
    · have he : j = a - 1 := by omega
      have ht : left = true := by cases left <;> simp_all only [Bool.toNat_false, Bool.toNat_true] <;> omega
      have hit : ∃ i, c.workTapePos i = a ∧ (act.workTapes i).2 = .neg := by
        have h := hleft.trans ht
        simpa only [dgCross, headAt, decide_eq_true_eq] using h
      obtain ⟨i, hi, hd⟩ := hit
      refine ⟨i, t + 1, le_refl _, ?_⟩
      rw [hstep]
      change (act.apply c).workTapePos i = j
      simp only [Action.apply, hd, SignType.cast]
      omega
  · intro i u hu
    by_cases hu' : u ≤ t
    · have h := w.history i u hu'
      constructor <;> omega
    · have he : u = t + 1 := by omega
      subst u
      exact hheads i

/-- The represented width is bounded by total source space: the interval
injects into the union of the source heads' visited sets.
**Proof sketch.** Use the window's visited witness for each coordinate, then
bound the cardinality of the union by the sum over source tapes. -/
private lemma dgWindow_space {Γ : Type} (M : FinTM Γ) (x : List Γ)
    (t : ℕ) (a : ℤ) (n : ℕ) (w : DGWindow M x t a n) :
    n ≤ M.tm.spaceUsed (M.tm.initCfg x) t := by
  let cover := Finset.univ.biUnion (fun i => M.tm.visitedByTapeHead (M.tm.initCfg x) t i)
  have hsub : Finset.Icc a (a + n - 1) ⊆ cover := by
    intro j hj
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
    obtain ⟨i, u, hu, he⟩ := w.visited j hj₁ (by omega)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), he⟩⟩
  have hcard : (Finset.Icc a (a + n - 1)).card = n := by rw [Int.card_Icc]; omega
  rw [← hcard]
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-- The new cycle cost has the same quadratic numerical majorant as the old
cost formula. This is a fresh comparison of costs, not use of the old machine
as a space witness or use of its timing theorem for the new machine. -/
private lemma dgCost_le (k t n : ℕ) (hk : 0 < k) (hn : n ≤ 2 * t + 1)
    (left right : Bool) : dgCost k n left right ≤ (4 * t + 7) * k + 4 := by
  have h := Nat.mul_le_mul_right k hn
  cases left <;> cases right <;>
    simp only [dgCost, Bool.toNat_false, Bool.toNat_true, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero, Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at h ⊢ <;> omega

/-- Every source prefix before its first halt has a canonical simulated
endpoint, with an all-prefix physical ledger and a quadratic time majorant.
**Proof sketch.** Initialize at the origin. At each live step use the two
crossing flags, preserve the source window, and concatenate the contained
macro-step with the earlier trajectory. The interval only enlarges. The exact
new cycle cost is bounded before invoking the old numerical sum formula. -/
private lemma dg_simulate {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) (a₀ : Γ) (x : List (SweepAlphabet Γ M.k))
    (τ : ℕ) (hlive : ∀ t < τ,
      (M.tm.runFrom (M.tm.initCfg (x.map (dgRetract a₀))) t).state ≠ none) :
    ∀ t ≤ τ, ∃ (a : ℤ) (n u : ℕ),
      DGWindow M (x.map (dgRetract a₀)) t a n ∧ u ≤ sweepTime M.k t ∧
      DGSpan (dgTM M a₀).tm ((dgTM M a₀).tm.initCfg x)
        (dgStart M a₀ (M.tm.runFrom (M.tm.initCfg (x.map (dgRetract a₀))) t)
          a n (a * M.k - 1)) u (a * M.k - 1) ((a + n) * M.k) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨0, 1, 2 * M.k + 2, dgWindow_init M hk _, le_refl _, ?_⟩
    simpa only [MultiTapeTM.runFrom_zero, zero_mul, zero_sub, Int.natCast_one,
      zero_add, one_mul] using dg_init M a₀ x
  | succ t ih =>
    intro ht
    obtain ⟨a, n, u, w, htime, hspan⟩ := ih (by omega)
    let c := M.tm.runFrom (M.tm.initCfg (x.map (dgRetract a₀))) t
    obtain ⟨q, hs⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
    let act := M.tm.tr q c.inputSymbol c.workTapeSymbols
    let left := dgCross act (fun i => headAt c i a) .neg
    let right := dgCross act (fun i => headAt c i (a + n - 1)) .pos
    have hstep : M.tm.runFrom (M.tm.initCfg (x.map (dgRetract a₀))) (t + 1) = act.apply c := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      simp only [MultiTapeTM.step, hs]
      rfl
    have w' := dgWindow_step M (x.map (dgRetract a₀)) t a n w act hstep left right rfl rfl
    have hcycle := dg_step M hk a₀ c q hs a (a * M.k - 1) n w.heads
      (fun i => w.blank i (a - 1) (Or.inl (by omega)))
      (fun i => w.blank i (a + n) (Or.inr (le_refl _))) left right rfl rfl
    have hnext : M.tm.step c = M.tm.runFrom (M.tm.initCfg (x.map (dgRetract a₀))) (t + 1) := by
      exact MultiTapeTM.runFrom_succ_eq_step'.symm
    rw [hnext] at hcycle
    have hlo : a * M.k - 1 - (left.toNat : ℤ) * M.k = (a - left.toNat) * M.k - 1 := by ring
    have hhi : a * M.k - 1 + 1 + ((n : ℤ) + right.toNat) * M.k =
        (a - left.toNat + (n + right.toNat + left.toNat : ℕ)) * M.k := by push_cast; ring
    rw [hlo, hhi] at hcycle
    have hl0 : 0 ≤ (left.toNat : ℤ) * M.k := by exact_mod_cast (Nat.zero_le (left.toNat * M.k))
    have hr0 : 0 ≤ (right.toNat : ℤ) * M.k := by exact_mod_cast (Nat.zero_le (right.toNat * M.k))
    have hlower : (a - left.toNat) * M.k - 1 ≤ a * M.k - 1 := by rw [sub_mul]; omega
    have hupper : (a + n) * M.k ≤
        (a - left.toNat + (n + right.toNat + left.toNat : ℕ)) * M.k := by
      have he : (a - left.toNat + (n + right.toNat + left.toNat : ℕ)) * M.k =
          (a + n) * M.k + (right.toNat : ℤ) * M.k := by push_cast; ring
      rw [he]
      omega
    refine ⟨a - left.toNat, n + right.toNat + left.toNat,
      u + dgCost M.k n left right, w', ?_, ?_⟩
    · exact Nat.add_le_add htime (dgCost_le M.k t n hk w.size left right)
    · exact dgSpan_add (dgSpan_mono hspan hlower hupper) hcycle

/-- The demand-grown witness computes on every native word after finite-control
retraction, with both resource bounds at that word's unchanged length.
**Proof sketch.** Simulate through the source's first halt. The final window is
exactly covered by source visits, while the whole physical trajectory lies
between its boundary cells. Halting absorption extends that containment to
all later times. Its cardinality is `n*k+2`; the window bound and a single
coefficient absorb both this space ledger and the quadratic time ledger. -/
private lemma dg_all_inputs {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) (a₀ : Γ)
    (f : List Γ → List Γ) (T S : ℕ → ℕ) (hM : M.ComputesFunInTime f T)
    (hS : ∀ y t, M.tm.spaceUsed (M.tm.initCfg y) t ≤ S y.length)
    (x : List (SweepAlphabet Γ M.k)) :
    (dgTM M a₀).ComputesInTime x ((f (x.map (dgRetract a₀))).map (sweepEmbed Γ M.k))
      ((9 * M.k + 6) * (T x.length + 1) ^ 2) ∧
    ∀ t, (dgTM M a₀).tm.spaceUsed ((dgTM M a₀).tm.initCfg x) t ≤
      (9 * M.k + 6) * (S x.length + 1) := by
  let y := x.map (dgRetract a₀)
  obtain ⟨hhalt, hout⟩ := (computesInTime_iff M y (f y) (T y.length)).mp (hM y)
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg y) t).state = none := ⟨T y.length, hhalt⟩
  let τ := Nat.find hex
  have hτ : (M.tm.runFrom (M.tm.initCfg y) τ).state = none := Nat.find_spec hex
  have htime : τ ≤ T y.length := Nat.find_min' hex hhalt
  have hlive : ∀ t < τ, (M.tm.runFrom (M.tm.initCfg y) t).state ≠ none :=
    fun _ h => Nat.find_min hex h
  obtain ⟨a, n, u, window, hu, span⟩ := dg_simulate M hk a₀ x τ hlive τ (le_refl _)
  have houtτ : (M.tm.runFrom (M.tm.initCfg y) τ).output = f y :=
    (M.tm.runFrom_output_eq_of_halt (M.tm.initCfg y) htime hτ).symm.trans hout
  let final := dgStart M a₀ (M.tm.runFrom (M.tm.initCfg y) τ) a n (a * M.k - 1)
  have hf : final.state = none := by
    change (M.tm.runFrom (M.tm.initCfg y) τ).state.map _ = none
    rw [hτ]
    rfl
  have compute : (dgTM M a₀).ComputesInTime x ((f y).map (sweepEmbed Γ M.k)) u := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [span.1]
    constructor
    · exact hf
    · change (M.tm.runFrom (M.tm.initCfg y) τ).output.map (sweepEmbed Γ M.k) = _
      rw [houtτ]
  have hpositions (v : ℕ) :
      a * M.k - 1 ≤ ((dgTM M a₀).tm.runFrom ((dgTM M a₀).tm.initCfg x) v).workTapePos (0 : Fin 1) ∧
      ((dgTM M a₀).tm.runFrom ((dgTM M a₀).tm.initCfg x) v).workTapePos (0 : Fin 1) ≤ (a + n) * M.k := by
    by_cases hv : v ≤ u
    · exact span.2 v hv
    · have he : v = u + (v - u) := by omega
      rw [he, MultiTapeTM.runFrom_add, span.1, MultiTapeTM.runFrom_of_halt _ hf]
      have h := span.2 u (le_refl _)
      rw [span.1] at h
      exact h
  constructor
  · apply compute.mono
    calc u ≤ sweepTime M.k τ := hu
      _ ≤ (9 * M.k + 6) * (τ + 1) ^ 2 := sweepTime_le M.k τ
      _ ≤ (9 * M.k + 6) * (T x.length + 1) ^ 2 := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        simpa only [y, List.length_map] using Nat.add_le_add_right htime 1
  · intro v
    have hsub : (dgTM M a₀).tm.visitedByTapeHead ((dgTM M a₀).tm.initCfg x) v (0 : Fin 1) ⊆
        Finset.Icc (a * M.k - 1) ((a + n) * M.k) := by
      intro j hj
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_Icc.mpr (hpositions s)
    have hcard : (Finset.Icc (a * M.k - 1) ((a + n) * M.k)).card = n * M.k + 2 := by
      rw [Int.card_Icc]
      have he : (a + n) * M.k + 1 - (a * M.k - 1) = ((n * M.k + 2 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [he, Int.toNat_natCast]
    have hphysical : (dgTM M a₀).tm.spaceUsed ((dgTM M a₀).tm.initCfg x) v ≤ n * M.k + 2 := by
      change (∑ i : Fin 1, ((dgTM M a₀).tm.visitedByTapeHead ((dgTM M a₀).tm.initCfg x) v i).card) ≤ _
      have hz (i : Fin 1) : i = 0 := Subsingleton.elim _ _
      simp only [hz, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, one_mul]
      rw [← hcard]
      exact Finset.card_le_card hsub
    have hn : n ≤ S x.length := by
      have h := (dgWindow_space M y τ a n window).trans (hS y τ)
      simpa only [y, List.length_map] using h
    refine hphysical.trans ?_
    calc n * M.k + 2 ≤ (S x.length + 1) * M.k + 2 * (S x.length + 1) :=
        Nat.add_le_add
          ((Nat.mul_le_mul_right M.k hn).trans (Nat.mul_le_mul_right M.k (Nat.le_succ _)))
          (Nat.le_mul_of_pos_right 2 (Nat.succ_pos _))
      _ = (M.k + 2) * (S x.length + 1) := by ring
      _ ≤ (9 * M.k + 6) * (S x.length + 1) := Nat.mul_le_mul_right _ (by omega)

/-- The one-work-tape reduction preserves space up to a constant: the
single-tape machine of `Turing.FinTM.one_work_tape` can be taken with an
all-time space bound of coefficient-constant shape in the source's. Part
of the Z4 space annotation (`machine-library-design.md` §13), plan §2.7's
fallback route to the space-efficient universal (Ex 4.1).

**Proof sketch** (round-1 repair, A-S2-2 of `audits/zone-infra-findings.md`
— the received `sweepTM` witness does NOT satisfy this bound: its
`.growLeft`/`.growRight` phases extend the swept window unconditionally
every macro-step, so a stationary-work-head input scanner has source space
`1` but simulator space `Ω(n)`; the audit's counterexample is binding).
The fill constructs a **demand-grown** sweep witness, reusing and
refactoring the existing sweep infrastructure without copying it: extend a
boundary only when a simulated head first crosses it. Each source tape's
visited interval contains the origin, so the union's cardinality is at
most the sum of the source cardinalities — the total source space; an
interleaved `M.k`-cells-per-coordinate realization pays a factor `M.k`
and a constant boundary allowance, absorbed into `c`. Mid-sweep visits lie
inside the represented source-visited intervals through the current
transition plus the allowance; a halted simulation is fixed. The space
conclusion ranges over **all** `Γ'`-words: for nonempty `Γ`, a
finite-control retraction fixing `e` simulates the same-length retracted
source input (so `hS` applies with no monotonicity); for empty `Γ`, every
source word is empty and an immediately halting one-tape machine suffices;
for `M.k = 0`, the unused-tape embedding visits one cell, inside
`c * (S + 1)`. -/
theorem one_work_tape_spaceUsed {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T S : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T)
    (hS : ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ S x.length) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f (fun n => c * (T n + 1) ^ 2) ∧
      ∀ x t, M'.tm.spaceUsed (M'.tm.initCfg x) t ≤ c * (S x.length + 1) := by
  classical
  by_cases hk : M.k = 0
  · refine ⟨Γ, inferInstance, inferInstance, Function.Embedding.refl Γ,
      unusedTapeTM M hk, 1, rfl, ?_, ?_⟩
    · intro x
      simpa only [Function.Embedding.coe_refl, List.map_id, one_mul] using
        ((unusedTape_computes M hk f T hM) x).mono
          (show T x.length ≤ (T x.length + 1) ^ 2 from
            (Nat.le_succ _).trans (by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
    · intro x t
      rw [dg_unused_space]
      simp only [one_mul]
      omega
  by_cases hΓ : Nonempty Γ
  · obtain ⟨a₀⟩ := hΓ
    refine ⟨SweepAlphabet Γ M.k, inferInstance, inferInstance, sweepEmbed Γ M.k,
      dgTM M a₀, 9 * M.k + 6, rfl, ?_, ?_⟩
    · intro y
      have h := (dg_all_inputs M (Nat.pos_of_ne_zero hk) a₀ f T S hM hS
        (y.map (sweepEmbed Γ M.k))).1
      simpa only [List.map_map, Function.comp_def, dgRetract_embed,
        List.map_id_fun', id_eq, List.length_map] using h
    · intro x t
      exact (dg_all_inputs M (Nat.pos_of_ne_zero hk) a₀ f T S hM hS x).2 t
  · let Z : FinTM Γ :=
      { k := 0
        State := Unit
        tm := { q₀ := (), tr := fun _ _ _ => ⟨0, fun i => i.elim0, none, none⟩ } }
    have hZ : Z.ComputesFunInTime f (fun _ => 1) := by
      intro x
      have hx : f x = [] := by
        cases he : f x with
        | nil => rfl
        | cons a as => exact (hΓ ⟨a⟩).elim
      apply (computesInTime_iff _ _ _ _).mpr
      rw [hx]
      exact ⟨rfl, rfl⟩
    refine ⟨Γ, inferInstance, inferInstance, Function.Embedding.refl Γ,
      unusedTapeTM Z rfl, 1, rfl, ?_, ?_⟩
    · intro x
      simpa only [Function.Embedding.coe_refl, List.map_id, one_mul] using
        ((unusedTape_computes Z rfl f (fun _ => 1) hZ) x).mono
          (show 1 ≤ (T x.length + 1) ^ 2 from Nat.pow_pos (Nat.succ_pos _))
    · intro x t
      rw [dg_unused_space]
      simp only [one_mul]
      omega

/-- The binary one-work-tape normal form preserves space up to a constant:
the composed conversion of `Turing.FinTM.one_work_tape_binary` with the
space clause carried through both stages. This is the exact deliverable
shape of plan §2.7's fallback for Ex 4.1/Thm 4.8: a space-faithful route
into the one-tape binary normal form.

**Proof sketch.** Chain the **corrected** first stage
(`Turing.FinTM.one_work_tape_spaceUsed`, whose round-2 route is the
demand-grown witness) with `Turing.FinTM.alphabet_reduction_spaceUsed`;
with first-stage coefficient `c₁` and second-stage `c₂`, both clauses are
absorbed by the single coefficient `c₂ * (c₁ + 1)` (the round-1 audit's
composition calculation). -/
theorem one_work_tape_binary_spaceUsed (M : FinTM Bool)
    (f : List Bool → List Bool) (T S : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T)
    (hS : ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ S x.length) :
    ∃ (M' : FinTM Bool) (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTime f (fun n => c * (T n + 1) ^ 2) ∧
      ∀ x t, M'.tm.spaceUsed (M'.tm.initCfg x) t ≤ c * (S x.length + 1) := by
  obtain ⟨Γ', instF, instD, e, M₁, c₁, hk₁, h₁, hs₁⟩ :=
    one_work_tape_spaceUsed M f T S hM hS
  haveI := instF
  haveI := instD
  obtain ⟨c₂, M₂, hk₂, h₂, hs₂⟩ :=
    alphabet_reduction_spaceUsed e M₁ f (fun n => c₁ * (T n + 1) ^ 2)
      (fun n => c₁ * (S n + 1)) h₁ hs₁
  refine ⟨M₂, c₂ * (c₁ + 1), by rw [hk₂, hk₁], ?_, ?_⟩
  · intro x
    apply (h₂ x).mono
    have hpow : 1 ≤ (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
    calc c₂ * (c₁ * (T x.length + 1) ^ 2 + 1)
        ≤ c₂ * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left hpow _)
      _ = c₂ * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring
  · intro x t
    calc M₂.tm.spaceUsed (M₂.tm.initCfg x) t
        ≤ c₂ * (c₁ * (S x.length + 1) + 1) := hs₂ x t
      _ ≤ c₂ * (c₁ * (S x.length + 1) + (S x.length + 1)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.succ_pos _) _)
      _ = c₂ * (c₁ + 1) * (S x.length + 1) := by ring

end Turing.FinTM
