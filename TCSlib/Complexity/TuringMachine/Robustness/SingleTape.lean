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
