/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Valid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One machine step as a local relation between code words

[AB09, §4.1.1]: an edge `C → C'` of the configuration graph is one transition. On code words
it is *local*: the chunk of cell `z` of `C'` is a function `Complexity.Codec.stepCell` of the
chunks of cells `z - 1`, `z`, `z + 1` of `C` and of the applied action (which writes at the
head and moves the head flag by one cell), and the new configuration stays in the window
exactly when no head flag would leave the region. So the sliding check of
`TCSlib.Complexity.SpaceComplexity.Codec.Scan`, with `stepCell` as its rule, recognizes the
chunk region of the successor; the input position and the header (state and output summary)
are updated by the action.

Configuration-graph infrastructure for the codec checkers; not a result of [AB09].

## Main definitions

* `Complexity.Codec.effAct` — the action applied in a step: the transition under the choice
  bit, or idling once halted.
* `Complexity.Codec.stepCell`, `Complexity.Codec.stepG` — the local rule of a step.
* `Complexity.Codec.sScan`, `Complexity.Codec.sDone` — the sliding check of two chunk
  regions under two rules at once (the two choice bits), and its verdict.

## Main results

* `Complexity.Codec.stepWith_eq_apply` — a step applies the effective action.
* `Complexity.Codec.cellOf_apply` — the cells of the successor, cell by cell.
* `Complexity.Codec.slide_step_iff` — the sliding verdict recognizes the successor's chunk
  region and its window bound.
* `Complexity.Codec.sScan_eq` — the letter-level scan is the chunk-level one.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {x : List Bool}

/-! ## The applied action -/

variable (N) in
/-- The idle action: no moves, no writes, no output, halted. -/
def idleAct : Action N.k Bool N.State := ⟨0, fun _ => (none, 0), none, none⟩

variable (N) in
/-- **The action of a step** of `N` under the choice bit `b`, in a configuration with control
state `q`, input symbol `inp` and work symbols `ws`: the transition `tr b q inp ws`, or the
idle action once halted. -/
def effAct (q : Option N.State) (inp : Option Bool) (ws : Fin N.k → Option Bool) (b : Bool) :
    Action N.k Bool N.State :=
  match q with
  | none => idleAct N
  | some q => N.tm.tr b q inp ws

/-- **A step applies the effective action** (the idle action leaves a halted configuration
unchanged). -/
theorem stepWith_eq_apply (b : Bool) (C : Cfg N.k Bool N.State x) :
    N.tm.stepWith b C = (effAct N C.state C.inputSymbol C.workTapeSymbols b).apply C := by
  cases h : C.state with
  | none =>
    rw [NDTM.stepWith_of_halt h]
    simp only [effAct, idleAct]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp [h]
    · simp [moveInputPos_zero]
    · rfl
    · funext i; simp
    · simp
  | some q => simp only [NDTM.stepWith, h, effAct]

/-- The summary index after appending an optional output letter. -/
def sumUpd : Fin 3 → Option Bool → Fin 3
  | 0, none => 0
  | 0, some true => 1
  | 0, some false => 2
  | 1, none => 1
  | 1, some _ => 2
  | 2, _ => 2

/-- The summary of an extended output is a function of the old summary and the letter. -/
lemma sumIdx_append (u : List Bool) (o : Option Bool) :
    sumIdx (outSummary (u ++ o.toList)) = sumUpd (sumIdx (outSummary u)) o := by
  rcases u with _ | ⟨a, _ | ⟨b, u⟩⟩ <;> rcases o with _ | ⟨_ | _⟩ <;>
    (try cases a) <;> rfl

/-- The header after applying an action. -/
def newHd (a : Action N.k Bool N.State) (h : Hd N) : Hd N := (a.state, sumUpd h.2 a.output)

/-! ## The local rule -/

variable (N) in
/-- The empty cell, read outside the region: no header, blank, no head. -/
def cellE : CellV N := (none, fun _ => (none, false))

/-- **The local rule of a step** under the action `a` with new header `h'`: the cell keeps
its header slot (relabelled `h'`), the action writes at a flagged head, and the head flag
moves from the left neighbour (right move) or the right neighbour (left move). -/
def stepCell (a : Action N.k Bool N.State) (h' : Hd N) (l c r : CellV N) : CellV N :=
  (c.1.map fun _ => h',
    fun i => (if (c.2 i).2 then (a.workTapes i).1.getD (c.2 i).1 else (c.2 i).1,
      match (a.workTapes i).2 with
      | .zero => (c.2 i).2
      | .pos => (l.2 i).2
      | .neg => (r.2 i).2))

/-- The local rule on decoded chunks (`none` for an undecodable chunk). -/
def stepG (a : Action N.k Bool N.State) (h' : Hd N) :
    Option (CellV N) → Option (CellV N) → Option (CellV N) → Option (CellV N)
  | some l, some c, some r => some (stepCell a h' l c r)
  | _, _, _ => none

/-- The header of a configuration. -/
def hdOf (C : Cfg N.k Bool N.State x) : Hd N := (C.state, sumIdx (outSummary C.output))

/-- The left neighbour of cell `j` in the region (empty beyond the left end). -/
def nbL (s : ℕ) (C : Cfg N.k Bool N.State x) (j : ℕ) : CellV N :=
  if j = 0 then cellE N else cellOf s C (j - 1)

/-- The right neighbour of cell `j` in the region (empty beyond the right end). -/
def nbR (s : ℕ) (C : Cfg N.k Bool N.State x) (j : ℕ) : CellV N :=
  if j + 1 < 2 * s + 1 then cellOf s C (j + 1) else cellE N

/-- Casting the three signs to `ℤ`. -/
private lemma signType_cast (m : SignType) :
    (m : ℤ) = match m with | .zero => 0 | .pos => 1 | .neg => -1 := by
  cases m <;> rfl

/-- **The cells of the successor**: applying an action to a window-bounded configuration
changes each cell by the local rule.

**Proof sketch.** Componentwise. The header slot of the leftmost cell carries the new state
and the updated summary (`sumIdx_append`). A tape cell changes only under the head, by the
written symbol. The new head of a tape is at `pos + m` for the move `m`, so the cell at `z`
is flagged iff the old flag sits at `z - m`, i.e. in the left neighbour for a right move and
in the right neighbour for a left move; beyond the region there is no old head (window). -/
theorem cellOf_apply (s : ℕ) (C : Cfg N.k Bool N.State x) (hC : InWin N s C)
    (a : Action N.k Bool N.State) (j : ℕ) (hj : j < 2 * s + 1) :
    cellOf s (a.apply C) j =
      stepCell a (newHd a (hdOf C)) (nbL s C j) (cellOf s C j) (nbR s C j) := by
  simp only [cellOf, stepCell, newHd, hdOf]
  refine Prod.ext ?_ (funext fun i => Prod.ext ?_ ?_)
  · by_cases hj0 : j = 0 <;> simp [hj0, Action.apply, sumIdx_append]
  · simp only [Action.apply]
    cases hw : (a.workTapes i).1 with
    | none =>
      simp only [Option.getD_none]
      split <;> rfl
    | some w =>
      simp only [Option.getD_some]
      by_cases hz : C.workTapePos i = (j : ℤ) - s
      · rw [show ((j : ℤ) - s) = C.workTapePos i from hz.symm]; simp
      · simp [hz, Function.update_of_ne (Ne.symm hz)]
  · have hp := (hC i).1
    rw [abs_le] at hp
    simp only [Action.apply, signType_cast]
    cases hm : (a.workTapes i).2 with
    | zero => simp
    | pos =>
      simp only [nbL]
      by_cases hj0 : j = 0
      · simp only [hj0, ↓reduceIte, cellE, decide_eq_false_iff_not]; omega
      · simp only [hj0, ↓reduceIte, cellOf, decide_eq_decide]
        constructor <;> intro h <;> push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj0)] at h ⊢ <;>
          omega
    | neg =>
      simp only [nbR]
      by_cases hjr : j + 1 < 2 * s + 1
      · simp only [hjr, ↓reduceIte, cellOf, decide_eq_decide]
        push_cast
        constructor <;> intro h <;> omega
      · simp only [hjr, ↓reduceIte, cellE, decide_eq_false_iff_not]; omega

/-- **The boundary condition of a step is the window bound of the successor**: no head flag
leaves the region (left end under a left move, right end under a right move) iff the
successor of a window-bounded configuration is window-bounded.

**Proof sketch.** Writes happen under the heads, inside the window; a head at `p` with
`|p| ≤ s` moves to `p ± 1`, which leaves `[-s, s]` exactly at the two ends. -/
theorem boundary_iff (s : ℕ) (C : Cfg N.k Bool N.State x) (hC : InWin N s C)
    (a : Action N.k Bool N.State) (h' : Hd N) :
    (stepCell a h' (cellE N) (cellE N) (cellOf s C 0) = cellE N ∧
      stepCell a h' (cellOf s C (2 * s)) (cellE N) (cellE N) = cellE N) ↔
      InWin N s (a.apply C) := by
  have left : stepCell a h' (cellE N) (cellE N) (cellOf s C 0) = cellE N ↔
      ∀ i, (a.workTapes i).2 = .neg → C.workTapePos i ≠ -s := by
    simp only [stepCell, cellE, Option.map_none, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq,
      true_and]
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    simp only [Prod.mk.injEq, true_and]
    cases (a.workTapes i).2 <;> simp [cellOf]
  have right : stepCell a h' (cellOf s C (2 * s)) (cellE N) (cellE N) = cellE N ↔
      ∀ i, (a.workTapes i).2 = .pos → C.workTapePos i ≠ s := by
    simp only [stepCell, cellE, Option.map_none, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq,
      true_and]
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    simp only [Prod.mk.injEq, true_and]
    cases (a.workTapes i).2 <;> simp [cellOf]
    omega
  rw [left, right]
  constructor
  · rintro ⟨hl, hr⟩ i
    have hp := (hC i).1
    rw [abs_le] at hp
    refine ⟨?_, fun z hz => ?_⟩
    · simp only [Action.apply, signType_cast]
      cases hm : (a.workTapes i).2 with
      | zero => simp; rw [abs_le]; omega
      | pos => have := hr i hm; simp; rw [abs_le]; constructor <;> omega
      | neg => have := hl i hm; simp; rw [abs_le]; constructor <;> omega
    · simp only [Action.apply] at hz
      cases hw : (a.workTapes i).1 with
      | none => rw [hw] at hz; exact (hC i).2 z hz
      | some w =>
        rw [hw] at hz
        dsimp only at hz
        by_cases hzp : z = C.workTapePos i
        · rw [hzp, abs_le]; exact hp
        · rw [Function.update_of_ne hzp] at hz; exact (hC i).2 z hz
  · intro hW
    refine ⟨fun i hm hp => ?_, fun i hm hp => ?_⟩
    · have := (hW i).1
      simp only [Action.apply, signType_cast, hm, hp] at this
      rw [abs_le] at this; omega
    · have := (hW i).1
      simp only [Action.apply, signType_cast, hm, hp] at this
      rw [abs_le] at this; omega

/-- **The sliding verdict of a step**: on the cells of a window-bounded configuration `C`
and a list `v` of `2s + 1` decoded chunks, the local rule of the action `a` holds everywhere
(with empty padding) iff `v` lists the cells of `a.apply C` and `a.apply C` is
window-bounded.

**Proof sketch.** Positions `1 … 2s + 1` of the sliding relation are the cells of the
successor (`cellOf_apply`); positions `0` and `2s + 2` are the two boundary conditions
(`boundary_iff`). -/
theorem slide_step_iff (s : ℕ) (C : Cfg N.k Bool N.State x) (hC : InWin N s C)
    (a : Action N.k Bool N.State) (v : List (Option (CellV N))) (hv : v.length = 2 * s + 1) :
    (∀ i < 2 * s + 1 + 2, (some (cellE N) :: v).getD i (some (cellE N)) =
      stepG a (newHd a (hdOf C))
        ((some (cellE N) :: some (cellE N) ::
          (List.range (2 * s + 1)).map fun j => some (cellOf s C j)).getD i (some (cellE N)))
        ((some (cellE N) :: some (cellE N) ::
          (List.range (2 * s + 1)).map fun j => some (cellOf s C j)).getD (i + 1)
            (some (cellE N)))
        ((some (cellE N) :: some (cellE N) ::
          (List.range (2 * s + 1)).map fun j => some (cellOf s C j)).getD (i + 2)
            (some (cellE N)))) ↔
      (∀ j < 2 * s + 1, v.getD j (some (cellE N)) = some (cellOf s (a.apply C) j)) ∧
        InWin N s (a.apply C) := by
  have hU0 : (some (cellE N) :: some (cellE N) :: (List.range (2 * s + 1)).map
      fun j => some (cellOf s C j)).getD 0 (some (cellE N)) = some (cellE N) := rfl
  have hUC : ∀ j < 2 * s + 1, (some (cellE N) :: some (cellE N) :: (List.range (2 * s + 1)).map
      fun j => some (cellOf s C j)).getD (j + 2) (some (cellE N)) = some (cellOf s C j) := by
    intro j hj
    simp [List.getD_eq_getElem?_getD, hj]
  have hUout : ∀ t, 2 * s + 1 ≤ t → (some (cellE N) :: some (cellE N) :: (List.range (2 * s + 1)).map
      fun j => some (cellOf s C j)).getD (t + 2) (some (cellE N)) = some (cellE N) := by
    intro t ht
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl
  have hUL : ∀ j < 2 * s + 1, (some (cellE N) :: some (cellE N) :: (List.range (2 * s + 1)).map
      fun j => some (cellOf s C j)).getD (j + 1) (some (cellE N)) = some (nbL s C j) := by
    intro j hj
    rcases j with _ | j
    · rfl
    · rw [show j + 1 + 1 = j + 2 by omega, hUC j (by omega)]
      simp [nbL]
  have hUR : ∀ j < 2 * s + 1, (some (cellE N) :: some (cellE N) :: (List.range (2 * s + 1)).map
      fun j => some (cellOf s C j)).getD (j + 1 + 2) (some (cellE N)) = some (nbR s C j) := by
    intro j hj
    by_cases h1 : j + 1 < 2 * s + 1
    · rw [hUC (j + 1) h1]; simp [nbR, h1]
    · rw [hUout (j + 1) (by omega)]; simp [nbR, h1]
  have hvout : (some (cellE N) :: v).getD (2 * s + 1 + 1) (some (cellE N)) = some (cellE N) := by
    rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  rw [← boundary_iff s C hC a (newHd a (hdOf C))]
  constructor
  · intro hall
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · have := hall (j + 1) (by omega)
      rw [List.getD_cons_succ, hUL j hj, show j + 1 + 1 = j + 2 by omega, hUC j hj, hUR j hj]
        at this
      rw [this, cellOf_apply s C hC a j hj]
      rfl
    · have := hall 0 (by omega)
      rw [hU0, show 0 + 1 = 0 + 1 from rfl, hUL 0 (by omega), show 0 + 2 = 0 + 2 from rfl,
        hUC 0 (by omega)] at this
      simp only [List.getD_cons_zero, stepG, nbL, ↓reduceIte, Option.some.injEq] at this
      exact this.symm
    · have := hall (2 * s + 1 + 1) (by omega)
      rw [hvout, show 2 * s + 1 + 1 = 2 * s + 2 by omega, hUC (2 * s) (by omega),
        show 2 * s + 2 + 1 = (2 * s + 1) + 2 by omega, hUout (2 * s + 1) le_rfl,
        show 2 * s + 2 + 2 = (2 * s + 2) + 2 by omega, hUout (2 * s + 2) (by omega)] at this
      simp only [stepG, Option.some.injEq] at this
      exact this.symm
  · rintro ⟨hcells, hl, hr⟩ i hi
    by_cases h0 : i = 0
    · subst h0
      rw [hU0, hUL 0 (by omega), show 0 + 2 = 0 + 2 from rfl, hUC 0 (by omega)]
      simp only [List.getD_cons_zero, stepG, nbL, ↓reduceIte]
      rw [hl]
    by_cases hlast : i = 2 * s + 1 + 1
    · subst hlast
      rw [hvout, show 2 * s + 1 + 1 = 2 * s + 2 by omega, hUC (2 * s) (by omega),
        show 2 * s + 2 + 1 = (2 * s + 1) + 2 by omega, hUout (2 * s + 1) le_rfl,
        show 2 * s + 2 + 2 = (2 * s + 2) + 2 by omega, hUout (2 * s + 2) (by omega)]
      simp only [stepG]
      rw [hr]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j < 2 * s + 1 := by omega
    rw [List.getD_cons_succ, hcells j hj, hUL j hj, show j + 1 + 1 = j + 2 by omega, hUC j hj,
      hUR j hj, cellOf_apply s C hC a j hj]
    rfl

/-! ## The letter-level sliding scan of two chunk regions -/

variable (N) in
/-- Decoded chunks (or `none`), the letters of the sliding check. -/
abbrev SX := Option (CellV N)

variable (N) in
/-- The state of the double sliding check: one sliding state per choice bit. -/
abbrev SSt := SlSt (SX N) × SlSt (SX N)

set_option synthInstance.maxSize 1000 in
/-- Double sliding states are finitely many. -/
instance SSt.instFintype : Fintype (SSt N) := inferInstance

set_option synthInstance.maxSize 1000 in
/-- Double sliding states have decidable equality. -/
instance SSt.instDecidableEq : DecidableEq (SSt N) := inferInstance

variable (N) in
/-- The decoded chunks of a block of letter pairs, one per stream. -/
noncomputable def pairChunk (ch : List (Bool × Bool)) : SX N × SX N :=
  (decChunk N (ch.map Prod.fst), decChunk N (ch.map Prod.snd))

variable (N) in
/-- The initial sliding state: empty padding, verdict `true`. -/
def sInit : SlSt (SX N) := (some (cellE N), some (cellE N), some (cellE N), true)

variable (N) in
/-- One chunk of the double sliding check under the rules `G₀`, `G₁`. -/
noncomputable def sChunk (G₀ G₁ : SX N → SX N → SX N → SX N) (st : SSt N)
    (ch : List (Bool × Bool)) : SSt N :=
  (slStep G₀ st.1 (pairChunk N ch), slStep G₁ st.2 (pairChunk N ch))

variable (N) in
/-- **The double sliding scan** of two chunk regions `u` and `u'`, letter by letter through
the chunk adaptor, under the rules `G₀` and `G₁`. -/
noncomputable def sScan (G₀ G₁ : SX N → SX N → SX N → SX N) (u u' : List Bool) : SSt N :=
  ((List.zip u u').foldl (adStep (w := hH N + 3 * N.k) (sChunk N G₀ G₁))
    ((sInit N, sInit N), 0, fun _ => (false, false))).1

variable (N) in
/-- The verdict of a sliding state after the two padding letters. -/
def sDone (G : SX N → SX N → SX N → SX N) (st : SlSt (SX N)) : Bool :=
  (slStep G (slStep G st (some (cellE N), some (cellE N))) (some (cellE N), some (cellE N))).2.2.2

variable (N) in
/-- The decoded blocks of a chunk region with `m` blocks. -/
noncomputable def blocksD (u : List Bool) (m : ℕ) : List (SX N) :=
  (List.range m).map fun j => decChunk N (block N u j)

/-- A fold of a pair of independent steps is the pair of the folds. -/
lemma foldl_pair {α β γ : Type} (f : α → γ → α) (g : β → γ → β) (a : α) (b : β) (L : List γ) :
    L.foldl (fun st c => (f st.1 c, g st.2 c)) (a, b) = (L.foldl f a, L.foldl g b) := by
  induction L generalizing a b with
  | nil => rfl
  | cons c L ih => exact ih _ _

/-- **The letter-level double scan is the chunk-level one**: on regions of `m` blocks, each
component of `sScan` is the sliding check over the zipped decoded blocks.

**Proof sketch.** As for the validity scan: split both regions into blocks, zip block by
block (`zip_flatten`), fold block by block (`foldl_adStep_flatten`), and separate the two
independent components (`foldl_pair`). -/
theorem sScan_eq (G₀ G₁ : SX N → SX N → SX N → SX N) (u u' : List Bool) (m : ℕ)
    (hu : u.length = W N * m) (hu' : u'.length = W N * m) :
    sScan N G₀ G₁ u u' =
      ((List.zip (blocksD N u m) (blocksD N u' m)).foldl (slStep G₀) (sInit N),
        (List.zip (blocksD N u m) (blocksD N u' m)).foldl (slStep G₁) (sInit N)) := by
  have e1 := eq_flatten_blocks u (W N) m hu
  have e2 := eq_flatten_blocks u' (W N) m hu'
  set B := List.ofFn fun j : Fin m => (u.drop (W N * j)).take (W N) with hB
  set B' := List.ofFn fun j : Fin m => (u'.drop (W N * j)).take (W N) with hB'
  have hlen : ∀ (v : List Bool), v.length = W N * m → ∀ j : Fin m,
      ((v.drop (W N * j)).take (W N)).length = W N := by
    intro v hv j
    have := j.isLt
    have : W N * j + W N ≤ v.length := by rw [hv, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    simp; omega
  have hBl : ∀ j (h : j < m), B[j]'(by simp [hB, h]) = block N u j := by
    intro j h; simp [hB, block]
  have hBl' : ∀ j (h : j < m), B'[j]'(by simp [hB', h]) = block N u' j := by
    intro j h; simp [hB', block]
  have hz : List.zip u u' = (List.zipWith List.zip B B').flatten := by
    conv_lhs => rw [e1, e2]
    exact zip_flatten B B' (by simp [hB, hB']) (fun i h1 h2 => by
      simp only [hB, hB', List.getElem_ofFn]
      have hi : i < m := by simpa [hB] using h1
      rw [hlen u hu ⟨i, hi⟩, hlen u' hu' ⟨i, hi⟩])
  unfold sScan
  rw [hz]
  obtain ⟨buf, e⟩ := foldl_adStep_flatten (w := hH N + 3 * N.k) (sChunk N G₀ G₁)
    (sInit N, sInit N) (List.zipWith List.zip B B')
    (by
      intro ch hch
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hch
      have hjm : j < m := by
        have := hj; simp only [List.length_zipWith, hB, hB', List.length_ofFn, min_self] at this
        exact this
      simp only [List.getElem_zipWith, List.length_zip, hB, hB', List.getElem_ofFn]
      rw [hlen u hu ⟨j, hjm⟩, hlen u' hu' ⟨j, hjm⟩]
      simp [W])
    (fun _ => (false, false))
  rw [e]
  simp only
  have hmap : ∀ L : List (List (Bool × Bool)), L.foldl (sChunk N G₀ G₁) (sInit N, sInit N) =
      (L.map (pairChunk N)).foldl (fun st p => (slStep G₀ st.1 p, slStep G₁ st.2 p))
        (sInit N, sInit N) := by
    intro L; rw [List.foldl_map]; rfl
  have hpair : (List.zipWith List.zip B B').map (pairChunk N) =
      List.zip (blocksD N u m) (blocksD N u' m) := by
    apply List.ext_getElem (by simp [hB, hB', blocksD])
    intro i h1 h2
    have hi : i < m := by simpa [hB, hB'] using h1
    simp only [List.getElem_map, List.getElem_zipWith, List.getElem_zip, blocksD,
      List.getElem_range]
    rw [hBl i hi, hBl' i hi]
    simp only [pairChunk]
    have l1 : (block N u i).length = W N := by simpa [hB, block] using hlen u hu ⟨i, hi⟩
    have l2 : (block N u' i).length = W N := by simpa [hB', block] using hlen u' hu' ⟨i, hi⟩
    rw [List.map_fst_zip (by rw [l1, l2]), List.map_snd_zip (by rw [l1, l2])]
  rw [hmap, hpair, foldl_pair]

/-- The decoded blocks of a chunk word are its cells. -/
lemma blocksD_chunksWord (f : ℕ → CellV N) (m : ℕ) :
    blocksD N (chunksWord N f m) m = (List.range m).map fun j => some (f j) := by
  apply List.map_congr_left
  intro j hj
  rw [block_chunksWord N f m j (List.mem_range.mp hj), decChunk_encChunk]

/-- **The sliding verdict of a step on code words**: for a window-bounded `C`, the sliding
check of the chunk region of `C` against a region `A'` of the same size, with the local
rule of the action `a`, accepts iff `A'` is the chunk region of `a.apply C` and `a.apply C`
is window-bounded.

**Proof sketch.** The decoded blocks of the region of `C` are its cells
(`blocksD_chunksWord`); the verdict after the two padding letters is the sliding relation
(`slide_ok_iff`), which is `slide_step_iff`. A list of decoded blocks lists the cells of the
successor iff each block is the successor's chunk (`decChunk_encChunk`,
`encChunk_of_decChunk`), i.e. iff the region is the successor's chunk word
(`eq_flatten_blocks`). -/
theorem sDone_step (s : ℕ) (C : Cfg N.k Bool N.State x) (hC : InWin N s C)
    (a : Action N.k Bool N.State) (A' : List Bool) (hA' : A'.length = W N * (2 * s + 1)) :
    sDone N (stepG a (newHd a (hdOf C)))
        ((List.zip (blocksD N (chunksWord N (cellOf s C) (2 * s + 1)) (2 * s + 1))
          (blocksD N A' (2 * s + 1))).foldl (slStep (stepG a (newHd a (hdOf C)))) (sInit N)) =
        true ↔
      A' = chunksWord N (cellOf s (a.apply C)) (2 * s + 1) ∧ InWin N s (a.apply C) := by
  rw [blocksD_chunksWord]
  have hlen : ((List.range (2 * s + 1)).map fun j => some (cellOf s C j)).length =
      (blocksD N A' (2 * s + 1)).length := by simp [blocksD]
  have := slide_ok_iff (stepG a (newHd a (hdOf C))) (some (cellE N)) _ _ hlen
  rw [List.foldl_append] at this
  simp only [List.foldl_cons, List.foldl_nil] at this
  unfold sDone sInit
  rw [this]
  simp only [List.length_map, List.length_range]
  rw [slide_step_iff s C hC a _ (by simp [blocksD])]
  apply and_congr_left
  intro _
  constructor
  · intro hcells
    rw [eq_flatten_blocks A' (W N) (2 * s + 1) hA']
    unfold chunksWord
    congr 1
    apply List.ofFn_inj.mpr
    funext j
    have := hcells j j.isLt
    simp only [blocksD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
      j.isLt, Option.map_some, Option.getD_some] at this
    exact (encChunk_of_decChunk N this).symm
  · rintro rfl j hj
    simp [blocksD, List.getD_eq_getElem?_getD, hj, block_chunksWord N _ _ j hj]

end Complexity.Codec
