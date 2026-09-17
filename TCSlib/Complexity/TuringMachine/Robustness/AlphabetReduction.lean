/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Alphabet reduction

[AB09, Claim 1.5]: a machine over any finite alphabet `Γ` is simulated by a machine
over the binary alphabet with only a constant-factor slowdown (the constant depending
on `|Γ|`), and with the same number of work tapes. This is the theorem that justifies
defining `DTIME` over binary-alphabet machines (see
`TCSlib.Complexity.ClassP.DTIME`).

## Deviations from [AB09]

* [AB09] states the slowdown as `4 log |Γ| · T(n)`; we existentialize the constant and
  pad with `+ 1` (empty input), consistently with the rest of the development.
* [AB09]'s statement fixes input and output over `{0,1}` with only the *work* alphabet
  reduced. In our model a machine has one alphabet for all tapes, so "computing a
  binary function" for a `Γ`-machine is expressed via a symbol embedding `e : Bool ↪ Γ`
  (`Turing.FinTM.ComputesFunInTimeVia`): the simulator reads genuine binary input
  directly (its table composes with `e`), block-encodes work-tape symbols in
  `⌈log₂ |Γ|⌉` bits, and decodes each emitted symbol `e b` back to the bit `b`.
  Emitted symbols are always in the range of `e` because the append-only output equals
  the final output string, which is `(f x).map e` — early emissions included, since an
  irrevocable emission remains a prefix of the final output.
* [AB09]'s Claim 1.5 hypothesizes a time-constructible `T`; the simulation does not
  need it, so we drop the hypothesis. The statement also generalizes Boolean output to
  string output.

## Main results

* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.5, p. 16.)
-/

namespace Turing.FinTM

noncomputable section

private abbrev ArBlock (N : ℕ) := Fin (N + 1) → Option Bool

private def arCell (N : ℕ) (p : ℤ) : ℤ := p / ((N : ℤ) + 1)

private def arIndex (N : ℕ) (p : ℤ) : Fin (N + 1) :=
  ⟨(p % ((N : ℤ) + 1)).toNat, by
    have h₁ := Int.emod_nonneg p (show (N : ℤ) + 1 ≠ 0 by omega)
    have h₂ := Int.emod_lt_of_pos p (show 0 < (N : ℤ) + 1 by omega)
    omega⟩

private def arPos (N : ℕ) (z : ℤ) (j : ℕ) : ℤ := ((N : ℤ) + 1) * z + j

private lemma arCoords (N : ℕ) (z : ℤ) (j : Fin (N + 1)) :
    arCell N (arPos N z j.val) = z ∧ arIndex N (arPos N z j.val) = j := by
  have hj := j.isLt
  have h := (Int.ediv_emod_unique (show 0 < (N : ℤ) + 1 by omega)).2
    (show (j.val : ℤ) + ((N : ℤ) + 1) * z = arPos N z j.val ∧
      0 ≤ (j.val : ℤ) ∧ (j.val : ℤ) < (N : ℤ) + 1 from
      ⟨by simp [arPos, add_comm], by omega, by omega⟩)
  refine ⟨h.1, Fin.ext ?_⟩
  simp only [arIndex, h.2, Int.toNat_natCast]

private lemma arPos_coords (N : ℕ) (p : ℤ) :
    arPos N (arCell N p) (arIndex N p).val = p := by
  have h := Int.emod_nonneg p (show (N : ℤ) + 1 ≠ 0 by omega)
  simp only [arPos, arCell, arIndex, Int.toNat_of_nonneg h]
  exact Int.mul_ediv_add_emod p ((N : ℤ) + 1)

private lemma arPos_eq {N : ℕ} (z z' : ℤ) (j j' : Fin (N + 1)) :
    arPos N z j.val = arPos N z' j'.val ↔ z = z' ∧ j = j' := by
  constructor
  · intro h
    have h₁ := congrArg (arCell N) h
    have h₂ := congrArg (arIndex N) h
    rw [(arCoords N z j).1, (arCoords N z' j').1] at h₁
    rw [(arCoords N z j).2, (arCoords N z' j').2] at h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

private def arTape {N : ℕ} (F : ℤ → ArBlock N) (p : ℤ) : Option Bool :=
  F (arCell N p) (arIndex N p)

private lemma arTape_at {N : ℕ} (F : ℤ → ArBlock N) (z : ℤ) (j : Fin (N + 1)) :
    arTape F (arPos N z j.val) = F z j := by
  simp only [arTape, (arCoords N z j).1, (arCoords N z j).2]

private lemma arTape_ext {N : ℕ} (u v : ℤ → Option Bool)
    (h : ∀ z (j : Fin (N + 1)), u (arPos N z j.val) = v (arPos N z j.val)) : u = v := by
  funext p
  simpa only [arPos_coords] using h (arCell N p) (arIndex N p)

private lemma arTape_update {N : ℕ} (F : ℤ → ArBlock N) (z : ℤ)
    (j : Fin (N + 1)) (b : Option Bool) :
    Function.update (arTape F) (arPos N z j.val) b =
      arTape (fun z' j' => if z' = z ∧ j' = j then b else F z' j') := by
  apply arTape_ext (N := N)
  intro z' j'
  simp only [Function.update_apply, arTape_at, arPos_eq]

/-- A fixed-width one-hot code for nonblank symbols, with an all-blank code for
logical blank. Testing the position assigned to a symbol proves injectivity. -/
private def arCode {Γ : Type} [Fintype Γ] : Option Γ ↪ ArBlock (Fintype.card Γ) where
  toFun a j := a.map fun x => decide (j.val = (Fintype.equivFin Γ x).val)
  inj' := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => have := congrFun h 0; simp at this
    | some a =>
      cases b with
      | none => have := congrFun h 0; simp at this
      | some b =>
        have ha := (Fintype.equivFin Γ a).isLt
        have h₁ := congrFun h ⟨(Fintype.equivFin Γ a).val, by omega⟩
        have h₂ : (Fintype.equivFin Γ a).val = (Fintype.equivFin Γ b).val := by simpa using h₁
        exact congrArg some ((Fintype.equivFin Γ).injective (Fin.ext h₂))

private def arDecode {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N) :
    ArBlock N → Option Γ := Function.invFun E

private lemma arDecode_code {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N) (a : Option Γ) :
    arDecode E (E a) = a := Function.leftInverse_invFun E.injective a

private def arBit {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (a : Γ) : Bool :=
  decide (a = e true)

private lemma arBit_embed {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) :
    arBit e (e b) = b := by
  cases b <;> simp [arBit, e.injective.eq_iff]

private abbrev ArPending (Γ S : Type) (k : ℕ) :=
  Option S × (Fin k → Option Γ) × (Fin k → SignType)

private abbrev ArState (Γ S : Type) (k N : ℕ) :=
  (S × Fin (N + 2) × (Fin k → ArBlock N)) ⊕
    (ArPending Γ S k × (Fin (N + 1) ⊕ Fin (N + 2)))

private def arReady {Γ S : Type} {k N : ℕ} (q : S) : ArState Γ S k N :=
  .inl (q, 0, fun _ _ => none)

private def arPending {Γ S : Type} {k : ℕ} (read : Fin k → Option Γ)
    (a : Action k Γ S) : ArPending Γ S k :=
  (a.state, fun i => (a.workTapes i).1.getD (read i), fun i => (a.workTapes i).2)

/-- A block cycle reads right, writes left, and then moves a whole block in each
source direction. Even with zero work tapes the finite controller performs the same
positive number of steps. Input motion and the possible emission occur only once,
at the transition between reading and writing. -/
private def arTM {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) : FinTM Bool where
  k := M.k
  State := ArState Γ M.State M.k N
  decEqState := Classical.decEq _
  tm :=
    { q₀ := arReady M.tm.q₀
      tr := fun q inp work => match q with
        | .inl (q, j, buf) =>
          if h : j.val < N + 1 then
            ⟨0, fun _ => (none, .pos), none,
              some (.inl (q, ⟨j.val + 1, by omega⟩,
                fun i => Function.update (buf i) ⟨j.val, h⟩ (work i)))⟩
          else
            let a := M.tm.tr q (inp.map e) (fun i => arDecode E (buf i))
            ⟨a.inputTape, fun _ => (none, .neg), a.output.map (arBit e),
              some (.inr (arPending (fun i => arDecode E (buf i)) a, .inl ⟨N, by omega⟩))⟩
        | .inr (a, .inl j) =>
          if h : j.val = 0 then
            ⟨0, fun i => (some (E (a.2.1 i) j), 0), none,
              some (.inr (a, .inr ⟨N + 1, by omega⟩))⟩
          else
            ⟨0, fun i => (some (E (a.2.1 i) j), .neg), none,
              some (.inr (a, .inl ⟨j.val - 1, by omega⟩))⟩
        | .inr (a, .inr r) =>
          if h : r.val = 0 then
            ⟨0, fun _ => (none, 0), none, a.1.map arReady⟩
          else
            ⟨0, fun i => (none, a.2.2 i), none,
              some (.inr (a, .inr ⟨r.val - 1, by omega⟩))⟩ }

/-- Canonical macro-boundary representation. Output is mapped through the total
bit decoder; under the computation premise `arEmission_in_image` additionally shows
that every emission is in the bit embedding's image, so its default case is unused. -/
private def arCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e)) :
    Cfg k Bool (ArState Γ S k N) x where
  state := c.state.map arReady
  inputPos := ⟨c.inputPos.val, by simpa only [List.length_map] using c.inputPos.isLt⟩
  workTapes i := arTape (fun z => E (c.workTapes i z))
  workTapePos i := arPos N (c.workTapePos i) 0
  output := c.output.map (arBit e)

private lemma arCfg_input {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e)) :
    (arCfg E e c).inputSymbol.map e = c.inputSymbol := by
  unfold Cfg.inputSymbol
  simp only [arCfg, List.length_map, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> simp_all

private def arBuffer {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) (j : ℕ) : Fin k → ArBlock N :=
  fun i b => if b.val < j then E (read i) b else none

private lemma arBuffer_zero {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) : arBuffer E read 0 = fun _ _ => none := by
  funext i b
  simp [arBuffer]

private lemma arBuffer_full {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) : arBuffer E read (N + 1) = fun i => E (read i) := by
  funext i b
  simp only [arBuffer, if_pos b.isLt]

private lemma arBuffer_update {Γ : Type} {k N : ℕ} (E : Option Γ ↪ ArBlock N)
    (read : Fin k → Option Γ) (j : Fin (N + 1)) :
    (fun i => Function.update (arBuffer E read j.val i) j (E (read i) j)) =
      arBuffer E read (j.val + 1) := by
  funext i b
  by_cases h : b = j
  · subst b
    simp [arBuffer]
  · have hv : b.val ≠ j.val := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h, arBuffer]
    split_ifs <;> first | rfl | omega

private def arReadCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (j : Fin (N + 2)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e c with
    state := some (.inl (q, j, arBuffer E c.workTapeSymbols j.val))
    workTapePos := fun i => arPos N (c.workTapePos i) j.val }

private lemma arReadCfg_zero {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (hc : c.state = some q) : arReadCfg E e c q 0 = arCfg E e c := by
  simp [arReadCfg, arCfg, hc, arReady, arBuffer_zero]

private lemma arReadCfg_symbols {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (q : S) (j : Fin (N + 2)) (hj : j.val < N + 1) :
    (arReadCfg E e c q j).workTapeSymbols = fun i => E (c.workTapeSymbols i) ⟨j.val, hj⟩ := by
  funext i
  exact arTape_at (fun z => E (c.workTapes i z)) (c.workTapePos i) ⟨j.val, hj⟩

private lemma arReadCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State)
    (j : Fin (N + 2)) (hj : j.val < N + 1) :
    (arTM E e M).tm.step (arReadCfg E e c q j) =
      arReadCfg E e c q ⟨j.val + 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : j.val < N + 1 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_pos hj]
  rw [arReadCfg_symbols E e c q j hj]
  refine Cfg.ext ?_ ?_ rfl ?_ ?_
  · have hb := arBuffer_update E c.workTapeSymbols ⟨j.val, hj⟩
    dsimp only at hb
    simp only [Action.apply, arReadCfg, hb]
  · simp [arReadCfg, arCfg, Action.apply]
  · funext i
    simp [arReadCfg, arPos, Action.apply, SignType.cast]
    omega
  · simp [arReadCfg, arCfg, Action.apply]

private lemma arReadCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State) (hc : c.state = some q) :
    ∀ j (hj : j ≤ N + 1), (arTM E e M).tm.runFrom (arCfg E e c) j =
      arReadCfg E e c q ⟨j, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; exact (arReadCfg_zero E e c q hc).symm
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact arReadCfg_step E e M c q ⟨j, by omega⟩ (by dsimp only; omega)

private def arTail {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) (r : ℕ) : ℤ → ArBlock N :=
  fun z j => if z = p ∧ r ≤ j.val then E w j else E (t z) j

private lemma arTail_full {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) :
    arTail E t p w (N + 1) = fun z => E (t z) := by
  funext z j
  have := j.isLt
  simp [arTail, show ¬N + 1 ≤ j.val by omega]

private lemma arTail_zero {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) :
    arTail E t p w 0 = fun z => E (Function.update t p w z) := by
  funext z j
  simp only [arTail, Nat.zero_le, and_true, Function.update_apply]
  split <;> rfl

/-- One leftward write extends the completed suffix by one bit. Distinct blocks
remain unchanged; within this block the only new index is the written index. -/
private lemma arTail_update {Γ : Type} {N : ℕ} (E : Option Γ ↪ ArBlock N)
    (t : ℤ → Option Γ) (p : ℤ) (w : Option Γ) (j : Fin (N + 1)) :
    Function.update (arTape (arTail E t p w (j.val + 1))) (arPos N p j.val) (E w j) =
      arTape (arTail E t p w j.val) := by
  apply arTape_ext (N := N)
  intro z b
  simp only [Function.update_apply, arTape_at, arPos_eq, arTail]
  by_cases hz : z = p
  · subst z
    by_cases hj : b = j
    · subst b; simp
    · have hv : b.val ≠ j.val := fun h => hj (Fin.ext h)
      simp only [true_and, hj, and_false, if_false]
      split_ifs <;> first | rfl | omega
  · simp [hz]

private lemma arUpdated_tape {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (a : Action k Γ S) (i : Fin k) :
    (a.apply c).workTapes i = Function.update (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) := by
  cases hw : (a.workTapes i).1 with
  | none => simp [Action.apply, hw, Cfg.workTapeSymbols]
  | some w => simp [Action.apply, hw]

private def arMoveCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (a : Action k Γ S) (r : Fin (N + 2)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e (a.apply c) with
    state := some (.inr (arPending c.workTapeSymbols a, .inr r))
    workTapePos := fun i => arPos N (c.workTapePos i) 0 +
      (((N : ℤ) + 1) - r.val) * ((a.workTapes i).2 : ℤ) }

private def arWriteCfg {Γ S : Type} [DecidableEq Γ] {k N : ℕ} {x : List Bool}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (c : Cfg k Γ S (x.map e))
    (a : Action k Γ S) (j : Fin (N + 1)) : Cfg k Bool (ArState Γ S k N) x :=
  { arCfg E e (a.apply c) with
    state := some (.inr (arPending c.workTapeSymbols a, .inl j))
    workTapes := fun i => arTape (arTail E (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) (j.val + 1))
    workTapePos := fun i => arPos N (c.workTapePos i) j.val }

private lemma arMoveCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State)
    (r : Fin (N + 2)) (hr : r.val ≠ 0) :
    (arTM E e M).tm.step (arMoveCfg E e c a r) =
      arMoveCfg E e c a ⟨r.val - 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : r.val = 0 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_neg hr]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [arMoveCfg, arCfg, Action.apply]
  · funext i
    have hcast : ((r.val - 1 : ℕ) : ℤ) = (r.val : ℤ) - 1 := by omega
    simp only [Action.apply, arMoveCfg, arPending, hcast]
    ring
  · simp [arMoveCfg, arCfg, Action.apply]

private lemma arMoveCfg_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    (arTM E e M).tm.step (arMoveCfg E e c a 0) = arCfg E e (a.apply c) := by
  unfold MultiTapeTM.step
  dsimp only [arMoveCfg, arTM, arPending]
  rw [dif_pos (show (0 : Fin (N + 2)).val = 0 from rfl)]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · simp [arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arCfg, arPos, Fin.val_zero, SignType.coe_zero]
    ring
  · simp [arCfg, Action.apply]

private lemma arMoveCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    ∀ r (hr : r ≤ N + 1), (arTM E e M).tm.runFrom (arMoveCfg E e c a ⟨r, by omega⟩)
      (r + 1) = arCfg E e (a.apply c) := by
  intro r
  induction r with
  | zero => intro hr; exact arMoveCfg_finish E e M c a
  | succ r ih =>
    intro hr
    rw [MultiTapeTM.runFrom_succ_eq_step, arMoveCfg_step E e M c a ⟨r + 1, by omega⟩ (by simp)]
    exact ih (by omega)

private lemma arWriteCfg_step {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State)
    (j : Fin (N + 1)) (hj : j.val ≠ 0) :
    (arTM E e M).tm.step (arWriteCfg E e c a j) =
      arWriteCfg E e c a ⟨j.val - 1, by omega⟩ := by
  unfold MultiTapeTM.step
  change ((if h : j.val = 0 then _ else _) : Action M.k Bool (ArState Γ M.State M.k N)).apply _ = _
  rw [dif_neg hj]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [arWriteCfg, arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arWriteCfg, arPending]
    rw [arTail_update]
    congr 2
    omega
  · funext i
    simp [Action.apply, arWriteCfg, arPos, SignType.cast]
    omega
  · simp [arWriteCfg, arCfg, Action.apply]

private lemma arWriteCfg_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    (arTM E e M).tm.step (arWriteCfg E e c a 0) =
      arMoveCfg E e c a ⟨N + 1, by omega⟩ := by
  unfold MultiTapeTM.step
  dsimp only [arWriteCfg, arTM, arPending]
  rw [dif_pos (show (0 : Fin (N + 1)).val = 0 from rfl)]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [arMoveCfg, arCfg, Action.apply]
  · funext i
    simp only [Action.apply, arMoveCfg, arCfg, arPending]
    rw [arTail_update]
    simp only [Fin.val_zero, arTail_zero]
    change arTape (fun z => E (Function.update (c.workTapes i) (c.workTapePos i)
      ((a.workTapes i).1.getD (c.workTapeSymbols i)) z)) =
      arTape (fun z => E ((a.apply c).workTapes i z))
    rw [arUpdated_tape]
  · funext i
    simp [arMoveCfg, arPos, Action.apply]
  · simp [arMoveCfg, arCfg, Action.apply]

private lemma arWriteCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (a : Action M.k Γ M.State) :
    ∀ j (hj : j ≤ N), (arTM E e M).tm.runFrom (arWriteCfg E e c a ⟨j, by omega⟩)
      (j + 1) = arMoveCfg E e c a ⟨N + 1, by omega⟩ := by
  intro j
  induction j with
  | zero => intro hj; exact arWriteCfg_finish E e M c a
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, arWriteCfg_step E e M c a ⟨j + 1, by omega⟩ (by simp)]
    exact ih (by omega)

/-- At the end of the read sweep, decoding recovers all scanned source symbols.
Execute the source input move and emission, save its pending work update in finite
control, and move left to the last bit of each block to start the write sweep. -/
private lemma arReadCfg_dispatch {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (q : M.State) :
    (arTM E e M).tm.step (arReadCfg E e c q ⟨N + 1, by omega⟩) =
      arWriteCfg E e c (M.tm.tr q c.inputSymbol c.workTapeSymbols) ⟨N, by omega⟩ := by
  unfold MultiTapeTM.step
  dsimp only [arReadCfg, arTM]
  rw [dif_neg (show ¬N + 1 < N + 1 by omega)]
  simp only [arBuffer_full, arDecode_code]
  have hi : (arReadCfg E e c q ⟨N + 1, by omega⟩).inputSymbol.map e =
      c.inputSymbol := arCfg_input E e c
  simp only [arReadCfg, arBuffer_full] at hi
  rw [hi]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · apply Fin.ext
    simp [arWriteCfg, arCfg, Action.apply, moveInputPos]
    split <;> rfl
  · funext i
    simp only [Action.apply, arWriteCfg, arCfg, arTail_full]
  · funext i
    simp [arWriteCfg, arPos, Action.apply, SignType.cast]
    omega
  · simp [arWriteCfg, arCfg, Action.apply, List.map_append, Option.toList_map]

/-- Three sweeps plus two control transitions simulate one source step. Once the
source has halted, both represented configurations are absorbing. -/
private lemma arCfg_cycle {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) :
    (arTM E e M).tm.runFrom (arCfg E e c) (3 * (N + 1) + 2) =
      arCfg E e (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs,
      MultiTapeTM.runFrom_of_halt _ (show (arCfg E e c).state = none by simp [arCfg, hs])]
  | some q =>
    rw [show 3 * (N + 1) + 2 = (N + 1) + (1 + ((N + 1) + ((N + 1) + 1))) by omega,
      MultiTapeTM.runFrom_add, arReadCfg_run E e M c q hs (N + 1) (le_refl _)]
    rw [MultiTapeTM.runFrom_add]
    change (arTM E e M).tm.runFrom
      ((arTM E e M).tm.step (arReadCfg E e c q ⟨N + 1, by omega⟩)) _ = _
    rw [arReadCfg_dispatch, MultiTapeTM.runFrom_add,
      arWriteCfg_run E e M c _ N (le_refl _), arMoveCfg_run E e M c _ (N + 1) (le_refl _)]
    simp only [MultiTapeTM.step, hs]

private lemma arCfg_run {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (e : Bool ↪ Γ) (M : FinTM Γ) {x : List Bool}
    (c : Cfg M.k Γ M.State (x.map e)) (t : ℕ) :
    (arTM E e M).tm.runFrom (arCfg E e c) ((3 * (N + 1) + 2) * t) =
      arCfg E e (M.tm.runFrom c t) := by
  induction t with
  | zero => simp only [Nat.mul_zero, MultiTapeTM.runFrom_zero]
  | succ t ih =>
    rw [Nat.mul_succ, MultiTapeTM.runFrom_add, ih, arCfg_cycle,
      MultiTapeTM.runFrom_succ_eq_step']

private lemma arCfg_init {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (hE : E none = fun _ => none)
    (e : Bool ↪ Γ) (M : FinTM Γ) (x : List Bool) :
    (arTM E e M).tm.initCfg x = arCfg E e (M.tm.initCfg (x.map e)) := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp [arCfg]
  · funext i p
    simp only [MultiTapeTM.initCfg, Cfg.init, arCfg, arTape, hE]
  · funext i
    simp [arCfg, arPos]

/-- The output decoder is total, with `false` for every non-image symbol. In the
computation invariant those cases are unreachable: an emitted source symbol remains
in the append-only output, which is a prefix of the completed embedded output. -/
private lemma arEmission_in_image {Γ : Type} [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) (x : List Bool) (t : ℕ) (a : Γ)
    (ha : M.tm.outputSymbol (M.tm.runFrom (M.tm.initCfg (x.map e)) t) = some a) :
    ∃ b, e b = a := by
  obtain ⟨hs, ho⟩ := (computesInTime_iff M _ _ _).1 (hM x)
  by_cases ht : t < T x.length
  · have hp := M.tm.output_prefix (M.tm.initCfg (x.map e)) (show t + 1 ≤ T x.length by omega)
    rw [ho] at hp
    have hm : a ∈ (M.tm.runFrom (M.tm.initCfg (x.map e)) (t + 1)).output := by
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, ha]
      simp
    obtain ⟨b, _, hb⟩ := List.mem_map.1 (hp.sublist.subset hm)
    exact ⟨b, hb⟩
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show T x.length ≤ t by omega)
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs,
      MultiTapeTM.outputSymbol_of_halt hs] at ha
    cases ha

private lemma arTM_computes {Γ : Type} [Fintype Γ] [DecidableEq Γ] {N : ℕ}
    (E : Option Γ ↪ ArBlock N) (hE : E none = fun _ => none)
    (e : Bool ↪ Γ) (M : FinTM Γ) (x : List Bool) (w : List Bool) (t : ℕ)
    (h : M.ComputesInTime (x.map e) (w.map e) t) :
    (arTM E e M).ComputesInTime x w ((3 * (N + 1) + 2) * t) := by
  rw [computesInTime_iff, arCfg_init E hE, arCfg_run]
  obtain ⟨hs, ho⟩ := (computesInTime_iff M _ _ _).1 h
  simp only [arCfg, hs, ho, Option.map_none, true_and, List.map_map]
  simp only [Function.comp_def, arBit_embed]
  exact List.map_id w

/-- **Alphabet reduction** [AB09, Claim 1.5]: if a machine over a finite alphabet `Γ`
computes the binary string function `f` via `e : Bool ↪ Γ` within time `T`, then a
binary-alphabet machine with the *same number of work tapes* computes `f` within
`c · (T n + 1)` for some constant `c` (depending on the original machine).

**Proof sketch.** Fix a binary block code of length `L = ⌈log₂ |Γ|⌉` for `Option Γ`'s
non-blank symbols. `M'` keeps each of `M`'s work tapes as a block-encoded tape. One
step of `M` is simulated by: reading the `L` bits under each work head into the state
(`L` steps per tape, walking right), reading the input bit directly (its `e`-image is
determined by the table), computing `M`'s transition inside the finite state, writing
back the `L`-bit codes while returning left (`L` steps per tape), moving each head `L`
cells in the simulated direction, and emitting the decoded bit whenever `M` emits.
Total: at most `c` steps of `M'` per step of `M` with `c = O((k + 1) · L)` — the
`+ 1` covering the input-read, state-update, and emission work that remains even for
`k = 0` — plus a constant start-up. Logical blank is represented by the all-blank (`none`-cell) block — never-
visited blocks already have this shape, so no binary code needs reserving and no
initialization pass is required (phase-2 audit, finding 8). The invariant
relating block-encoded configurations to `M`'s configurations is preserved by each
simulated step, and `M`'s halting transfers.

**Implementation note (epoch 2, batch C).** As permitted by the brief's arbitrary
fixed-width scheme, the implementation uses a one-hot binary code of width
`L = Fintype.card Γ + 1` for nonblank symbols; logical blank remains all-`none`.
The proof factors through any injective code of positive width with this blank
property. All work tapes are swept simultaneously: `L` reads, one dispatch,
`L` writes, `L` moves, and one final control transition, for exactly `3 * L + 2`
steps per live source step. This also covers zero work tapes. The input is never
block-encoded. `arEmission_in_image` formalizes the output-prefix argument, while
the run correspondence maps the entire output through a total decoder. -/
theorem alphabet_reduction {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : FinTM Γ) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTimeVia e f T) :
    ∃ (c : ℕ) (M' : FinTM Bool), M'.k = M.k ∧
      M'.ComputesFunInTime f fun n => c * (T n + 1) := by
  let E := arCode (Γ := Γ)
  have hE : E none = fun _ => none := rfl
  refine ⟨3 * (Fintype.card Γ + 1) + 2, arTM E e M, rfl, ?_⟩
  intro x
  exact (arTM_computes E hE e M x (f x) (T x.length) (hM x)).mono
    (Nat.mul_le_mul_left _ (Nat.le_succ _))

end

end Turing.FinTM
