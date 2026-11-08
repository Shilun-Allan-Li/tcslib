/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Frag

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Input shapes and the plain format check

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Parse`: the input shapes
`⟨1ⁿ, w⟩` and `⟨1ⁿ, ⟨u, w⟩⟩`, input-scanning configurations, the input rewind, and the
format check of plain inputs `⟨1ⁿ, w⟩`.

## Main definitions

* `Complexity.LogProg.ValidPlain`, `Complexity.LogProg.ValidPair` — the input shapes.
* `Complexity.LogProg.xCfg` — a configuration with the input head and one register head
  moved.

## Main results

* `Complexity.LogProg.rewind_x` — the input rewind.
* `Complexity.LogProg.validPlain_iff` — the plain format, read off the leading run.
* `Complexity.LogProg.valPlain_run` — the plain format check.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: logspace machines read their input in place.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-! ## Input shapes -/

/-- The input is `⟨1ⁿ, w⟩` with `w` without trailing `0`. -/
def ValidPlain (y : List Bool) : Prop :=
  ∃ n w, y = pairEncode (List.replicate n true) w ∧ Canon w

/-- The input is `⟨1ⁿ, ⟨u, w⟩⟩` with `u`, `w` without trailing `0`. -/
def ValidPair (y : List Bool) : Prop :=
  ∃ n u w, y = pairEncode (List.replicate n true) (pairEncode u w) ∧ Canon u ∧ Canon w

/-- Doubling `1ⁿ` gives `1²ⁿ`. -/
lemma dbl_replicate (n : ℕ) : dbl (List.replicate n true) = List.replicate (2 * n) true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, Nat.mul_succ]

/-! ## Configurations -/

/-- A configuration with state `s`, input head `ip`, and the head of register `r` at `p`
(tapes as in `c`). -/
def xCfg (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ) :
    Cfg m Bool Λ x :=
  ⟨some s, ip, c.workTapes, Function.update c.workTapePos r p, c.output⟩

/-- The input-scanning view `xCfg c s …` is in state `s`. -/
@[simp] lemma xCfg_state (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m)
    (p : ℤ) : (xCfg c s ip r p).state = some s := rfl

/-- An action moving the input head and the head of register `r`. -/
def xAct (r : Fin m) (mvI mvR : SignType) (s : Λ) : Action m Bool Λ :=
  ⟨mvI, fun r' => if r' = r then (none, mvR) else (none, 0), none, some s⟩

/-- Reject: write `0` and halt. -/
def rejAct : Action m Bool Λ := ⟨0, fun _ => (none, 0), some false, none⟩

/-- Applying an input-scanning action moves the input head by `mvI`, the register head by
`mvR`, and enters `s'`. -/
lemma apply_xAct (c : Cfg m Bool Λ x) (s s' : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ)
    (mvI mvR : SignType) :
    (xAct r mvI mvR s').apply (xCfg c s ip r p) = xCfg c s' (moveInputPos ip mvI) r (p + mvR) := by
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [xAct, xCfg])
  · funext r' z
    simp only [xAct, xCfg, Action.apply]
    split_ifs <;> rfl
  · funext r'
    simp only [xAct, xCfg, Action.apply]
    by_cases h : r' = r
    · subst h; simp
    · simp [h]

/-- The input-scanning view reads register `r` at its head position `p`. -/
lemma xCfg_read (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ) :
    (xCfg c s ip r p).workTapeSymbols r = c.workTapes r p := by
  simp [xCfg, Cfg.workTapeSymbols]

/-- The input symbol at input position `q` (`0` and `|x| + 1` are the blanks). -/
def inSym (x : List Bool) (q : ℕ) : Option Bool := if q = 0 then none else x[q - 1]?

/-- The input-scanning view reads the input symbol at its input head position. -/
lemma xCfg_inSym (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ) :
    (xCfg c s ip r p).inputSymbol = inSym x ip.val := by
  rw [inputSymbol_eq]; rfl

section Run

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool)

/-- One step of the program from an input-scanning view at a non-call state is the
transition's action applied to it. -/
lemma rrun_one_x (c : Cfg m Bool Λ x) (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ)
    (hs : P.call s = none) :
    rrun P oracle (xCfg c s ip r p) 1 =
      (P.tm.tr s (inSym x ip.val) (xCfg c s ip r p).workTapeSymbols).apply (xCfg c s ip r p) := by
  rw [rrun_one, rstep_noncall P oracle _ s rfl hs, ← xCfg_inSym c s ip r p]
  unfold MultiTapeTM.step
  rfl

/-- The input head moves by one inside the tape. -/
lemma moveInputPos_pos_val (ip : Fin (x.length + 2)) (h : ip.val ≤ x.length) :
    (moveInputPos ip 1).val = ip.val + 1 := by
  rw [moveInputPos_val]; simp; omega

/-- Moving the input head left decrements its position (truncated at `0`). -/
lemma moveInputPos_neg_val' (ip : Fin (x.length + 2)) :
    (moveInputPos ip (-1)).val = ip.val - 1 := by
  rw [moveInputPos_val]

/-- **A right scan of the input** through a family of states `st j`: for `k` steps the state
`st j` reads the input at position `q₀ + j` and moves right into `st (j + 1)`, leaving the
registers alone. -/
lemma scanR (c : Cfg m Bool Λ x) (r : Fin m) (p : ℤ) (st : ℕ → Λ) (q₀ k : ℕ)
    (hk : q₀ + k ≤ x.length + 1)
    (htr : ∀ j < k, ∀ w, P.tm.tr (st j) (inSym x (q₀ + j)) w = xAct r 1 0 (st (j + 1)))
    (hc : ∀ j < k, P.call (st j) = none) :
    ∀ (j : ℕ) (hj : j ≤ k), rrun P oracle (xCfg c (st 0) ⟨q₀, by omega⟩ r p) j =
      xCfg c (st j) ⟨q₀ + j, by omega⟩ r p := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [rrun_succ, ih (by omega), ← rrun_one, rrun_one_x P oracle c _ _ r p (hc j (by omega))]
    simp only
    rw [htr j (by omega), apply_xAct]
    congr 1
    · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    · simp

/-- **The input rewind**: from `rw₁` one unconditional left move into `rw₂`, which moves left
over input symbols and, at the left blank, steps onto position `1` into `nx`.

**Proof sketch.** After the first left move, induction on the input head position: on an input
letter the head moves left, and at the left blank (position `0`) it moves right onto position
`1` and the state becomes `nx`. The register head never moves. -/
lemma rewind_x (c : Cfg m Bool Λ x) (r : Fin m) (p : ℤ) (rw₁ rw₂ nx : Λ)
    (h₁ : ∀ a w, P.tm.tr rw₁ a w = xAct r (-1) 0 rw₂)
    (h₂ : ∀ a w, P.tm.tr rw₂ a w = match a with
      | some _ => xAct r (-1) 0 rw₂
      | none => xAct r 1 0 nx)
    (h₁c : P.call rw₁ = none) (h₂c : P.call rw₂ = none) (ip : Fin (x.length + 2)) :
    ∃ T, rrun P oracle (xCfg c rw₁ ip r p) T = xCfg c nx ⟨1, by omega⟩ r p ∧
      ∀ t < T, ∃ s ip', rrun P oracle (xCfg c rw₁ ip r p) t = xCfg c s ip' r p ∧
        P.call s = none := by
  -- the scan phase, by induction on the position
  have scan : ∀ (j : ℕ) (ip' : Fin (x.length + 2)), ip'.val = j → j ≤ x.length →
      rrun P oracle (xCfg c rw₂ ip' r p) (j + 1) = xCfg c nx ⟨1, by omega⟩ r p ∧
      ∀ t < j + 1, ∃ ip'', rrun P oracle (xCfg c rw₂ ip' r p) t = xCfg c rw₂ ip'' r p := by
    intro j
    induction j with
    | zero =>
      intro ip' hip _
      refine ⟨?_, fun t ht => ⟨ip', by obtain rfl : t = 0 := by omega
                                       rfl⟩⟩
      rw [rrun_one_x P oracle c rw₂ ip' r p h₂c, h₂]
      have : inSym x ip'.val = none := by simp [inSym, hip]
      rw [this]
      simp only
      rw [apply_xAct]
      congr 1
      · exact Fin.ext (by rw [moveInputPos_pos_val ip' (by omega)]; show ip'.val + 1 = 1; omega)
      · simp
    | succ j ih =>
      intro ip' hip hj
      have hsym : inSym x ip'.val = some x[j] := by
        simp [inSym, hip, List.getElem?_eq_getElem (show j < x.length by omega)]
      have hstep : rrun P oracle (xCfg c rw₂ ip' r p) 1 =
          xCfg c rw₂ (moveInputPos ip' (-1)) r p := by
        rw [rrun_one_x P oracle c rw₂ ip' r p h₂c, h₂, hsym]
        simp only
        rw [apply_xAct]; simp
      obtain ⟨ihr, ihm⟩ := ih (moveInputPos ip' (-1)) (by rw [moveInputPos_neg_val']; omega)
        (by omega)
      refine ⟨by rw [rrun_succ_left, hstep, ihr], fun t ht => ?_⟩
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨ip', rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        exact ihm t' (by omega)
  have hstep : rrun P oracle (xCfg c rw₁ ip r p) 1 = xCfg c rw₂ (moveInputPos ip (-1)) r p := by
    rw [rrun_one_x P oracle c rw₁ ip r p h₁c, h₁, apply_xAct]; simp
  obtain ⟨hr, hm⟩ := scan (moveInputPos ip (-1)).val (moveInputPos ip (-1)) rfl
    (by rw [moveInputPos_neg_val']; have := ip.isLt; omega)
  refine ⟨1 + ((moveInputPos ip (-1)).val + 1), by rw [rrun_add, hstep, hr], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t 1 with h | h
  · obtain rfl : t = 0 := by omega
    exact ⟨rw₁, ip, rfl, h₁c⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, hstep]
    obtain ⟨ip'', h⟩ := hm t' (by omega)
    exact ⟨rw₂, ip'', h, h₂c⟩

end Run

/-! ## The plain format check -/

/-- The leading run of `1`s of `x`. -/
def tRun (x : List Bool) : ℕ := (x.takeWhile (· = true)).length

/-- The leading run of `1`s is no longer than the word. -/
lemma tRun_le (x : List Bool) : tRun x ≤ x.length := (List.takeWhile_prefix _).length_le

/-- The letters before the end of the leading run of `1`s are `1`s. -/
lemma getElem?_lt_tRun (x : List Bool) (j : ℕ) (hj : j < tRun x) : x[j]? = some true :=
  takeWhile_true_getElem? x j hj

/-- The letter ending the leading run of `1`s (if any) is not a `1`. -/
lemma getElem?_tRun (x : List Bool) : x[tRun x]? ≠ some true := takeWhile_true_end x

/-- The plain format, read off the leading run: an even run of `1`s, then `0 1`, then a word
without trailing `0`.

**Proof sketch.** (⇒) On `pairEncode 1ⁿ w` the leading run is `1²ⁿ` (`dbl_replicate`), followed
by `0 1 w`. (⇐) Split the word at its leading run of even length `2n` and at the following `0
1`: the prefix is `dbl 1ⁿ`, so the word is `⟨1ⁿ, rest⟩` with `rest` without trailing `0`. -/
lemma validPlain_iff (y : List Bool) :
    ValidPlain y ↔ tRun y % 2 = 0 ∧ y[tRun y]? = some false ∧ y[tRun y + 1]? = some true ∧
      Canon (y.drop (tRun y + 2)) := by
  constructor
  · rintro ⟨n, w, rfl, hw⟩
    have ht : tRun (pairEncode (List.replicate n true) w) = 2 * n := by
      simp only [tRun, pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
      rw [List.takeWhile_append_of_pos (by simp)]
      simp
    rw [ht]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simp [pairEncode_eq_dbl, dbl_replicate]
    · simp [pairEncode_eq_dbl, dbl_replicate]
    · simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append, hw]
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨tRun y / 2, y.drop (tRun y + 2), ?_, h3⟩
    have htake : y.take (tRun y) = List.replicate (tRun y) true := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < tRun y
      · rw [List.getElem?_take, if_pos hi, getElem?_lt_tRun y i hi]; simp [hi]
      · rw [List.getElem?_take, if_neg hi]; simp [hi]
    have hlen : tRun y + 2 ≤ y.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at h2; simp at h2
    have hsplit : y = y.take (tRun y) ++ [false, true] ++ y.drop (tRun y + 2) := by
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_append, List.getElem?_append]
      by_cases ha : i < tRun y
      · simp [ha, List.length_take, show tRun y ≤ y.length from tRun_le y,
          show i < tRun y + 2 by omega, List.getElem?_eq_getElem (show i < y.length by omega)]
      · by_cases hb : i < tRun y + 2
        · have : i = tRun y ∨ i = tRun y + 1 := by omega
          rcases this with rfl | rfl
          · simp [h1, show tRun y ≤ y.length from tRun_le y]
          · simp [h2, show tRun y ≤ y.length from tRun_le y]
        · simp [hb, show tRun y ≤ y.length from tRun_le y, List.getElem?_drop]
          congr 1; omega
    rw [pairEncode_eq_dbl, dbl_replicate, show 2 * (tRun y / 2) = tRun y by omega, ← htake]
    exact hsplit

/-- The run of `1`s: count parity. -/
def valUAct (r : Fin m) (vU0 vU1 vS : Λ) (par : Bool) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 (if par then vU0 else vU1)
  | some false => if par then rejAct else xAct r 1 0 vS
  | none => rejAct

/-- The `1` of the separator. -/
def valSAct (r : Fin m) (vW0 : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 vW0
  | _ => rejAct

/-- The final word: remember the last bit; at the end reject a trailing `0`, else rewind. -/
def valWAct (r : Fin m) (vWF vWT rw₁ : Λ) (last : Option Bool) (a : Option Bool) :
    Action m Bool Λ :=
  match a with
  | some b => xAct r 1 0 (if b then vWT else vWF)
  | none => if last = some false then rejAct else xAct r 0 0 rw₁

/-- The input symbol at cell `j + 1` is the `j`-th letter of the input (cell `0` is the left
end marker). -/
lemma inSym_succ (x : List Bool) (j : ℕ) : inSym x (j + 1) = x[j]? := by simp [inSym]

/-- **The rejecting step**: from an input-scanning view at a non-call state whose transition on the
current input symbol is `rejAct`, one step halts with output `0` appended and the register head
where it was.

**Proof sketch.** Rewrite the one-step run with `rrun_one_x` and the transition with `htr`;
`rejAct` writes `false` to the output, moves no head and halts. Compare the components of the
resulting configuration. -/
lemma rrun_one_rej (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (s : Λ) (ip : Fin (x.length + 2)) (r : Fin m) (p : ℤ) (hs : P.call s = none)
    (htr : ∀ w, P.tm.tr s (inSym x ip.val) w = rejAct) :
    (rrun P oracle (xCfg c s ip r p) 1).state = none ∧
      (rrun P oracle (xCfg c s ip r p) 1).output = c.output ++ [false] ∧
      (rrun P oracle (xCfg c s ip r p) 1).workTapePos = Function.update c.workTapePos r p := by
  rw [rrun_one_x P oracle c s ip r p hs, htr]
  simp [rejAct, Action.apply, xCfg]

section ValPlain

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (vU0 vU1 vS vW0 vWF vWT rw₁ rw₂ next : Λ)
  (hU0 : ∀ a w, P.tm.tr vU0 a w = valUAct r vU0 vU1 vS false a)
  (hU1 : ∀ a w, P.tm.tr vU1 a w = valUAct r vU0 vU1 vS true a)
  (hS : ∀ a w, P.tm.tr vS a w = valSAct r vW0 a)
  (hW0 : ∀ a w, P.tm.tr vW0 a w = valWAct r vWF vWT rw₁ none a)
  (hWF : ∀ a w, P.tm.tr vWF a w = valWAct r vWF vWT rw₁ (some false) a)
  (hWT : ∀ a w, P.tm.tr vWT a w = valWAct r vWF vWT rw₁ (some true) a)
  (h₁ : ∀ a w, P.tm.tr rw₁ a w = xAct r (-1) 0 rw₂)
  (h₂ : ∀ a w, P.tm.tr rw₂ a w = match a with
    | some _ => xAct r (-1) 0 rw₂
    | none => xAct r 1 0 next)
  (cU0 : P.call vU0 = none) (cU1 : P.call vU1 = none) (cS : P.call vS = none)
  (cW0 : P.call vW0 = none) (cWF : P.call vWF = none) (cWT : P.call vWT = none)
  (c₁ : P.call rw₁ = none) (c₂ : P.call rw₂ = none)

/-- The outcome of a fragment run: either it reaches `next` with the input head on position
`1`, or it rejects; on the way only non-call states, the registers' heads unchanged. -/
def FragOK (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x) (s₀ : Λ)
    (r : Fin m) (p : ℤ) (good : Prop) (next : Λ) : Prop :=
  (good → ∃ T, rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) T = xCfg c next ⟨1, by omega⟩ r p ∧
      ∀ t < T, ∃ s ip, rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) t = xCfg c s ip r p ∧
        P.call s = none) ∧
  (¬ good → ∃ T, (rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) T).state = none ∧
      (rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) T).output = c.output ++ [false] ∧
      (rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) T).workTapePos =
        Function.update c.workTapePos r p ∧
      ∀ t < T, ∃ s ip, rrun P oracle (xCfg c s₀ ⟨1, by omega⟩ r p) t = xCfg c s ip r p ∧
        P.call s = none)

include hU0 hU1 hS hW0 hWF hWT h₁ h₂ cU0 cU1 cS cW0 cWF cWT c₁ c₂ in
/-- **The plain format check**: it reaches `next` (input head back on position `1`) exactly
on inputs `⟨1ⁿ, w⟩` with `w` free of trailing `0`s, and rejects otherwise.

**Proof sketch.** The run of `1`s is scanned with its parity (`scanR`); then the separator
`0 1`; then the final word with its last bit (`scanR`); finally `rewind_x`. Every failure
rejects in one step. `validPlain_iff` identifies acceptance with the shape. -/
lemma valPlain_run (c : Cfg m Bool Λ x) (p : ℤ) :
    FragOK P oracle c vU0 r p (ValidPlain x) next := by
  set t := tRun x with ht
  have htx : t ≤ x.length := tRun_le x
  -- the run of `1`s
  let st : ℕ → Λ := fun j => if j % 2 = 0 then vU0 else vU1
  have hscan := scanR P oracle c r p st 1 t (by omega) (fun j hj w => by
      rw [show 1 + j = j + 1 by ring, inSym_succ, getElem?_lt_tRun x j hj]
      simp only [st]
      split_ifs with h1 h2 h2
      · omega
      · rw [hU0]; simp [valUAct]
      · rw [hU1]; simp [valUAct]
      · omega)
    (fun j hj => by simp only [st]; split_ifs <;> assumption)
  have hs0 : st 0 = vU0 := rfl
  have hst : ∀ j, P.call (st j) = none := fun j => by simp only [st]; split_ifs <;> assumption
  have hmidU : ∀ j ≤ t, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) j = xCfg c s ip r p ∧
      P.call s = none := fun j hj => ⟨st j, _, by rw [← hs0]; exact hscan j hj, hst j⟩
  have hU : rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) t = xCfg c (st t) ⟨1 + t, by omega⟩ r p :=
    by rw [← hs0]; exact hscan t le_rfl
  have hsym1 : inSym x (1 + t) = x[t]? := by rw [show 1 + t = t + 1 by ring, inSym_succ]
  -- a rejecting continuation
  have rejAt : ∀ (T₀ : ℕ) (s : Λ) (ip : Fin (x.length + 2)), P.call s = none →
      (∀ w, P.tm.tr s (inSym x ip.val) w = rejAct) →
      rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) T₀ = xCfg c s ip r p →
      (∀ t' < T₀, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) t' = xCfg c s ip r p ∧
        P.call s = none) →
      ∃ T, (rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) T).state = none ∧
        (rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) T).output = c.output ++ [false] ∧
        (rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) T).workTapePos =
          Function.update c.workTapePos r p ∧
        ∀ t < T, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) t = xCfg c s ip r p ∧
          P.call s = none := by
    intro T₀ s ip hs htr hrun hmid
    obtain ⟨e1, e2, e3⟩ := rrun_one_rej P oracle c s ip r p hs htr
    refine ⟨T₀ + 1, by rw [rrun_add, hrun]; exact e1, by rw [rrun_add, hrun]; exact e2,
      by rw [rrun_add, hrun]; exact e3, fun t' ht' => ?_⟩
    rcases Nat.lt_or_ge t' T₀ with h | h
    · exact hmid t' h
    · obtain rfl : t' = T₀ := by omega
      exact ⟨s, ip, hrun, hs⟩
  have hvalid := validPlain_iff x
  rw [← ht] at hvalid
  have hnotT := getElem?_tRun x
  rw [← ht] at hnotT
  -- the symbol after the run
  rcases hxt : x[t]? with _ | b
  · -- end of input: reject
    have hbad : ¬ ValidPlain x := by rw [hvalid, hxt]; simp
    refine ⟨fun h => absurd h hbad, fun _ => rejAt t (st t) _ (hst t) (fun w => ?_) hU
      (fun t' ht' => hmidU t' ht'.le)⟩
    rw [hsym1, hxt]
    simp only [st]; split_ifs
    · rw [hU0]; rfl
    · rw [hU1]; rfl
  cases b with
  | true => exact absurd hxt hnotT
  | false =>
  have htlt : t < x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt; simp at hxt
  by_cases hpar : t % 2 = 0
  swap
  · -- odd run: reject
    have hbad : ¬ ValidPlain x := by rw [hvalid]; omega
    refine ⟨fun h => absurd h hbad, fun _ => rejAt t (st t) _ (hst t) (fun w => ?_) hU
      (fun t' ht' => hmidU t' ht'.le)⟩
    rw [hsym1, hxt]
    simp only [st, hpar, ↓reduceIte]
    rw [hU1]; rfl
  -- even run: the separator
  have hS1 : rrun P oracle (xCfg c (st t) ⟨1 + t, by omega⟩ r p) 1 =
      xCfg c vS ⟨2 + t, by omega⟩ r p := by
    rw [rrun_one_x P oracle c _ _ r p (hst t)]
    simp only [st, hpar, ↓reduceIte]
    rw [hU0, hsym1, hxt]
    simp only [valUAct, Bool.false_eq_true, ↓reduceIte]
    rw [apply_xAct]
    congr 1
    · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    · simp
  have hsym2 : inSym x (2 + t) = x[t + 1]? := by rw [show 2 + t = (t + 1) + 1 by ring, inSym_succ]
  have hmidS : ∀ j ≤ t + 1, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) j =
      xCfg c s ip r p ∧ P.call s = none := by
    intro j hj
    rcases Nat.lt_or_ge j (t + 1) with h | h
    · exact hmidU j (by omega)
    · obtain rfl : j = t + 1 := by omega
      exact ⟨vS, _, by rw [rrun_add, hU, hS1], cS⟩
  have hSrun : rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (t + 1) =
      xCfg c vS ⟨2 + t, by omega⟩ r p := by rw [rrun_add, hU, hS1]
  rcases hxt1 : x[t + 1]? with _ | b'
  · have hbad : ¬ ValidPlain x := by rw [hvalid, hxt1]; simp
    refine ⟨fun h => absurd h hbad, fun _ => rejAt (t + 1) vS _ cS (fun w => ?_) hSrun
      (fun t' ht' => hmidS t' ht'.le)⟩
    rw [hsym2, hxt1, hS]; rfl
  cases b' with
  | false =>
    have hbad : ¬ ValidPlain x := by rw [hvalid, hxt1]; simp
    refine ⟨fun h => absurd h hbad, fun _ => rejAt (t + 1) vS _ cS (fun w => ?_) hSrun
      (fun t' ht' => hmidS t' ht'.le)⟩
    rw [hsym2, hxt1, hS]; rfl
  | true =>
  have htlt1 : t + 1 < x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt1; simp at hxt1
  have hS2 : rrun P oracle (xCfg c vS ⟨2 + t, by omega⟩ r p) 1 =
      xCfg c vW0 ⟨3 + t, by omega⟩ r p := by
    have hlen : t + 2 ≤ x.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt1; simp at hxt1
    rw [rrun_one_x P oracle c _ _ r p cS, hS, hsym2, hxt1]
    simp only [valSAct]
    rw [apply_xAct]
    congr 1
    · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
    · simp
  -- the final word
  set w := x.drop (t + 2) with hw
  have hwlen : w.length + t + 2 = x.length := by
    have : t + 2 ≤ x.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt1; simp at hxt1
    simp [hw]; omega
  let st' : ℕ → Λ := fun j => match (w.take j).getLast? with
    | none => vW0
    | some false => vWF
    | some true => vWT
  have htake_last : ∀ (j : ℕ) (hj : j < w.length), (w.take (j + 1)).getLast? = some w[j] := by
    intro j hj
    have h : List.take (j + 1) w = List.take j w ++ [w[j]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hj]; rfl
    rw [h, List.getLast?_append]
    simp
  have hst'c : ∀ j, P.call (st' j) = none := by
    intro j; simp only [st']; split <;> assumption
  have hscanW := scanR P oracle c r p st' (3 + t) w.length (by omega) (fun j hj ww => by
      rw [show 3 + t + j = (t + 2 + j) + 1 by ring, inSym_succ]
      have hx : x[t + 2 + j]? = some w[j] := by
        rw [← List.getElem?_eq_getElem hj, hw, List.getElem?_drop]
      rw [hx]
      have e : st' (j + 1) = if w[j] then vWT else vWF := by
        simp only [st', htake_last j hj]; cases w[j] <;> rfl
      rw [e]
      simp only [st']
      split
      · rw [hW0]; rfl
      · rw [hWF]; rfl
      · rw [hWT]; rfl)
    (fun j hj => hst'c j)
  have hs'0 : st' 0 = vW0 := by simp [st']
  have hWrun : rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (t + 1 + 1 + w.length) =
      xCfg c (st' w.length) ⟨3 + t + w.length, by omega⟩ r p := by
    rw [rrun_add, rrun_add, hSrun, hS2, ← hs'0]
    exact hscanW w.length le_rfl
  have hmidW : ∀ j ≤ t + 1 + 1 + w.length, ∃ s ip, rrun P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) j =
      xCfg c s ip r p ∧ P.call s = none := by
    intro j hj
    rcases Nat.lt_or_ge j (t + 1 + 1) with h | h
    · exact hmidS j (by omega)
    · obtain ⟨j', rfl⟩ : ∃ j', j = t + 1 + 1 + j' := ⟨j - (t + 2), by omega⟩
      refine ⟨st' j', ⟨3 + t + j', by omega⟩, ?_, hst'c j'⟩
      rw [rrun_add, rrun_add, hSrun, hS2, ← hs'0]
      exact hscanW j' (by omega)
  have hlast : (w.take w.length).getLast? = w.getLast? := by rw [List.take_length]
  have hendSym : inSym x (3 + t + w.length) = none := by
    rw [show 3 + t + w.length = x.length + 1 by omega, inSym_succ]; simp
  by_cases hcan : w.getLast? = some false
  · -- trailing zero: reject
    have hbad : ¬ ValidPlain x := by
      rw [hvalid]; rintro ⟨-, -, -, h3⟩
      have hne : w ≠ [] := by rintro h; rw [h] at hcan; simp at hcan
      have := h3 hne
      rw [List.getLast?_eq_getLast hne] at hcan
      simp [this] at hcan
    refine ⟨fun h => absurd h hbad, fun _ => rejAt _ (st' w.length) _ (hst'c _) (fun ww => ?_)
      hWrun (fun t' ht' => hmidW t' ht'.le)⟩
    rw [hendSym]
    simp only [st', hlast, hcan]
    rw [hWF]; simp [valWAct]
  · have hgood : ValidPlain x := by
      rw [hvalid]
      refine ⟨hpar, hxt, hxt1, fun hne => ?_⟩
      have := List.getLast?_eq_getLast hne
      cases h : w.getLast hne
      · rw [h] at this; exact absurd this hcan
      · rfl
    refine ⟨fun _ => ?_, fun h => absurd hgood h⟩
    have hE : rrun P oracle (xCfg c (st' w.length) ⟨3 + t + w.length, by omega⟩ r p) 1 =
        xCfg c rw₁ ⟨3 + t + w.length, by omega⟩ r p := by
      rw [rrun_one_x P oracle c _ _ r p (hst'c _), hendSym]
      have e : ∀ ww, P.tm.tr (st' w.length) none ww = xAct r 0 0 rw₁ := by
        intro ww
        simp only [st', hlast]
        split
        · rw [hW0]; rfl
        · rename_i h; rw [h] at hcan; exact absurd rfl hcan
        · rw [hWT]; rfl
      rw [e, apply_xAct]
      simp
    obtain ⟨T₄, hr4, hm4⟩ := rewind_x P oracle c r p rw₁ rw₂ next h₁ h₂ c₁ c₂
      ⟨3 + t + w.length, by omega⟩
    refine ⟨t + 1 + 1 + w.length + 1 + T₄, by rw [rrun_add, rrun_add, hWrun, hE, hr4],
      fun t' ht' => ?_⟩
    rcases Nat.lt_or_ge t' (t + 1 + 1 + w.length + 1) with h | h
    · rcases Nat.lt_or_ge t' (t + 1 + 1 + w.length) with h' | h'
      · exact hmidW t' h'.le
      · obtain rfl : t' = t + 1 + 1 + w.length := by omega
        exact hmidW _ le_rfl
    · obtain ⟨t'', rfl⟩ : ∃ t'', t' = t + 1 + 1 + w.length + 1 + t'' :=
        ⟨t' - (t + 1 + 1 + w.length + 1), by omega⟩
      rw [rrun_add, rrun_add, hWrun, hE]
      exact hm4 t'' (by omega)

end ValPlain

end Complexity.LogProg
