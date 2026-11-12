/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.Formulas.QBFEncoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The pure side of the `TQBF` register machine

The facts about quantified formulas that the polynomial-width register machine deciding
`TQBF` (`TCSlib.Complexity.ClassPSPACE.TQBFARM.Walk`) relies on, stated without machines.

* **Syntax.** The finite automaton `Complexity.LogProg.TQBFARM.synStep` (an aligned-pair
  stage followed by the six-state grammar automaton `Std.Sat.CNF.syntaxStep`) accepts exactly
  the encodings `pairEncode qs (CNF.serialize φ)` (`synOK_spec`, `repr_of_synOK`); every other
  string decodes to a true formula (`truth_of_not_synOK`), the fallback convention of
  `Complexity.QBF.decode`.
* **Stack semantics.** The machine keeps the partial assignment of the quantifier prefix as a
  binary stack `S` (a leading `1`, then one bit per bound variable, the innermost lowest);
  `Complexity.LogProg.TQBFARM.asg k S` is the assignment it denotes at depth `k`, and
  `Complexity.LogProg.TQBFARM.Val qs φ k S` the truth value of the remaining formula.
  Pushing a bit is an update of the assignment (`asg_push`), so `Val` obeys the AND/OR
  recursion of [AB09, §4.2, proof of Theorem 4.13] (`val_leaf`, `val_ex`, `val_all`) and is
  the truth of the decoded formula at the root (`val_root`).

Infrastructure for [AB09, §4.2, Theorem 4.13, membership half]; not itself a result of the
book.

## Main definitions

* `Complexity.LogProg.TQBFARM.synStep`, `Complexity.LogProg.TQBFARM.synOK` — the syntax
  automaton and its verdict.
* `Complexity.LogProg.TQBFARM.asg`, `Complexity.LogProg.TQBFARM.Val` — the stack semantics.

## Main results

* `Complexity.LogProg.TQBFARM.truth_of_not_synOK`, `Complexity.LogProg.TQBFARM.repr_of_synOK`.
* `Complexity.LogProg.TQBFARM.val_leaf`, `val_ex`, `val_all`, `val_root`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13.)
-/

namespace Complexity.LogProg.TQBFARM

open Std.Sat (CNF)
open Turing

/-! ## Syntax -/

/-- The states of the syntax automaton: during the aligned-pair stage, no bit or the first bit
of a pair (`inl`); after the separator, a state of the grammar automaton (`inr`). -/
abbrev SynSt := Option Bool ⊕ Fin 6

/-- **The syntax automaton**: equal aligned pairs are prefix bits, `01` is the separator into
the grammar automaton `Std.Sat.CNF.syntaxStep`, and `10` enters its error state. -/
def synStep : SynSt → Bool → SynSt
  | .inl none, b => .inl (some b)
  | .inl (some false), false => .inl none
  | .inl (some false), true => .inr 0
  | .inl (some true), true => .inl none
  | .inl (some true), false => .inr 5
  | .inr q, b => .inr (CNF.syntaxStep q b)

/-- The syntax verdict: the automaton ends in the grammar's exact-end state `4`. -/
def synOK (x : List Bool) : Bool :=
  decide (x.foldl synStep (.inl none) = .inr 4)

/-- After the separator the automaton is the grammar automaton. -/
theorem synStep_matrix (x : List Bool) (q : Fin 6) :
    x.foldl synStep (.inr q) = .inr (x.foldl CNF.syntaxStep q) := by
  induction x generalizing q with
  | nil => rfl
  | cons b x ih => exact ih (CNF.syntaxStep q b)

/-- **The syntax automaton accepts exactly a successful pair decoding followed by a successful
matrix parse.**

**Proof sketch.** Follow the recursion of `Turing.pairDecode` two bits at a time: equal pairs
return to the pair stage, `01` hands the rest to the grammar automaton
(`Std.Sat.CNF.syntaxOK_spec`), and `10` or an incomplete pair never reaches state `4`
(`Std.Sat.CNF.syntaxSuffix_run` from the error state). -/
theorem synOK_spec (x : List Bool) :
    synOK x = match pairDecode x with
      | none => false
      | some (_, m) => (CNF.parse m).isSome := by
  induction x using pairDecode.induct with
  | case1 xs ih =>
      change synOK xs = _
      rw [ih]
      cases hp : pairDecode xs <;> simp [pairDecode, hp]
  | case2 xs ih =>
      change synOK xs = _
      rw [ih]
      cases hp : pairDecode xs <;> simp [pairDecode, hp]
  | case3 xs =>
      simp only [synOK, List.foldl_cons, synStep, synStep_matrix, Sum.inr.injEq, pairDecode]
      exact CNF.syntaxOK_spec xs
  | case4 xs h00 h11 h01 =>
      rcases xs with _ | ⟨b, _ | ⟨c, r⟩⟩
      · rfl
      · cases b <;> rfl
      · cases b <;> cases c
        · exact False.elim (h00 r rfl)
        · exact False.elim (h01 r rfl)
        · have herr : r.foldl CNF.syntaxStep 5 ≠ 4 := by
            intro hc
            exact (CNF.syntaxSuffix_run 5 r).mpr hc
          simpa [synOK, synStep, synStep_matrix, pairDecode] using herr
        · exact False.elim (h11 r rfl)

/-- The empty matrix is true under every prefix. -/
theorem truthAux_nil (qs : List QBF.Quant) (σ : ℕ → Bool) (i : ℕ) :
    QBF.truthAux [] qs σ i := by
  induction qs generalizing σ i with
  | nil => rfl
  | cons q qs ih =>
      cases q with
      | ex => exact ⟨false, ih _ _⟩
      | all => exact fun b => ih (Function.update σ i b) (i + 1)

/-- **Rejected strings are true formulas**: a string failing the syntax check decodes to a
fallback with the empty (true) matrix. -/
theorem truth_of_not_synOK {x : List Bool} (h : synOK x = false) : (QBF.decode x).truth := by
  cases hp : pairDecode x with
  | none =>
      simpa [QBF.decode, hp, QBF.truth, CNF.fallback] using truthAux_nil [] (fun _ => false) 0
  | some p =>
      obtain ⟨qs, m⟩ := p
      have hm : CNF.parse m = none := by
        cases he : CNF.parse m with
        | none => rfl
        | some φ => simp [synOK_spec, hp, he] at h
      simpa [QBF.decode, hp, QBF.truth, CNF.decode, hm, CNF.fallback] using
        truthAux_nil (qs.map QBF.quantOfBit) (fun _ => false) 0

/-- **Accepted strings are encodings**: a string passing the syntax check is
`pairEncode qs (CNF.serialize φ)`. -/
theorem repr_of_synOK {x : List Bool} (h : synOK x = true) :
    ∃ (qs : List Bool) (φ : CNF ℕ), x = pairEncode qs (CNF.serialize φ) := by
  rw [synOK_spec] at h
  cases hp : pairDecode x with
  | none => simp [hp] at h
  | some p =>
      obtain ⟨qs, y⟩ := p
      cases hm : CNF.parse y with
      | none => simp [hp, hm] at h
      | some φ =>
          exact ⟨qs, φ, (eq_pairEncode_of_pairDecode x qs y hp).trans
            (congrArg (pairEncode qs) (CNF.parse_repr hm))⟩

/-- The decoding of an encoding: prefix bits read as quantifiers, the matrix recovered. -/
theorem decode_pairEncode (qs : List Bool) (φ : CNF ℕ) :
    QBF.decode (pairEncode qs (CNF.serialize φ)) = ⟨qs.map QBF.quantOfBit, φ⟩ := by
  simp [QBF.decode, pairDecode_pairEncode, CNF.decode_serialize]

/-! ## Stack semantics -/

/-- **The assignment of a stack** `S` at depth `k`: variable `v < k` reads bit `k - 1 - v` of
`S` (the innermost variable is the lowest bit), every other variable reads `false`. -/
def asg (k S : ℕ) : ℕ → Bool :=
  fun v => decide (v < k) && decide (S / 2 ^ (k - 1 - v) % 2 = 1)

/-- At depth `0` every variable reads `false`. -/
theorem asg_zero (S : ℕ) : asg 0 S = fun _ => false := by
  funext v; simp [asg]

/-- **Pushing a bit is an update**: binding variable `k` to `b` in the assignment of `S` at
depth `k` gives the assignment of `2S + b` at depth `k + 1`.

**Proof sketch.** Below `k`, `(2S + b) / 2 ^ (j + 1) = S / 2 ^ j`; at `k` the new lowest bit
is `b`; above, both sides read `false`. -/
theorem asg_push (k S : ℕ) (b : Bool) :
    Function.update (asg k S) k b = asg (k + 1) (2 * S + b.toNat) := by
  funext v
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  rcases lt_trichotomy v k with h | rfl | h
  · rw [Function.update_of_ne h.ne]
    simp only [asg]
    have e : k + 1 - 1 - v = (k - 1 - v) + 1 := by omega
    rw [e, pow_succ', ← Nat.div_div_eq_div_mul, show (2 * S + b.toNat) / 2 = S by omega]
    simp [h, show v < k + 1 by omega]
  · rw [Function.update_self]
    simp only [asg, show v + 1 - 1 - v = 0 by omega, pow_zero, Nat.div_one]
    cases b <;> simp [Nat.mul_mod_right, Nat.add_mod]
  · rw [Function.update_of_ne h.ne']
    simp [asg, show ¬ v < k by omega, show ¬ v < k + 1 by omega]

/-- **The value of a stack**: the truth of the matrix `φ` under the quantifiers of the prefix
bits `qs` from position `k` on, starting from the assignment of `S` at depth `k`. -/
def Val (qs : List Bool) (φ : CNF ℕ) (k S : ℕ) : Prop :=
  QBF.truthAux φ ((qs.drop k).map QBF.quantOfBit) (asg k S) k

/-- At the full depth the value is the matrix's value. -/
theorem val_leaf (qs : List Bool) (φ : CNF ℕ) (S : ℕ) :
    Val qs φ qs.length S ↔ φ.eval (asg qs.length S) = true := by
  simp [Val, QBF.truthAux]

/-- The prefix bits from position `k < |qs|` on. -/
private theorem drop_map_eq (qs : List Bool) (k : ℕ) (hk : k < qs.length) :
    (qs.drop k).map QBF.quantOfBit =
      QBF.quantOfBit qs[k] :: (qs.drop (k + 1)).map QBF.quantOfBit := by
  rw [List.drop_eq_getElem_cons hk, List.map_cons]

/-- **An existential level**: the value is the disjunction of the two pushes. -/
theorem val_ex (qs : List Bool) (φ : CNF ℕ) (k S : ℕ) (hk : k < qs.length)
    (hq : qs[k] = true) :
    Val qs φ k S ↔ Val qs φ (k + 1) (2 * S) ∨ Val qs φ (k + 1) (2 * S + 1) := by
  unfold Val
  rw [drop_map_eq qs k hk, hq]
  simp only [QBF.quantOfBit, if_true, QBF.truthAux, asg_push]
  constructor
  · rintro ⟨b, hb⟩; cases b
    · left; simpa using hb
    · right; simpa using hb
  · rintro (h | h)
    · exact ⟨false, by simpa using h⟩
    · exact ⟨true, by simpa using h⟩

/-- **A universal level**: the value is the conjunction of the two pushes. -/
theorem val_all (qs : List Bool) (φ : CNF ℕ) (k S : ℕ) (hk : k < qs.length)
    (hq : qs[k] = false) :
    Val qs φ k S ↔ Val qs φ (k + 1) (2 * S) ∧ Val qs φ (k + 1) (2 * S + 1) := by
  unfold Val
  rw [drop_map_eq qs k hk, hq]
  simp only [QBF.quantOfBit, Bool.false_eq_true, if_false, QBF.truthAux, asg_push]
  constructor
  · intro h; exact ⟨by simpa using h false, by simpa using h true⟩
  · rintro ⟨h0, h1⟩ b; cases b
    · simpa using h0
    · simpa using h1

/-- **The root**: the value of the stack `1` at depth `0` is the truth of the encoded formula. -/
theorem val_root (qs : List Bool) (φ : CNF ℕ) :
    Val qs φ 0 1 ↔ (QBF.decode (pairEncode qs (CNF.serialize φ))).truth := by
  rw [decode_pairEncode]
  simp [Val, QBF.truth, asg_zero]

end Complexity.LogProg.TQBFARM
