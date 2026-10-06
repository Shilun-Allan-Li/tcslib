/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time pairing, projections and branching

Closure facts for the function class FP (`Complexity.PolyTimeComputable`, implicit
throughout [AB09, ch. 2]) needed when a reduction must keep its input while computing
from it: constant functions, the threaded payload map, pairing of two polynomial-time
functions through `Turing.pairEncode`, the total pair projections, concatenation,
Boolean branching and length tests, and the unary length maps `x ↦ 1^|x|` and
`x ↦ 1^{C(|x|+1)^d}` (the input of a uniformity machine, [AB09, Def 6.12]). All are
assembled from the proved machine catalog of
`TCSlib.Complexity.TuringMachine.Build.Primitives`. The closure facts for the class `P`
built on them are in `TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.pairMapSnd` — on `pairEncode a b`, output `pairEncode a (g b)`; malformed
  words go to `[]`.
* `Complexity.pairFstD`, `Complexity.pairSndD` — total pair projections (`[]` on
  malformed words).

## Main results

* `Complexity.polyTimeComputable_of_linear` — a linear-time machine contract gives a
  polynomial-time computable function.
* `Complexity.polyTimeComputable_const` — constant functions are polynomial-time.
* `Complexity.PolyTimeComputable.pairMapSnd` — the threaded payload map preserves
  polynomial time.
* `Complexity.PolyTimeComputable.pairEncode` — `x ↦ pairEncode (f x) (g x)` is
  polynomial-time when `f` and `g` are.
* `Complexity.polyTimeComputable_unary` — `x ↦ 1^|x|` is polynomial-time;
  `Complexity.polyTimeComputable_polyUnary` — so is `x ↦ 1^{C(|x|+1)^d}`.
* `Complexity.PolyTimeComputable.append` — FP is closed under concatenation.
* `Complexity.polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`,
  `polyTimeComputable_pairSwap`, `polyTimeComputable_pairConcat`,
  `polyTimeComputable_prepend` — projections and rearrangements of pairs.
* `Complexity.polyTimeComputable_ite`, `polyTimeComputable_and` — Boolean branching.
* `Complexity.polyTimeComputable_lenLe`, `polyTimeComputable_lenEq` — length tests on
  pairs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Ch. 2; §6.2, Definition 6.12.)
-/

namespace Complexity

open Turing

/-- A function computed by a finite binary machine within a linear bound `a · (n + 1)`
is polynomial-time computable. -/
theorem polyTimeComputable_of_linear {f : List Bool → List Bool}
    (h : ∃ (M : FinTM Bool) (a : ℕ), M.ComputesFunInTime f (fun n => a * (n + 1))) :
    PolyTimeComputable f := by
  obtain ⟨M, a, hM⟩ := h
  exact ⟨M, a, 1, by simpa only [Nat.pow_one] using hM⟩

/-- Every constant function `fun _ => w` is polynomial-time computable. -/
theorem polyTimeComputable_const (w : List Bool) : PolyTimeComputable (fun _ => w) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_const w)

/-- The threaded payload map of `g`: on a pair `pairEncode a b` it outputs
`pairEncode a (g b)` (the first component is carried unchanged), and on a word that is
not a pair it outputs `[]`. -/
def pairMapSnd (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, b) => pairEncode a (g b)
  | none => []

/-- On a pair, the threaded payload map transforms the second component. -/
@[simp]
theorem pairMapSnd_pairEncode (g : List Bool → List Bool) (a b : List Bool) :
    pairMapSnd g (pairEncode a b) = pairEncode a (g b) := by
  simp [pairMapSnd, pairDecode_pairEncode]

/-- If `g` is polynomial-time computable, so is its threaded payload map
`Complexity.pairMapSnd g`.

**Proof sketch.** `Turing.FinTM.computesFunInTime_pairMapSnd` with the monotone
majorant `C (n+1)^c` of `g`'s bound gives a budget `K (n + 1 + C (n+1)^c)`, which is at
most `K (C + 1) (n+1)^(c+1)`. -/
theorem PolyTimeComputable.pairMapSnd {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (Complexity.pairMapSnd g) := by
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_pairMapSnd hG
    (by
      intro m n h
      exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) c))
  refine ⟨M, K * (C + 1), c + 1, fun x => (hM x).mono ?_⟩
  have hn : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ c + 1 by omega)
  have hc := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (Nat.le_succ c))
  calc
    _ ≤ K * ((x.length + 1) ^ (c + 1) + C * (x.length + 1) ^ (c + 1)) :=
      Nat.mul_le_mul_left K (Nat.add_le_add hn hc)
    _ = _ := by ring

/-- Appending to a pair appends to its second component. -/
private lemma pairEncode_append (a b c : List Bool) :
    pairEncode a b ++ c = pairEncode a (b ++ c) := by
  simp [pairEncode, List.append_assoc]

/-- **Pairing two polynomial-time functions is polynomial-time**: if `f` and `g` are
polynomial-time computable, so is `x ↦ pairEncode (f x) (g x)`.

**Proof sketch.** Only the second component of a pair can be transformed in place
(`Complexity.pairMapSnd`), so the first component is built with an empty payload and
then retained. Duplicating `x` (`Turing.FinTM.computesFunInTime_pairDup`) and mapping
the payload gives `H x = pairEncode (f x) []`; duplicating `x` and mapping `H` gives
`s x = pairEncode x (H x)`; duplicating `s x` and mapping `g ∘ fst` gives
`t x = pairEncode (s x) (g x)`. Concatenating the components of `t x`
(`Turing.FinTM.computesFunInTime_pairConcat`) yields
`pairEncode x (pairEncode (f x) (g x))`, whose second component is the result. -/
theorem PolyTimeComputable.pairEncode {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => Turing.pairEncode (f x) (g x)) := by
  have hd := polyTimeComputable_of_linear FinTM.computesFunInTime_pairDup
  have hp := polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  -- `H x = pairEncode (f x) []`, `s x = pairEncode x (H x)`, `t x = pairEncode (s x) (g x)`
  have hH := (((polyTimeComputable_const []).pairMapSnd).comp hd).comp hf
  have hS := hH.pairMapSnd.comp hd
  have hT := ((hg.comp hp).pairMapSnd.comp hd).comp hS
  -- concatenate, then project the second component
  have h := hs.comp (hc.comp hT)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairMapSnd_pairEncode, pairDecode_pairEncode,
    Option.map_some, Option.getD_some]
  rw [pairEncode_append, pairEncode_append]
  simp [pairDecode_pairEncode]

/-- The last `true` of `1^(n+1)` is its last letter: stripping it leaves `1ⁿ`. -/
private lemma splitAtLastTrue_replicate_succ (n : ℕ) :
    splitAtLastTrue (List.replicate (n + 1) true) = some (List.replicate n true) := by
  rw [splitAtLastTrue, List.reverse_replicate, List.replicate_succ]
  simp [List.reverse_replicate]

/-- **The unary length map is polynomial-time**: `x ↦ 1^|x|` is polynomial-time
computable. (This is how the input `1ⁿ` of a uniformity machine [AB09, Def 6.12] is
produced from an input of length `n`.)

**Proof sketch.** Pair `x` with `1^(|x|+1)` (the unary polynomial generator at
`1 · (n + 1)¹`, `Turing.FinTM.computesFunInTime_polyUnary`), strip the last `true` of the
second component (`Turing.FinTM.computesFunInTime_stripLast`), and project the second
component (`Turing.FinTM.computesFunInTime_pairSnd`). -/
theorem polyTimeComputable_unary :
    PolyTimeComputable (fun x => List.replicate x.length true) := by
  have hu : PolyTimeComputable (fun x => List.replicate (1 * (x.length + 1) ^ 1) true) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_polyUnary 1 1
    exact ⟨M, c, 2, hM⟩
  have hpair := polyTimeComputable_id.pairEncode hu
  have hstrip : PolyTimeComputable (fun x => match pairDecode x with
      | some (a, v) =>
        match splitAtLastTrue v with
        | some u => Turing.pairEncode a u
        | none => []
      | none => []) := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_stripLast
    exact ⟨M, c, 2, hM⟩
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  convert hs.comp (hstrip.comp hpair) using 1
  funext x
  simp only [Function.comp_apply, id, pairDecode_pairEncode, Nat.pow_one, Nat.one_mul,
    splitAtLastTrue_replicate_succ, Option.map_some, Option.getD_some]

/-- **FP is closed under concatenation**: if `f` and `g` are polynomial-time computable,
so is `x ↦ f x ++ g x`. (Pair the two results, `PolyTimeComputable.pairEncode`, then
concatenate the components, `Turing.FinTM.computesFunInTime_pairConcat`.) -/
theorem PolyTimeComputable.append {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => f x ++ g x) := by
  have hc := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert hc.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- `x ↦ 1^{C (|x| + 1)^d}` is polynomial-time computable. -/
theorem polyTimeComputable_polyUnary (C d : ℕ) :
    PolyTimeComputable fun x => List.replicate (C * (x.length + 1) ^ d) true := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyUnary C d
  exact ⟨M, a, d + 1, hM⟩

/-- Prepending a fixed word is polynomial-time. -/
theorem polyTimeComputable_prepend (w : List Bool) : PolyTimeComputable (fun x => w ++ x) :=
  polyTimeComputable_of_linear (FinTM.computesFunInTime_prepend w)

/-! ### Total pair projections -/

/-- The total first projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairFstD (z : List Bool) : List Bool := ((pairDecode z).map Prod.fst).getD []

/-- The total second projection of a `Turing.pairEncode` pair (`[]` on malformed words). -/
def pairSndD (z : List Bool) : List Bool := ((pairDecode z).map Prod.snd).getD []

/-- The first projection of a pair is its first component. -/
@[simp] theorem pairFstD_pairEncode (a b : List Bool) : pairFstD (pairEncode a b) = a := by
  simp [pairFstD, pairDecode_pairEncode]

/-- The second projection of a pair is its second component. -/
@[simp] theorem pairSndD_pairEncode (a b : List Bool) : pairSndD (pairEncode a b) = b := by
  simp [pairSndD, pairDecode_pairEncode]

/-- The first projection of a word is no longer than the word. -/
theorem length_pairFstD_le (z : List Bool) : (pairFstD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := Turing.eq_pairEncode_of_pairDecode z a b h
    subst hz
    simp [length_pairEncode]
    omega

/-- The first projection is polynomial-time computable. -/
theorem polyTimeComputable_pairFstD : PolyTimeComputable pairFstD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst

/-- The second projection is polynomial-time computable. -/
theorem polyTimeComputable_pairSndD : PolyTimeComputable pairSndD :=
  polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd

/-- Iterated first projections (the root of a nested tuple) are polynomial-time. -/
theorem polyTimeComputable_iterate_pairFstD (n : ℕ) : PolyTimeComputable (pairFstD^[n]) := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact polyTimeComputable_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact polyTimeComputable_pairFstD.comp ih

/-- Concatenating the two components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairConcat :
    PolyTimeComputable (fun z => pairFstD z ++ pairSndD z) := by
  have h := polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  convert h using 1
  funext z
  cases hz : pairDecode z with
  | none => simp [pairFstD, pairSndD, hz]
  | some p => cases p; simp [pairFstD, pairSndD, hz]

/-- Swapping the components of a pair is polynomial-time. -/
theorem polyTimeComputable_pairSwap :
    PolyTimeComputable (fun z => pairEncode (pairSndD z) (pairFstD z)) :=
  polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD

/-! ### Branching and length tests -/

/-- **Polynomial-time branching**: if the test `p` (as a one-bit output) and both branches
are polynomial-time computable, so is `x ↦ if p x then f x else g x`.

**Proof sketch.** The timed branch contract `Turing.FinTM.computesFunInTime_cond` runs
the test, then the selected branch; enlarge the three degrees to their maximum and
absorb the constants. -/
theorem polyTimeComputable_ite {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) := by
  obtain ⟨D, A, a, hD⟩ := hp
  obtain ⟨F, B, b, hF⟩ := hf
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hD hF hG
  let e := max a (max b c)
  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
  have hpow (d : ℕ) (hd : d ≤ e) : (x.length + 1) ^ d ≤ (x.length + 1) ^ e :=
    Nat.pow_le_pow_right (Nat.succ_pos _) hd
  have ha := Nat.mul_le_mul_left A (hpow a (Nat.le_max_left _ _))
  have hb := Nat.mul_le_mul_left B (hpow b
    ((Nat.le_max_left b c).trans (Nat.le_max_right a (max b c))))
  have hc := Nat.mul_le_mul_left C (hpow c
    ((Nat.le_max_right b c).trans (Nat.le_max_right a (max b c))))
  have hbc : max (B * (x.length + 1) ^ b) (C * (x.length + 1) ^ c) ≤
      B * (x.length + 1) ^ e + C * (x.length + 1) ^ e :=
    max_le (by omega) (by omega)
  have hone := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
  calc
    _ ≤ K * (A * (x.length + 1) ^ e +
        (B * (x.length + 1) ^ e + C * (x.length + 1) ^ e) +
        (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (Nat.add_le_add (Nat.add_le_add ha hbc) hone)
    _ = _ := by ring

/-- Polynomial-time Boolean conjunction of two one-bit tests. -/
theorem polyTimeComputable_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) := by
  convert polyTimeComputable_ite hp hq (polyTimeComputable_const [false]) using 1
  funext x
  cases p x <;> rfl

/-- The length test `|snd z| ≤ |fst z|` on pairs is polynomial-time.

**Proof sketch.** The catalog's threaded length check at `(C, e) = (1, 1)` decides
`|b| ≤ |a| + 1` on `⟨a, b⟩`; apply it to `⟨fst z, 1 :: snd z⟩`. -/
theorem polyTimeComputable_lenLe :
    PolyTimeComputable (fun z => [decide ((pairSndD z).length ≤ (pairFstD z).length)]) := by
  have hchk : PolyTimeComputable (fun x => [match pairDecode x with
      | some (a, b) => decide (b.length ≤ 1 * (a.length + 1) ^ 1)
      | none => false]) := by
    obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairLenCheck 1 1
    exact ⟨M, a, 2, hM⟩
  have hpair : PolyTimeComputable (fun z => pairEncode (pairFstD z) (true :: pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode
      ((polyTimeComputable_prepend [true]).comp polyTimeComputable_pairSndD)
  convert hchk.comp hpair using 1
  funext z
  simp [pairDecode_pairEncode]

/-- The length-equality test `|fst z| = |snd z|` on pairs is polynomial-time. -/
theorem polyTimeComputable_lenEq :
    PolyTimeComputable (fun z => [decide ((pairFstD z).length = (pairSndD z).length)]) := by
  have h := polyTimeComputable_and polyTimeComputable_lenLe
    (polyTimeComputable_lenLe.comp polyTimeComputable_pairSwap)
  convert h using 1
  funext z
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  congr 1
  by_cases h1 : (pairFstD z).length = (pairSndD z).length
  · simp [h1]
  · rcases Nat.lt_or_gt_of_ne h1 with h2 | h2
    · simp [h1, Nat.not_le_of_lt h2]
    · simp [h1, Nat.not_le_of_lt h2]

end Complexity
