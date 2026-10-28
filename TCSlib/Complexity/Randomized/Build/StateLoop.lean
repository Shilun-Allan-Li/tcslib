/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State loops: the pure and FP layer behind the derived repetition lemmas

The derived lemmas of `TCSlib.Complexity.Randomized.Repetition` — the `R(|x|)`-fold
iteration `Complexity.polyTimeComputable_iterate`, the concatenating variant
`Complexity.polyTimeComputable_iterateEmit`, and the string functions
`Complexity.polyTimeComputable_majority`, `polyTimeComputable_pairXor`,
`polyTimeComputable_pairEq`, `polyTimeComputable_blockMap` — are all instances of one pattern,
the **state loop**: a state word `⟨x, s⟩` whose first component retains the input `x` and whose
second component `s` evolves by a polynomial-time map `step` from `start x`; a polynomial-time
test `acc` fires for the first time at a round `N x ≤ R|x|`, and a polynomial-time `out` reads
the answer off the state. The loop is run by `Complexity.polyTimeComputable_iterateFind` on the
**guarded** step `Complexity.StateLoop.gstep step B`, which refuses to move when the new state
would exceed the length bound `B|fst w|`; thus the orbit of *every* word is polynomially
bounded (the hypothesis `horbit` of the repetition lemma quantifies over all words, not only
over well-formed state words), while on the genuine orbit the guard never fires.

This file supplies everything that does not depend on the repetition lemma itself:

* a small FP toolkit (head bit, tail, Boolean connectives of one-bit tests, the emptiness test
  and the length comparison of two polynomial-time maps);
* the state orbit `Complexity.StateLoop.orbit`, the guarded step `Complexity.StateLoop.gstep`
  with its polynomial bound on arbitrary words and its agreement with the orbit on well-formed
  words, and the `List.find?` evaluation `Complexity.StateLoop.find?_range_eq_some`;
* for the two iteration lemmas, the data of their state loops (`start`, `step`, `acc`, `out`),
  their polynomial-time proofs and the closed forms of the orbits (namespaces
  `Complexity.StateLoop.IterLoop` and `Complexity.StateLoop.EmitLoop`).

The four string loops (`MajLoop`, `XorLoop`, `EqLoop`, `BlockLoop`) are in
`TCSlib.Complexity.Randomized.Build.StringLoops`; the assembly through
`Complexity.polyTimeComputable_iterateFind` and the six public theorems live in
`TCSlib.Complexity.Randomized.Repetition`.

## Main definitions

* `Complexity.StateLoop.orbit`, `Complexity.StateLoop.gstep`, `Complexity.StateLoop.gstepBound`
  — the state orbit, the length-guarded step on state words and its orbit bound.
* `Complexity.StateLoop.IterLoop`, `Complexity.StateLoop.EmitLoop` — the state-loop data of
  `Complexity.polyTimeComputable_iterate` and `polyTimeComputable_iterateEmit`.

## Main results

* `Complexity.StateLoop.gstep_poly`, `Complexity.StateLoop.length_gstep_iterate_le`,
  `Complexity.StateLoop.gstep_iterate_eq` — the guarded step is polynomial-time, its orbit
  from any word `w` stays within `3|w| + 2 + B|w|`, and on the genuine orbit it agrees with
  `orbit`.
* `Complexity.StateLoop.find?_range_eq_some` — `List.find?` on `List.range (m + 1)` returns the
  first index at which the predicate holds.
* `Complexity.StateLoop.IterLoop.orbit_eq`, `Complexity.StateLoop.EmitLoop.orbit_eq` — the
  closed forms `⟨1^i, g^[i] x⟩` and `⟨1^i, ⟨g^[i] x, emit x ++ ⋯ ++ emit (g^[i-1] x)⟩⟩`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Lemma 80.5; Theorem 87.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines; §2.2, the class FP.)
-/

namespace Complexity.StateLoop

open Turing

/-! ### An FP toolkit -/

/-- The length comparison `|g x| ≤ |f x|` of two polynomial-time maps is a polynomial-time
one-bit test (`Complexity.polyTimeComputable_lenLe` on the pair `⟨f x, g x⟩`). -/
theorem lenLe_comp {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun x => [decide ((g x).length ≤ (f x).length)] := by
  convert polyTimeComputable_lenLe.comp (hf.pairEncode hg) using 1
  funext x
  simp

/-- The unary string `1^{p(|f x|)}` of a polynomial-time map `f` is polynomial-time
(`Complexity.polyTimeComputable_unaryPoly` after `f`). -/
theorem unaryPoly_comp (p : PolyExpr) {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    PolyTimeComputable fun x => List.replicate (p.eval (f x).length) true :=
  (polyTimeComputable_unaryPoly p).comp hf

/-- The first bit of a word (`false` on the empty word) as a one-bit output: `[w.headD false]`
is `(w ++ [false]).take 1`, a typed cut `Complexity.polyTimeComputable_pairTakePoly` at the
constant length `1`. -/
theorem headBit_poly : PolyTimeComputable fun w => [w.headD false] := by
  have h := (polyTimeComputable_pairTakePoly (.const 1)).comp
    ((polyTimeComputable_const []).pairEncode
      (polyTimeComputable_id.append (polyTimeComputable_const [false])))
  convert h using 1
  funext w
  cases w <;> simp

/-- The tail of a word is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` at the
constant length `1`). -/
theorem tail_poly : PolyTimeComputable List.tail := by
  have h := (polyTimeComputable_pairDropPoly (.const 1)).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id)
  convert h using 1
  funext w
  simp [List.drop_one]

/-- Prepending one bit is polynomial-time. -/
theorem cons_poly (b : Bool) : PolyTimeComputable fun w => b :: w :=
  polyTimeComputable_prepend [b]

/-- The emptiness test `[decide (w = [])]` is polynomial-time (the length test `|w| ≤ 0`). -/
theorem isNil_poly : PolyTimeComputable fun w => [decide (w = [])] := by
  convert lenLe_comp (polyTimeComputable_const []) polyTimeComputable_id using 1
  funext w
  simp

/-- Negation of a one-bit test is polynomial-time. -/
theorem not_poly {p : List Bool → Bool} (hp : PolyTimeComputable fun x => [p x]) :
    PolyTimeComputable fun x => [!p x] := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [false])
    (polyTimeComputable_const [true]) using 1
  funext x
  cases p x <;> rfl

/-- Disjunction of two one-bit tests is polynomial-time. -/
theorem or_poly {p q : List Bool → Bool} (hp : PolyTimeComputable fun x => [p x])
    (hq : PolyTimeComputable fun x => [q x]) : PolyTimeComputable fun x => [p x || q x] := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [true]) hq using 1
  funext x
  cases p x <;> rfl

/-- Exclusive or of two one-bit tests is polynomial-time. -/
theorem xor_poly {p q : List Bool → Bool} (hp : PolyTimeComputable fun x => [p x])
    (hq : PolyTimeComputable fun x => [q x]) :
    PolyTimeComputable fun x => [xor (p x) (q x)] := by
  convert polyTimeComputable_ite hp (not_poly hq) hq using 1
  funext x
  cases p x <;> cases q x <;> rfl

/-- The two components of a word together are no longer than the word. -/
theorem length_pairFstD_add_pairSndD_le (z : List Bool) :
    (pairFstD z).length + (pairSndD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairFstD, pairSndD, h]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z a b h
    subst hz
    rw [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode]
    omega

/-- The length of the concatenation of `i` chunks of length at most `M` is at most `i · M`. -/
theorem length_flatMap_range_le (f : ℕ → List Bool) (M : ℕ) :
    ∀ i, (∀ j < i, (f j).length ≤ M) → ((List.range i).flatMap f).length ≤ i * M
  | 0, _ => by simp
  | i + 1, hf => by
    rw [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_singleton,
      Nat.succ_mul]
    have h1 := length_flatMap_range_le f M i (fun j hj => hf j (Nat.lt_succ_of_lt hj))
    have h2 := hf i (Nat.lt_succ_self i)
    omega

/-- `List.find?` on `List.range (m + 1)` returns the first index `N ≤ m` at which the predicate
holds (`List.find?_eq_some_iff_getElem`). -/
theorem find?_range_eq_some {p : ℕ → Bool} {N m : ℕ} (hN : N ≤ m)
    (hfirst : ∀ i < N, p i = false) (hlast : p N = true) :
    (List.range (m + 1)).find? p = some N := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨hlast, N, by simpa using Nat.lt_succ_of_le hN, by simp, fun j hj => ?_⟩
  simp [hfirst j hj]

/-! ### The state orbit and the guarded step -/

/-- The state orbit: `orbit start step x i` is the state after `i` rounds, from `start x`,
advancing by `s ↦ step ⟨x, s⟩` (the step reads the retained input `x` off the state word). -/
def orbit (start step : List Bool → List Bool) (x : List Bool) : ℕ → List Bool
  | 0 => start x
  | i + 1 => step (pairEncode x (orbit start step x i))

/-- The orbit at round `0` is the initial state. -/
@[simp] theorem orbit_zero (start step : List Bool → List Bool) (x : List Bool) :
    orbit start step x 0 = start x := rfl

/-- The orbit at round `i + 1` is the step applied to the state word at round `i`. -/
@[simp] theorem orbit_succ (start step : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    orbit start step x (i + 1) = step (pairEncode x (orbit start step x i)) := rfl

/-- The length-guarded step on state words: advance `w` to `⟨fst w, step w⟩` if the new state
fits the bound `B|fst w|`, else stay. -/
def gstep (step : List Bool → List Bool) (B : PolyExpr) (w : List Bool) : List Bool :=
  if (step w).length ≤ B.eval (pairFstD w).length then pairEncode (pairFstD w) (step w) else w

/-- The bound `3n + 2 + B(n)` on the guarded orbit of an arbitrary word of length `n`. -/
def gstepBound (B : PolyExpr) : PolyExpr :=
  .add (.mul (.const 3) .var) (.add (.const 2) B)

/-- The guarded step is polynomial-time: `Complexity.polyTimeComputable_ite` on the length
test `|step w| ≤ |1^{B|fst w|}|` (`lenLe_comp`, `unaryPoly_comp`), the pairing of the first
projection with `step`, and the identity. -/
theorem gstep_poly {step : List Bool → List Bool} (hstep : PolyTimeComputable step)
    (B : PolyExpr) : PolyTimeComputable (gstep step B) := by
  have htest : PolyTimeComputable fun w =>
      [decide ((step w).length ≤ B.eval (pairFstD w).length)] := by
    convert lenLe_comp (unaryPoly_comp B polyTimeComputable_pairFstD) hstep using 1
    funext w
    simp
  convert polyTimeComputable_ite htest (polyTimeComputable_pairFstD.pairEncode hstep)
    polyTimeComputable_id using 1
  funext w
  simp [gstep]

/-- Along the guarded orbit of any word `w`, every point is `w` itself or a state word
`⟨fst w, s⟩` with `|s| ≤ B|fst w|`.

**Proof sketch.** Induction on the round. From `w` itself the guarded step either stays
(first alternative) or moves to `⟨fst w, step w⟩` with the guard's bound. From a state word
`⟨fst w, s⟩` the first projection is again `fst w` (`Complexity.pairFstD_pairEncode`), so the
step either stays (the bound on `s` is inherited) or moves to `⟨fst w, step ⟨fst w, s⟩⟩` with
the guard's bound. -/
theorem gstep_iterate_cases (step : List Bool → List Bool) (B : PolyExpr) (w : List Bool)
    (i : ℕ) :
    (gstep step B)^[i] w = w ∨
      ∃ s, (gstep step B)^[i] w = pairEncode (pairFstD w) s ∧
        s.length ≤ B.eval (pairFstD w).length := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with hw | ⟨s, hs, hlen⟩
    · rw [hw]
      unfold gstep
      split_ifs with hg
      · exact Or.inr ⟨step w, rfl, hg⟩
      · exact Or.inl rfl
    · rw [hs]
      unfold gstep
      rw [pairFstD_pairEncode]
      split_ifs with hg
      · exact Or.inr ⟨_, rfl, hg⟩
      · exact Or.inr ⟨s, rfl, hlen⟩

/-- The guarded orbit of any word `w` stays within `3|w| + 2 + B|w|` (`gstep_iterate_cases`,
`Complexity.length_pairFstD_le` and the monotonicity of `B`). -/
theorem length_gstep_iterate_le (step : List Bool → List Bool) (B : PolyExpr) (w : List Bool)
    (i : ℕ) : ((gstep step B)^[i] w).length ≤ (gstepBound B).eval w.length := by
  have hB := B.eval_mono (length_pairFstD_le w)
  have hf := length_pairFstD_le w
  simp only [gstepBound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]
  rcases gstep_iterate_cases step B w i with hw | ⟨s, hs, hlen⟩
  · rw [hw]; omega
  · rw [hs, length_pairEncode]; omega

/-- On the genuine orbit the guard never fires: if the states of the first `n` rounds fit the
bound `B|x|`, the guarded orbit from `⟨x, start x⟩` is `⟨x, orbit start step x i⟩` for `i ≤ n`. -/
theorem gstep_iterate_eq (start step : List Bool → List Bool) (B : PolyExpr) (x : List Bool)
    (n : ℕ) (hb : ∀ i ≤ n, (orbit start step x i).length ≤ B.eval x.length) :
    ∀ i ≤ n, (gstep step B)^[i] (pairEncode x (start x)) = pairEncode x (orbit start step x i) := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (Nat.le_of_succ_le hi)]
    have hb' : (step (pairEncode x (orbit start step x i))).length ≤ B.eval x.length :=
      hb (i + 1) hi
    unfold gstep
    rw [pairFstD_pairEncode, if_pos hb']
    rfl

/-! ### `iterate`: a unary round counter next to the orbit point -/

namespace IterLoop

/-- The initial state `⟨[], x⟩`: empty counter, orbit point `x`. -/
def start (x : List Bool) : List Bool := pairEncode [] x

/-- The step on the state word `⟨x, ⟨cnt, s⟩⟩`: append a token to the counter and advance the
orbit point, giving `⟨true :: cnt, g s⟩`. -/
def step (g : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (true :: pairFstD (pairSndD w)) (g (pairSndD (pairSndD w)))

/-- The acceptance test on `⟨x, ⟨cnt, s⟩⟩`: the counter has reached `R|x|`. -/
def acc (R : PolyExpr) (w : List Bool) : Bool :=
  decide (R.eval (pairFstD w).length ≤ (pairFstD (pairSndD w)).length)

/-- The output on `⟨x, ⟨cnt, s⟩⟩`: the orbit point `s`. -/
def out (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_const []).pairEncode polyTimeComputable_id

/-- The step is polynomial-time. -/
theorem step_poly {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (step g) :=
  ((cons_poly true).comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
    (hg.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The acceptance test is polynomial-time (`lenLe_comp` against `1^{R|x|}`). -/
theorem acc_poly (R : PolyExpr) : PolyTimeComputable fun w => [acc R w] := by
  convert lenLe_comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
    (unaryPoly_comp R polyTimeComputable_pairFstD) using 1
  funext w
  simp [acc]

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- The closed form of the orbit: `⟨1^i, g^[i] x⟩`. -/
theorem orbit_eq (g : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    orbit start (step g) x i = pairEncode (List.replicate i true) (g^[i] x) := by
  induction i with
  | zero => simp [start]
  | succ i ih => simp [step, ih, List.replicate_succ, Function.iterate_succ_apply']

end IterLoop

/-! ### `iterateEmit`: counter, orbit point and accumulator -/

namespace EmitLoop

/-- The initial state `⟨[], ⟨x, []⟩⟩`: empty counter, orbit point `x`, empty accumulator. -/
def start (x : List Bool) : List Bool := pairEncode [] (pairEncode x [])

/-- The step on `⟨x, ⟨cnt, ⟨s, a⟩⟩⟩`: `⟨true :: cnt, ⟨g s, a ++ emit s⟩⟩`. -/
def step (g emit : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairEncode (true :: pairFstD (pairSndD w))
    (pairEncode (g (pairFstD (pairSndD (pairSndD w))))
      (pairSndD (pairSndD (pairSndD w)) ++ emit (pairFstD (pairSndD (pairSndD w)))))

/-- The output on `⟨x, ⟨cnt, ⟨s, a⟩⟩⟩`: `a ++ emit s`. -/
def out (emit : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD w)) ++ emit (pairFstD (pairSndD (pairSndD w)))

/-- The orbit point of the state word. -/
theorem point_poly : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD w)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The accumulator of the state word. -/
theorem accum_poly : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_const []).pairEncode
    (polyTimeComputable_id.pairEncode (polyTimeComputable_const []))

/-- The step is polynomial-time. -/
theorem step_poly {g emit : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hemit : PolyTimeComputable emit) : PolyTimeComputable (step g emit) :=
  ((cons_poly true).comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
    ((hg.comp point_poly).pairEncode (accum_poly.append (hemit.comp point_poly)))

/-- The output is polynomial-time. -/
theorem out_poly {emit : List Bool → List Bool} (hemit : PolyTimeComputable emit) :
    PolyTimeComputable (out emit) :=
  accum_poly.append (hemit.comp point_poly)

/-- The closed form of the orbit: `⟨1^i, ⟨g^[i] x, emit x ++ ⋯ ++ emit (g^[i-1] x)⟩⟩`. -/
theorem orbit_eq (g emit : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    orbit start (step g emit) x i =
      pairEncode (List.replicate i true)
        (pairEncode (g^[i] x) ((List.range i).flatMap fun j => emit (g^[j] x))) := by
  induction i with
  | zero => simp [start]
  | succ i ih =>
    simp [step, ih, List.replicate_succ, Function.iterate_succ_apply', List.range_succ]

end EmitLoop

end Complexity.StateLoop
