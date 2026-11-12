/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import TCSlib.Complexity.CircuitComplexity.PPoly

/-!
# Shannon's hard functions for the book's circuit model

[AB09, Thm 6.21]: for every `n > 1` some Boolean function on `n` bits is computed by no
circuit of size `2 ^ n / (10 n)`.  Here "circuit" is the book's model
`BoolCircuit.DAGCircuit` (Def 6.1) with fan-in at most two (`DAGCircuit.IsFaninTwo`), and
size counts every vertex, the `n` inputs included.  The tree-circuit (formula) analogue,
with a different cutoff in a different model, is `HardFunctions.lean`.

## Main definitions

* `BoolCircuit.computableDAG n S` — the Boolean functions on `n` bits computed by a
  fan-in-two circuit of size at most `S`.  (The circuit descriptions used for counting
  are private.)

## Main results

* `BoolCircuit.card_computable_dag_le` — at most `(S + 1) * (3 (S + 1) ^ 2) ^ S * S`
  Boolean functions on `n` bits are computed by a fan-in-two circuit of size at most `S`.
* `BoolCircuit.exists_not_eval_dag_of_lt` — whenever that number is below `2 ^ 2 ^ n`,
  some function differs from every such circuit at some input.
* `BoolCircuit.exists_hard_function_dag` — [AB09, Thm 6.21] with the book's constant:
  for `n > 1` some `f` is computed by no fan-in-two circuit of size `≤ 2 ^ n / (10 n)`.
* `BoolCircuit.exists_language_hard_dag` — one language that escapes every `SIZE(T)`
  with `T n ≤ 2 ^ n / (10 n)` at some single length `n > 1`.

## Divergences from [AB09, Thm 6.21]

* **Counting.**  [AB09] bounds the number of size-`S` circuits by `2 ^ (9 S log S)` via
  an adjacency-list encoding.  We count descriptions directly: a number of gates `≤ S`,
  for each of at most `S` gates a kind (three options) and at most two argument vertices
  (each absent or one of `S` vertices), and an output vertex below `S`.  This gives
  `(S + 1) * (3 (S + 1) ^ 2) ^ S * S ≤ (2 (S + 1)) ^ (2 (S + 1))`, the same
  `2 ^ O(S log S)` shape, and it is below `2 ^ 2 ^ n` whenever `10 n S ≤ 2 ^ n` and
  `n ≥ 1`.  The statement keeps the book's cutoff `2 ^ n / (10 n)` (`ℕ` division).
* **Fan-in at most two.**  The model allows `∧`/`∨` fan-in `0` or `1` (see
  `DAGCircuit.lean`), which only enlarges the family the theorem quantifies over, so the
  statement is at least as strong as the book's.  `IsFaninTwo` also includes
  well-formedness (`DAGCircuit.IsWellFormed`): a `¬` gate has exactly one argument and no
  gate reads a vertex twice (`args.Nodup`, the book's graph has no parallel edges), both
  of which hold of every circuit in the sense of [AB09, Def 6.1].
* **Small `n`.**  Size counts the `n` input vertices, so a circuit has size at least `n`.
  With `ℕ` division `2 ^ n / (10 n)` is below `n` for `2 ≤ n ≤ 9` (it is `0` for
  `n ≤ 5`, then `1, 1, 3, 5`), so the statement is vacuous there.  So is the book's:
  its size also counts the `n` inputs ([AB09, Def 6.1]) and the real number
  `2 ^ n / (10 n)` is below `n` for every `n ≤ 9` (below `1` for `n ≤ 5`), so `ℕ`
  division adds no vacuity of its own.  At `n = 10` the cutoff is `10 = n`, admitting only
  the gateless circuits (projections); circuits with gates are first excluded at `n = 11`
  (`⌊2048 / 110⌋ = 18`).  No hypothesis beyond the book's `n > 1` is added.
* **Languages.**  [AB09] states the theorem for functions only.  `SIZE(2 ^ n / (10 n))`
  itself is empty in our `ℕ` reading (at `n = 0` the bound is `1 / 0 = 0`, and every
  circuit has a vertex), so `¬ L.InSIZE (fun n => 2 ^ n / (10 * n))` would be trivial;
  `exists_language_hard_dag` instead quantifies over every `T` that meets the Shannon
  bound at a single length `n > 1`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (Theorem 6.21.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-! ## Circuit descriptions -/

/-- A gate description over vertices below `S`: a kind code and up to two arguments. -/
private abbrev GateCode (S : ℕ) := Fin 3 × Option (Fin S) × Option (Fin S)

/-- A circuit description over vertices below `S`: a gate count `≤ S`, a gate
description for each of the first `S` slots (only the first `count` are used), and an
output vertex. -/
private abbrev CircCode (S : ℕ) := Fin (S + 1) × (Fin S → GateCode S) × Fin S

/-- Decode a kind code. -/
private def decodeKind : Fin 3 → GateKind
  | ⟨0, _⟩ => .and
  | ⟨1, _⟩ => .or
  | _ => .not

/-- Encode a gate kind. -/
private def encodeKind : GateKind → Fin 3
  | .and => 0
  | .or => 1
  | .not => 2

private theorem decodeKind_encodeKind (k : GateKind) : decodeKind (encodeKind k) = k := by
  cases k <;> rfl

/-- Decode a gate description. -/
private def decodeGate {S : ℕ} (c : GateCode S) : DAGGate :=
  ⟨decodeKind c.1, [c.2.1, c.2.2].filterMap (Option.map Fin.val)⟩

/-- Encode an optional argument vertex, dropping it if it is not below `S`. -/
private def encodeArg (S : ℕ) (a : Option ℕ) : Option (Fin S) :=
  a.bind fun a => if h : a < S then some ⟨a, h⟩ else none

/-- Encode a gate: its kind and its first two arguments. -/
private def encodeGate (S : ℕ) (g : DAGGate) : GateCode S :=
  (encodeKind g.kind, encodeArg S g.args[0]?, encodeArg S g.args[1]?)

/-- A gate of fan-in at most two reading only vertices below `S` is recovered from its
encoding. -/
private theorem decodeGate_encodeGate {S : ℕ} (g : DAGGate) (hlen : g.args.length ≤ 2)
    (hlt : ∀ a ∈ g.args, a < S) : decodeGate (encodeGate S g) = g := by
  obtain ⟨k, args⟩ := g
  simp only at hlen hlt
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [decodeGate, encodeGate, encodeArg, decodeKind_encodeKind]
  · have ha := hlt a (by simp)
    simp [decodeGate, encodeGate, encodeArg, decodeKind_encodeKind, ha]
  · have ha := hlt a (by simp)
    have hb := hlt b (by simp)
    simp [decodeGate, encodeGate, encodeArg, decodeKind_encodeKind, ha, hb]
  · simp at hlen

/-- The gate list a description denotes. -/
private def gatesOf {S : ℕ} (d : CircCode S) : List DAGGate :=
  List.ofFn fun i : Fin d.1 => decodeGate (d.2.1 ⟨i, by have := d.1.isLt; omega⟩)

/-- The function a description computes on `n` inputs. -/
private def evalCode (n : ℕ) {S : ℕ} (d : CircCode S) (x : Fin n → Bool) : Bool :=
  (runWith DAGGate.eval (gatesOf d) (List.ofFn x)).getD d.2.2 false

/-- Every fan-in-two circuit of size at most `S` computes the function of some
description. -/
private theorem exists_code {n S : ℕ} (C : DAGCircuit n) (hC : C.IsFaninTwo)
    (hS : C.size ≤ S) : ∃ d : CircCode S, evalCode n d = C.eval := by
  have hsz : n + C.gates.length ≤ S := hS
  let gs : Fin S → GateCode S := fun i =>
    if h : (i : ℕ) < C.gates.length then encodeGate S C.gates[i] else (0, none, none)
  refine ⟨(⟨C.gates.length, by omega⟩, gs, ⟨C.output, by have := C.output_lt; omega⟩), ?_⟩
  have hgates : gatesOf (⟨C.gates.length, by omega⟩, gs,
      (⟨C.output, by have := C.output_lt; omega⟩ : Fin S)) = C.gates := by
    apply List.ext_getElem (by simp [gatesOf])
    intro i h₁ h₂
    simp only [gatesOf, List.getElem_ofFn, gs, dif_pos h₂]
    refine decodeGate_encodeGate _ (hC.2 _ (List.getElem_mem h₂)) fun a ha => ?_
    have := C.args_lt i h₂ a ha
    omega
  funext x
  simp only [evalCode, hgates]
  rfl

/-! ## The counting argument -/

/-- The set of Boolean functions on `n` bits computed by some fan-in-two circuit of the
book's model with at most `S` vertices. -/
def computableDAG (n S : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ C : DAGCircuit n, C.IsFaninTwo ∧ C.size ≤ S ∧ C.eval = f}

/-- At most `(S + 1) * (3 (S + 1) ^ 2) ^ S * S` Boolean functions on `n` bits are
computed by a fan-in-two circuit of size at most `S`.  [AB09, Thm 6.21] (the counting
step, with an explicit description count in place of the book's `2 ^ (9 S log S)`).

**Proof sketch.** Every such circuit has at most `S` vertices, so it is described by its
number of gates (at most `S`), for each gate its kind (three options) and at most two
argument vertices (each absent or one of the `S` vertices), and its output vertex (one
of `S`); the function the circuit computes depends only on that description. So the
functions in question are among the images of the descriptions, of which there are the
displayed number. -/
theorem card_computable_dag_le (n S : ℕ) :
    (computableDAG n S).ncard ≤ (S + 1) * (3 * (S + 1) ^ 2) ^ S * S := by
  classical
  have hsub : computableDAG n S ⊆ ↑(Finset.univ.image (evalCode n (S := S))) := by
    rintro f ⟨C, hC, hS, rfl⟩
    obtain ⟨d, hd⟩ := exists_code C hC hS
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact ⟨d, hd⟩
  calc _ ≤ (↑(Finset.univ.image (evalCode n (S := S))) :
          Set ((Fin n → Bool) → Bool)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.univ.image (evalCode n (S := S))).card := Set.ncard_coe_finset _
    _ ≤ (Finset.univ : Finset (CircCode S)).card := Finset.card_image_le
    _ = (S + 1) * (3 * (S + 1) ^ 2) ^ S * S := by
      simp [Finset.card_univ, Fintype.card_prod, Fintype.card_option]
      ring

/-- Some Boolean function on `n` bits differs, at some input, from every fan-in-two
circuit of size at most `S`, whenever `(S + 1) * (3 (S + 1) ^ 2) ^ S * S < 2 ^ 2 ^ n`.
[AB09, Thm 6.21]

**Proof sketch.** There are `2 ^ 2 ^ n` functions and, by `card_computable_dag_le`, fewer
are computed by such circuits; a function outside that set is computed by none of them,
and two distinct functions differ at a point. -/
theorem exists_not_eval_dag_of_lt {n S : ℕ}
    (h : (S + 1) * (3 * (S + 1) ^ 2) ^ S * S < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ C : DAGCircuit n, C.IsFaninTwo → C.size ≤ S →
      ∃ x, C.eval x ≠ f x := by
  classical
  set T : Set ((Fin n → Bool) → Bool) := computableDAG n S
  have hcard : T.ncard ≤ (S + 1) * (3 * (S + 1) ^ 2) ^ S * S := card_computable_dag_le n S
  have hcardF : Nat.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
    simp
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → Bool) → Bool, f ∉ T := by
    by_contra hcon
    push_neg at hcon
    rw [Set.eq_univ_of_forall hcon, Set.ncard_univ, hcardF] at hcard
    omega
  refine ⟨f, fun C hC hS => ?_⟩
  by_contra hcon
  push_neg at hcon
  exact hf ⟨C, hC, hS, funext hcon⟩

/-- The description count is below `2 ^ 2 ^ n` once `10 n S ≤ 2 ^ n` and `n ≥ 1`.

**Proof sketch.** The case `S = 0` is immediate. Otherwise first bound the count by
`(2(S+1))^{2(S+1)}`, since `(S+1)S ≤ (2(S+1))²` and `3(S+1)² ≤ (2(S+1))²`. The hypothesis
`10 n S ≤ 2ⁿ` gives `2(S+1) ≤ 2ⁿ` and `n · 2(S+1) < 2ⁿ`, hence
`(2(S+1))^{2(S+1)} ≤ 2^{n · 2(S+1)} < 2^{2ⁿ}`. -/
private theorem count_lt {n S : ℕ} (hn : 1 ≤ n) (hS : 10 * n * S ≤ 2 ^ n) :
    (S + 1) * (3 * (S + 1) ^ 2) ^ S * S < 2 ^ 2 ^ n := by
  rcases Nat.eq_zero_or_pos S with rfl | hS0
  · simp only [Nat.mul_zero]
    positivity
  -- the description count is at most `(2 (S + 1)) ^ (2 (S + 1))`
  have h1 : (S + 1) * (3 * (S + 1) ^ 2) ^ S * S ≤ (2 * (S + 1)) ^ (2 * (S + 1)) := by
    calc (S + 1) * (3 * (S + 1) ^ 2) ^ S * S = ((S + 1) * S) * (3 * (S + 1) ^ 2) ^ S := by
          ring
      _ ≤ (2 * (S + 1)) ^ 2 * ((2 * (S + 1)) ^ 2) ^ S := by
          apply Nat.mul_le_mul
          · nlinarith
          · exact Nat.pow_le_pow_left (by nlinarith) _
      _ = (2 * (S + 1)) ^ (2 * (S + 1)) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
  have hnS : 1 ≤ n * S := Nat.mul_pos hn hS0
  -- `2 (S + 1) ≤ 4 S ≤ 2 ^ n`
  have h2 : 2 * (S + 1) ≤ 2 ^ n := by nlinarith
  -- `2 n (S + 1) ≤ 4 n S < 10 n S ≤ 2 ^ n`
  have h3 : n * (2 * (S + 1)) < 2 ^ n := by nlinarith
  calc (S + 1) * (3 * (S + 1) ^ 2) ^ S * S ≤ (2 * (S + 1)) ^ (2 * (S + 1)) := h1
    _ ≤ (2 ^ n) ^ (2 * (S + 1)) := Nat.pow_le_pow_left h2 _
    _ = 2 ^ (n * (2 * (S + 1))) := by rw [← pow_mul]
    _ < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) h3

/-- **Shannon's theorem.**  For every `n > 1` there is a Boolean function on `n` bits
that no fan-in-two circuit of size at most `2 ^ n / (10 n)` computes.  [AB09, Thm 6.21]

The book's model and constant; see the module docstring for the small-`n` cases: for
`2 ≤ n ≤ 9` the cutoff is below `n`, the least possible size, so the statement is vacuous
there — exactly as the book's is, its size also counting the inputs.

**Proof sketch.** Put `S = 2 ^ n / (10 n)`, so `10 n S ≤ 2 ^ n`. If `S = 0` the
description count is `0`. Otherwise the count is at most `(2 (S + 1)) ^ (2 (S + 1))`;
since `2 (S + 1) ≤ 4 S ≤ 2 ^ n` this is at most `2 ^ (2 n (S + 1))`, and
`2 n (S + 1) ≤ 4 n S < 10 n S ≤ 2 ^ n`. So fewer than `2 ^ 2 ^ n` functions are computed
by circuits of size at most `S`, and `exists_not_eval_dag_of_lt` applies. -/
theorem exists_hard_function_dag (n : ℕ) (hn : 1 < n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ C : DAGCircuit n, C.IsFaninTwo →
      C.size ≤ 2 ^ n / (10 * n) → ∃ x, C.eval x ≠ f x :=
  exists_not_eval_dag_of_lt (count_lt (by omega) (Nat.mul_div_le _ _))

/-- Some language is outside every `SIZE(T)` whose bound `T` drops to the Shannon bound
`2 ^ n / (10 n)` at some length `n > 1`.  A language form of [AB09, Thm 6.21].

**Proof sketch.** At each length `n > 1` let the language agree with a hard function of
`exists_hard_function_dag` (and be arbitrary at lengths `0` and `1`). A family deciding it
within `T` would, at a length `n > 1` with `T n ≤ 2 ^ n / (10 n)`, give a fan-in-two
circuit of that size computing the hard function. -/
theorem exists_language_hard_dag :
    ∃ L : Language Bool, ∀ T : ℕ → ℕ, (∃ n, 1 < n ∧ T n ≤ 2 ^ n / (10 * n)) →
      ¬ L.InSIZE T := by
  classical
  -- a hard function at each length `m > 1`
  let F : (m : ℕ) → (Fin m → Bool) → Bool := fun m =>
    if h : 1 < m then Classical.choose (exists_hard_function_dag m h) else fun _ => false
  refine ⟨{w | F w.length w.get = true}, ?_⟩
  rintro T ⟨n, hn, hT⟩ ⟨C, hG, hS, hL⟩
  -- the family's circuits agree with `F` at every length
  have hw : ∀ w : List Bool, (C.circuit w.length).eval w.get = F w.length w.get := fun w =>
    Bool.eq_iff_iff.mpr (Set.ext_iff.mp hL w)
  have hcast : ∀ (G : (m : ℕ) → (Fin m → Bool) → Bool) (m : ℕ) (w : List Bool)
      (h : w.length = m), G w.length w.get = G m fun i => w.get (Fin.cast h.symm i) := by
    intro G m w h
    subst h
    rfl
  have hall : ∀ y : Fin n → Bool, (C.circuit n).eval y = F n y := by
    intro y
    have hy : (fun i : Fin n => (List.ofFn y).get (Fin.cast (List.length_ofFn).symm i)) = y := by
      funext i
      simp
    have := hw (List.ofFn y)
    rwa [hcast (fun m z => (C.circuit m).eval z) n _ List.length_ofFn,
      hcast F n _ List.length_ofFn, hy] at this
  obtain ⟨x, hx⟩ := Classical.choose_spec (exists_hard_function_dag n hn) (C.circuit n) (hG n)
    ((hS n).trans hT)
  apply hx
  rw [hall x]
  simp only [F, dif_pos hn]

end BoolCircuit
