/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Computability.Language
import Mathlib.Data.List.GetD
import TCSlib.Complexity.CircuitComplexity.UnaryCode

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Algebraic circuits and the language ZEROP

The objects of polynomial identity testing [AB09, §7.2.3]: `n`-variable algebraic circuits
over `{+, −, ×}`, the integer polynomial such a circuit computes, its degree and value
bounds, the reduction of identity testing to `ZEROP`, and `ZEROP` as a `Language Bool`.

A circuit is a straight-line program: node `i` is a variable, the constant `1`, or an
operator applied to two nodes `j, k`; the output is the last node.  It is *well formed*
when it is nonempty and every operator reads earlier nodes only (the DAG condition).

## Main definitions

* `Randomized.AlgGate`, `Randomized.AlgCircuit` — nodes and circuits; `AlgCircuit.size`.
* `Randomized.AlgCircuit.eval` — evaluation over any commutative ring.
* `Randomized.AlgCircuit.toMvPolynomial` — the polynomial in `ℤ[x₁, …, x_n]` computed.
* `Randomized.AlgCircuit.WellFormed`, `Randomized.AlgCircuit.subCircuit` (`C − C′`).
* `Randomized.AlgCircuit.encode`, `Randomized.AlgCircuit.decode`, `Randomized.ZEROP`.

## Main results

* `Randomized.AlgCircuit.map_eval`, `Randomized.AlgCircuit.aeval_toMvPolynomial` — the
  circuit computes `toMvPolynomial` over every commutative ring.
* `Randomized.AlgCircuit.toMvPolynomial_eq_zero_iff` — zero polynomial iff zero function.
* `Randomized.AlgCircuit.totalDegree_toMvPolynomial_le` — degree at most `2^m`.
* `Randomized.AlgCircuit.abs_eval_le_pow` — on inputs bounded by `X ≥ 2`, `|C(x)| ≤ X^{2^m}`;
  `Randomized.AlgCircuit.abs_eval_le` — `(2X)^{2^m}` for every `X ≥ 1`.
* `Randomized.AlgCircuit.toMvPolynomial_subCircuit` — PIT reduces to ZEROP.
* `Randomized.AlgCircuit.decode_encode`, `Randomized.AlgCircuit.encode_of_decode`.

## Divergences

* Footnote 5 of [AB09, p.129] allows constants; we allow the constant `1` (every integer
  constant is then built with `+` and `−`) so that `n = 0` circuits are not all empty.
* The output is the last node, and nodes that do not feed it are allowed (the book asks
  for a single sink); such dead nodes change neither the polynomial nor any bound.
* Encoding: `n` in unary, then each node behind a continue bit, as a 3-bit tag followed by
  its unary indices (`BoolCircuit.encodeNat`); a stop bit ends the list.  `decode` parses and
  re-encodes, so only canonical strings decode.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open MvPolynomial

/-- A node of an `n`-variable algebraic circuit: an input variable, the constant `1`, or
`+`, `−`, `×` applied to the values of the nodes with indices `j` and `k`.
[AB09, §7.2.3] -/
inductive AlgGate (n : ℕ) where
  /-- The input variable `xᵢ`. -/
  | var (i : Fin n)
  /-- The constant `1`. -/
  | one
  /-- The sum of nodes `j` and `k`. -/
  | add (j k : ℕ)
  /-- The difference of nodes `j` and `k`. -/
  | sub (j k : ℕ)
  /-- The product of nodes `j` and `k`. -/
  | mul (j k : ℕ)
  deriving DecidableEq

/-- An `n`-variable algebraic circuit, as the list of its nodes in topological order; the
last node is the output.  [AB09, §7.2.3] -/
structure AlgCircuit (n : ℕ) where
  /-- The nodes, in order. -/
  gates : List (AlgGate n)
  deriving DecidableEq

namespace AlgGate

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The value of a node, given the input `x` and the values `vs` of the earlier nodes
(an index outside `vs` reads `0`). -/
def eval (x : Fin n → R) (vs : List R) : AlgGate n → R
  | var i => x i
  | one => 1
  | add j k => vs.getD j 0 + vs.getD k 0
  | sub j k => vs.getD j 0 - vs.getD k 0
  | mul j k => vs.getD j 0 * vs.getD k 0

/-- `g.refsBelow i`: every node index read by `g` is smaller than `i`. -/
def refsBelow (i : ℕ) : AlgGate n → Bool
  | var _ => true
  | one => true
  | add j k => decide (j < i ∧ k < i)
  | sub j k => decide (j < i ∧ k < i)
  | mul j k => decide (j < i ∧ k < i)

/-- Add `o` to every node index read by `g`. -/
def shift (o : ℕ) : AlgGate n → AlgGate n
  | var i => var i
  | one => one
  | add j k => add (j + o) (k + o)
  | sub j k => sub (j + o) (k + o)
  | mul j k => mul (j + o) (k + o)

/-- The value of `g` is preserved by a ring homomorphism applied to the inputs and the
earlier values. -/
theorem map_eval {S : Type*} [CommRing S] (f : R →+* S) (x : Fin n → R) (vs : List R)
    (g : AlgGate n) : f (g.eval x vs) = g.eval (f ∘ x) (vs.map f) := by
  have hget : ∀ j, (vs.map f).getD j 0 = f (vs.getD j 0) := fun j => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases vs[j]? <;> simp
  cases g <;> simp only [eval, hget, map_add, map_sub, map_mul, map_one, Function.comp]

/-- A shifted node reads, from `vs ++ ws` with `|vs| = o`, what the original reads from
`ws`. -/
theorem eval_shift (x : Fin n → R) (vs ws : List R) (g : AlgGate n) :
    (g.shift vs.length).eval x (vs ++ ws) = g.eval x ws := by
  have hget : ∀ j, (vs ++ ws).getD (j + vs.length) 0 = ws.getD j 0 := fun j => by
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel]
  cases g <;> simp only [eval, shift, hget]

end AlgGate

namespace AlgCircuit

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The values of all nodes of the gate list `gs` on input `x`, in order. -/
def run (x : Fin n → R) (gs : List (AlgGate n)) : List R :=
  gs.foldl (fun vs g => vs ++ [g.eval x vs]) []

/-- The size `m` of a circuit: its number of nodes. -/
def size (C : AlgCircuit n) : ℕ := C.gates.length

/-- The output of the circuit `C` on input `x ∈ Rⁿ` (the last node's value; `0` for the
empty circuit).  [AB09, §7.2.3] -/
def eval (C : AlgCircuit n) (x : Fin n → R) : R :=
  (run x C.gates).getD (C.size - 1) 0

/-- The polynomial in `ℤ[x₁, …, x_n]` computed by `C`: its output on the generic input
`(X₁, …, X_n)`.  [AB09, §7.2.3] -/
noncomputable def toMvPolynomial (C : AlgCircuit n) : MvPolynomial (Fin n) ℤ :=
  C.eval X

/-- `C` is well formed: it has an output node and every node reads earlier nodes only. -/
def WellFormed (C : AlgCircuit n) : Prop :=
  C.gates ≠ [] ∧ ∀ i (h : i < C.gates.length), (C.gates[i]).refsBelow i = true

instance (C : AlgCircuit n) : Decidable C.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Running `gs ++ [g]` appends `g`'s value to the values of `gs`. -/
theorem run_append_singleton (x : Fin n → R) (gs : List (AlgGate n)) (g : AlgGate n) :
    run x (gs ++ [g]) = run x gs ++ [g.eval x (run x gs)] := by
  simp [run, List.foldl_append]

/-- One value per node. -/
theorem length_run (x : Fin n → R) (gs : List (AlgGate n)) :
    (run x gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [run_append_singleton, ih]

/-- An entry of `vs ++ [v]` is an entry of `vs` (possibly the default) or `v`. -/
theorem getD_append_singleton (vs : List R) (v : R) (j : ℕ) :
    (vs ++ [v]).getD j 0 = vs.getD j 0 ∨ (vs ++ [v]).getD j 0 = v := by
  rcases lt_trichotomy j vs.length with h | h | h
  · left
    rw [List.getD_append _ _ _ _ h]
  · right
    subst h
    simp
  · left
    have h1 : (vs ++ [v]).length ≤ j := by simp; omega
    rw [List.getD_eq_default (hn := h1), List.getD_eq_default (hn := h.le)]

/-- Ring homomorphisms commute with running a circuit. -/
theorem run_map {S : Type*} [CommRing S] (f : R →+* S) (x : Fin n → R)
    (gs : List (AlgGate n)) : run (f ∘ x) gs = (run x gs).map f := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [run_append_singleton, ih, AlgGate.map_eval]

/-- **Evaluation commutes with ring homomorphisms**: `f(C(x)) = C(f ∘ x)`. -/
theorem map_eval {S : Type*} [CommRing S] (f : R →+* S) (C : AlgCircuit n)
    (x : Fin n → R) : f (C.eval x) = C.eval (f ∘ x) := by
  simp only [eval, run_map, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (run x C.gates)[C.size - 1]? <;> simp

/-- The circuit computes its polynomial over every commutative ring:
`toMvPolynomial C` evaluated at `x` is `C(x)`.  [AB09, §7.2.3: "a simple induction"] -/
theorem aeval_toMvPolynomial (C : AlgCircuit n) (x : Fin n → R) :
    aeval x C.toMvPolynomial = C.eval x := by
  have h := map_eval (aeval x : MvPolynomial (Fin n) ℤ →ₐ[ℤ] R).toRingHom C X
  convert h using 2
  funext i
  simp

/-- Integer form of `aeval_toMvPolynomial`. -/
theorem eval_toMvPolynomial (C : AlgCircuit n) (x : Fin n → ℤ) :
    MvPolynomial.eval x C.toMvPolynomial = C.eval x := by
  rw [← aeval_toMvPolynomial C x, aeval_eq_eval]

/-- `C` computes the zero polynomial iff it computes the zero function on `ℤⁿ`.
[AB09, §7.2.3, definition of ZEROP] -/
theorem toMvPolynomial_eq_zero_iff (C : AlgCircuit n) :
    C.toMvPolynomial = 0 ↔ ∀ x : Fin n → ℤ, C.eval x = 0 := by
  rw [MvPolynomial.funext_iff]
  simp [eval_toMvPolynomial]

/-- Every node of a gate list of length `L` computes a polynomial of degree `≤ 2^L`.

**Proof sketch.** Induction on the list from the right: the new node is a variable
(degree `1`), the constant (`0`), a sum or difference (the larger degree of two nodes,
`≤ 2^L`) or a product (the sum, `≤ 2^L + 2^L = 2^{L+1}`); out-of-range reads give `0`. -/
theorem totalDegree_run_le (gs : List (AlgGate n)) (j : ℕ) :
    ((run (X : Fin n → MvPolynomial (Fin n) ℤ) gs).getD j 0).totalDegree ≤ 2 ^ gs.length := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_append_singleton, List.length_append, List.length_singleton, pow_succ]
    have hle : ∀ i, ((run (X : Fin n → MvPolynomial (Fin n) ℤ) gs).getD i 0).totalDegree ≤
        2 ^ gs.length * 2 :=
      fun i => (ih i).trans (by omega)
    rcases getD_append_singleton (run (X : Fin n → MvPolynomial (Fin n) ℤ) gs) _ j with
      h | h <;> rw [h]
    · exact hle j
    · cases g with
      | var i =>
        simp only [AlgGate.eval, totalDegree_X]
        have := Nat.one_le_two_pow (n := gs.length)
        omega
      | one => simp [AlgGate.eval]
      | add a b => exact (totalDegree_add _ _).trans (max_le (hle a) (hle b))
      | sub a b => exact (totalDegree_sub _ _).trans (max_le (hle a) (hle b))
      | mul a b =>
        refine (totalDegree_mul _ _).trans ?_
        have := ih a
        have := ih b
        omega

/-- **Degree bound** [AB09, §7.2.3, p.130]: a circuit of size `m` computes a polynomial of
total degree at most `2^m`. -/
theorem totalDegree_toMvPolynomial_le (C : AlgCircuit n) :
    C.toMvPolynomial.totalDegree ≤ 2 ^ C.size :=
  totalDegree_run_le C.gates _

/-- Every node value of a gate list of length `L`, on integer inputs of absolute value at
most `X ≥ 2`, has absolute value at most `X^{2^L}`.

**Proof sketch.** Induction from the right with `B = X^{2^L} ≥ X ≥ 2`: a new node is an
input (`≤ X ≤ B`), `1`, a sum or difference (`≤ 2B ≤ B²`) or a product (`≤ B²`), and
`B² = X^{2^{L+1}}`. -/
theorem abs_run_le (x : Fin n → ℤ) (X : ℕ) (hX : 2 ≤ X) (hx : ∀ i, |x i| ≤ X)
    (gs : List (AlgGate n)) (j : ℕ) :
    |(run x gs).getD j 0| ≤ (X : ℤ) ^ 2 ^ gs.length := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => simp [run]
  | append_singleton gs g ih =>
    set B : ℤ := (X : ℤ) ^ 2 ^ gs.length with hB
    have hBX : (X : ℤ) ≤ B := le_self_pow₀ (by omega) (pow_pos two_pos _).ne'
    have hB2 : 2 ≤ B := le_trans (by exact_mod_cast hX) hBX
    have hsq : (X : ℤ) ^ 2 ^ (gs ++ [g]).length = B * B := by
      rw [hB, ← pow_add, List.length_append, List.length_singleton, pow_succ, mul_two]
    rw [run_append_singleton, hsq]
    have hle : ∀ i, |(run x gs).getD i 0| ≤ B * B := fun i =>
      (ih i).trans (le_mul_of_one_le_right (by omega) (by omega))
    rcases getD_append_singleton (run x gs) _ j with h | h <;> rw [h]
    · exact hle j
    · cases g with
      | var i =>
        simp only [AlgGate.eval]
        exact (hx i).trans (by nlinarith)
      | one => simp only [AlgGate.eval, abs_one]; nlinarith
      | add a b =>
        simp only [AlgGate.eval]
        refine (abs_add_le _ _).trans ?_
        nlinarith [ih a, ih b]
      | sub a b =>
        simp only [AlgGate.eval]
        refine (abs_sub _ _).trans ?_
        nlinarith [ih a, ih b]
      | mul a b =>
        simp only [AlgGate.eval, abs_mul]
        exact mul_le_mul (ih a) (ih b) (abs_nonneg _) (by omega)

/-- **Value bound** [AB09, §7.2.3, p.130]: on integer inputs of absolute value at most
`X ≥ 2`, a size-`m` circuit outputs a value of absolute value at most `X^{2^m}`. -/
theorem abs_eval_le_pow (C : AlgCircuit n) (x : Fin n → ℤ) (X : ℕ) (hX : 2 ≤ X)
    (hx : ∀ i, |x i| ≤ X) : |C.eval x| ≤ (X : ℤ) ^ 2 ^ C.size :=
  abs_run_le x X hX hx C.gates _

/-- The value bound for every `X ≥ 1`: `|C(x)| ≤ (2X)^{2^m}` (apply `abs_eval_le_pow` to
`2X ≥ 2`). -/
theorem abs_eval_le (C : AlgCircuit n) (x : Fin n → ℤ) (X : ℕ) (hX : 1 ≤ X)
    (hx : ∀ i, |x i| ≤ X) : |C.eval x| ≤ (2 * X : ℤ) ^ 2 ^ C.size := by
  have h := abs_eval_le_pow C x (2 * X) (by omega) fun i => (hx i).trans (by push_cast; omega)
  push_cast at h
  exact h

/-! ### Identity testing reduces to ZEROP -/

/-- Running `gs` followed by `hs` re-indexed past `gs` gives the two value lists side by
side. -/
theorem run_append_shift (x : Fin n → R) (gs hs : List (AlgGate n)) :
    run x (gs ++ hs.map (AlgGate.shift gs.length)) = run x gs ++ run x hs := by
  have key : ∀ (vs ws : List R) (hs : List (AlgGate n)),
      (hs.map (AlgGate.shift vs.length)).foldl (fun us g => us ++ [g.eval x us]) (vs ++ ws) =
        vs ++ hs.foldl (fun us g => us ++ [g.eval x us]) ws := by
    intro vs ws hs
    induction hs generalizing ws with
    | nil => rfl
    | cons h hs ih =>
      simp only [List.map_cons, List.foldl_cons, AlgGate.eval_shift, List.append_assoc]
      exact ih _
  have := key (run x gs) [] hs
  rw [length_run, List.append_nil] at this
  rw [run, List.foldl_append]
  exact this

/-- The circuit `D = C − C′` of [AB09, §7.2.3]: `C`'s nodes, then `C′`'s nodes re-indexed,
then one `−` node. -/
def subCircuit (C C' : AlgCircuit n) : AlgCircuit n :=
  ⟨C.gates ++ C'.gates.map (AlgGate.shift C.size) ++
    [AlgGate.sub (C.size - 1) (C.size + C'.size - 1)]⟩

/-- `C − C′` has size `|C| + |C′| + 1`. -/
theorem size_subCircuit (C C' : AlgCircuit n) :
    (C.subCircuit C').size = C.size + C'.size + 1 := by
  simp [subCircuit, size]
  omega

/-- `D(x) = C(x) − C′(x)` for nonempty `C, C′`. -/
theorem eval_subCircuit {C C' : AlgCircuit n} (hC : C.gates ≠ []) (hC' : C'.gates ≠ [])
    (x : Fin n → R) : (C.subCircuit C').eval x = C.eval x - C'.eval x := by
  have h1 : 0 < C.gates.length := List.length_pos_of_ne_nil hC
  have h2 : 0 < C'.gates.length := List.length_pos_of_ne_nil hC'
  have hrun := run_append_shift x C.gates C'.gates
  have hl1 := length_run x C.gates
  have hl2 := length_run x C'.gates
  unfold eval subCircuit size
  simp only [List.length_append, List.length_map, List.length_singleton]
  rw [run_append_singleton, hrun]
  have hidx : C.gates.length + C'.gates.length + 1 - 1 =
      (run x C.gates ++ run x C'.gates).length := by simp [hl1, hl2]
  rw [hidx, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
  simp only [AlgGate.eval]
  rw [List.getD_append _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl1]
  congr 2
  omega

/-- `C − C′` is well formed when `C` and `C′` are.

**Proof sketch.** A node of `C` keeps its references; a node of `C′` at position `i` now
sits at `|C| + i` and reads `j + |C|` with `j < i`; the final `−` node reads `|C| − 1` and
`|C| + |C′| − 1`, both below its position `|C| + |C′|`. -/
theorem WellFormed.subCircuit {C C' : AlgCircuit n} (hC : C.WellFormed)
    (hC' : C'.WellFormed) : (C.subCircuit C').WellFormed := by
  refine ⟨by simp [AlgCircuit.subCircuit], fun i hi => ?_⟩
  simp only [AlgCircuit.subCircuit, List.length_append, List.length_map,
    List.length_singleton] at hi
  simp only [AlgCircuit.subCircuit]
  have h1 : 0 < C.size := List.length_pos_of_ne_nil hC.1
  have h2 : 0 < C'.size := List.length_pos_of_ne_nil hC'.1
  simp only [size] at h1 h2
  rcases lt_or_ge i (C.gates.length + C'.gates.length) with hi' | hi'
  · rw [List.getElem_append_left (by simp; omega)]
    rcases lt_or_ge i C.gates.length with hi'' | hi''
    · rw [List.getElem_append_left hi'']
      exact hC.2 i hi''
    · rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map]
      have := hC'.2 (i - C.gates.length) (by omega)
      generalize C'.gates[i - C.gates.length] = g at this
      cases g <;> simp_all [AlgGate.refsBelow, AlgGate.shift, size] <;> omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp [AlgGate.refsBelow, size]
    omega

/-- **PIT reduces to ZEROP** [AB09, §7.2.3]: `D = C − C′` computes the polynomial
`C − C′`, so `C` and `C′` compute the same polynomial iff `D` computes zero. -/
theorem toMvPolynomial_subCircuit {C C' : AlgCircuit n} (hC : C.gates ≠ [])
    (hC' : C'.gates ≠ []) :
    (C.subCircuit C').toMvPolynomial = C.toMvPolynomial - C'.toMvPolynomial :=
  eval_subCircuit hC hC' X

/-- [AB09, §7.2.3]: `C ≡ C′` iff `C − C′ ∈ ZEROP` (at the polynomial level). -/
theorem toMvPolynomial_eq_iff_subCircuit {C C' : AlgCircuit n} (hC : C.gates ≠ [])
    (hC' : C'.gates ≠ []) :
    C.toMvPolynomial = C'.toMvPolynomial ↔ (C.subCircuit C').toMvPolynomial = 0 := by
  rw [toMvPolynomial_subCircuit hC hC', sub_eq_zero]

end AlgCircuit

/-! ### Encoding and the language ZEROP -/

open BoolCircuit (encodeNat decodeNat decodeNat_encodeNat)

namespace AlgGate

variable {n : ℕ}

/-- The code of a node: a 3-bit tag, then its indices in unary. -/
def encode : AlgGate n → List Bool
  | var i => [false, false, false] ++ encodeNat i
  | one => [false, false, true]
  | add j k => [false, true, false] ++ encodeNat j ++ encodeNat k
  | sub j k => [false, true, true] ++ encodeNat j ++ encodeNat k
  | mul j k => [true, false, false] ++ encodeNat j ++ encodeNat k

/-- Read two unary numbers and build a binary node from them. -/
def parseBin (mk : ℕ → ℕ → AlgGate n) (l : List Bool) : Option (AlgGate n × List Bool) :=
  match decodeNat l with
  | none => none
  | some (j, l₁) => match decodeNat l₁ with
    | none => none
    | some (k, l₂) => some (mk j k, l₂)

/-- Read one node code off the front of a string. -/
def parse (n : ℕ) : List Bool → Option (AlgGate n × List Bool)
  | false :: false :: false :: l => match decodeNat l with
    | none => none
    | some (i, l') => if h : i < n then some (var ⟨i, h⟩, l') else none
  | false :: false :: true :: l => some (one, l)
  | false :: true :: false :: l => parseBin add l
  | false :: true :: true :: l => parseBin sub l
  | true :: false :: false :: l => parseBin mul l
  | _ => none

/-- Parsing a node code returns the node and the untouched rest. -/
theorem parse_encode (g : AlgGate n) (r : List Bool) :
    parse n (g.encode ++ r) = some (g, r) := by
  cases g <;> simp [encode, parse, parseBin, decodeNat_encodeNat]

end AlgGate

namespace AlgCircuit

variable {n : ℕ}

/-- The code of a node list: each node behind a `1`, then a final `0`. -/
def encodeGates : List (AlgGate n) → List Bool
  | [] => [false]
  | g :: gs => true :: (g.encode ++ encodeGates gs)

/-- Read a node list (fuel bounds the number of nodes); the string must end exactly. -/
def parseGates (n : ℕ) : ℕ → List Bool → Option (List (AlgGate n))
  | _, [false] => some []
  | f + 1, true :: l => match AlgGate.parse n l with
    | none => none
    | some (g, l') => (parseGates n f l').map (g :: ·)
  | _, _ => none

/-- The binary encoding of a circuit `⟨n, C⟩`: `n` in unary, then its node list. -/
def encode (c : (n : ℕ) × AlgCircuit n) : List Bool :=
  encodeNat c.1 ++ encodeGates c.2.gates

/-- Decode a circuit: parse, then accept only if the parse re-encodes to the input. -/
def decode (x : List Bool) : Option ((n : ℕ) × AlgCircuit n) :=
  match decodeNat x with
  | none => none
  | some (n, l) => match parseGates n l.length l with
    | none => none
    | some gs => if encode ⟨n, ⟨gs⟩⟩ = x then some ⟨n, ⟨gs⟩⟩ else none

/-- A node list's code is longer than the list. -/
theorem length_encodeGates (gs : List (AlgGate n)) : gs.length < (encodeGates gs).length := by
  induction gs with
  | nil => simp [encodeGates]
  | cons g gs ih => simp [encodeGates]; omega

/-- Parsing a node-list code, with enough fuel, returns the list. -/
theorem parseGates_encodeGates (gs : List (AlgGate n)) (f : ℕ) (hf : gs.length ≤ f) :
    parseGates n f (encodeGates gs) = some gs := by
  induction gs generalizing f with
  | nil => simp [encodeGates, parseGates]
  | cons g gs ih =>
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [encodeGates, parseGates, AlgGate.parse_encode]
    rw [ih f (by simp at hf; omega)]
    rfl

/-- Decoding inverts encoding. -/
theorem decode_encode (c : (n : ℕ) × AlgCircuit n) : decode (encode c) = some c := by
  obtain ⟨n, ⟨gs⟩⟩ := c
  have hp : parseGates n (encodeGates gs).length (encodeGates gs) = some gs :=
    parseGates_encodeGates gs _ (length_encodeGates gs).le
  simp [decode, encode, decodeNat_encodeNat, hp]

/-- Only canonical strings decode. -/
theorem encode_of_decode {x : List Bool} {c : (n : ℕ) × AlgCircuit n}
    (h : decode x = some c) : encode c = x := by
  unfold decode at h
  split at h
  · cases h
  · split at h
    · cases h
    · split_ifs at h with he
      cases h
      exact he

/-- `decode x = some c` iff `x` is the code of `c`. -/
theorem decode_eq_some_iff {x : List Bool} {c : (n : ℕ) × AlgCircuit n} :
    decode x = some c ↔ encode c = x :=
  ⟨encode_of_decode, fun h => h ▸ decode_encode c⟩

/-- The number of variables and the size are each below the encoding length. -/
theorem lt_length_encode (c : (n : ℕ) × AlgCircuit n) :
    c.1 + c.2.size < (encode c).length := by
  have := length_encodeGates c.2.gates
  simp [encode, encodeNat, size]
  omega

end AlgCircuit

/-- **ZEROP** [AB09, §7.2.3]: the (encodings of) well-formed algebraic circuits that compute
the identically zero polynomial. -/
def ZEROP : Language Bool :=
  {x | ∃ c : (n : ℕ) × AlgCircuit n,
    AlgCircuit.encode c = x ∧ c.2.WellFormed ∧ c.2.toMvPolynomial = 0}

/-- Membership in `ZEROP` through the decoder. -/
theorem mem_ZEROP_iff (x : List Bool) :
    x ∈ ZEROP ↔ ∃ c : (n : ℕ) × AlgCircuit n,
      AlgCircuit.decode x = some c ∧ c.2.WellFormed ∧ c.2.toMvPolynomial = 0 := by
  constructor
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, AlgCircuit.decode_eq_some_iff.mpr h1, h2⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨c, AlgCircuit.decode_eq_some_iff.mp h1, h2⟩

end Randomized
