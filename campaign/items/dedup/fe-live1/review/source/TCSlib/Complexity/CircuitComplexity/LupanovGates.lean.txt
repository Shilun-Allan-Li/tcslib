/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.CircuitComplexity.BookModelBasics

/-!
# The gate list of the `O(2ⁿ / n)` circuit ([AB09, Ex 6.1])

The construction behind `Lupanov.lean`, as one explicit gate list over the book's model
`BoolCircuit.DAGCircuit` ([AB09, Def 6.1]).  Fix `k ≤ n`, write `m = n - k`, and split the
input into `y = x_0 … x_{m-1}` and `z = x_m … x_{n-1}`.  Gate `j` sits at vertex `n + j`;
the regions are

* `[0, n)`: the negations `¬xⱼ`;
* `[n, oZ)`: the **`y`-heap**, a prefix-sharing tree of minterms: node `q ∈ [1, 2ᵐ⁺¹)` is
  the constant `1` for `q = 1`, and otherwise the `∧` of node `q / 2` with the literal
  setting variable `⌊log₂ q⌋ - 1` to the last bit of `q`; node `q` is true iff the bits
  read so far, prefixed by a `1`, spell `q` (`heapPath`);
* `[oZ, oF)`: the same heap over `z`, with `2ᵏ⁺¹ - 1` nodes;
* `[oF, oC)`: the **function table**: entry `t < 2^(2ᵏ)` computes the function of `z`
  whose truth table is the binary expansion of `t`, as entry `t - 2^⌊log₂ t⌋` `∨` the
  `z`-minterm `⌊log₂ t⌋` (one gate per function of `z`);
* `[oC, total)`: the **combining gates**: gate `p < 2ᵐ` is the `y`-minterm `p` `∧` the
  table entry `code p` of the function `z ↦ f(y = p, z)`;

followed by a balanced `∨`-tree over the combining gates (`emitTree`).

## Main definitions

* `BoolCircuit.Lupanov.heapPath` — the bits of `x` from position `o`, read as a binary
  number behind a leading `1`; `BoolCircuit.Lupanov.ofBits` — a bit list as a number.
* `BoolCircuit.Lupanov.heapGate`, `funcGate`, `combGate`, `gateAt`, `gates`, `lupGates`
  — the gates of each region, the whole list, and the list with the output tree.

## Main results

* `BoolCircuit.Lupanov.gates_acyclic`, `gateAt_faninTwo` — the list is a fan-in-two DAG.
* `BoolCircuit.Lupanov.value_heap`, `value_func`, `value_comb` — what each region computes.

## Implementation notes

The literal vertices (`litV`, `value_litV`) and the leading `¬xᵢ` region repeat
`BookModelBasics.litVertex` / `negInputGates` / `vertexValue_litVertex`, but indexed by `ℕ`
rather than `Fin n`: the minterm heaps compute variable indices arithmetically (from heap
positions), and the `ℕ`-indexed form avoids carrying bound proofs through that arithmetic.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, p. 108; Exercise 6.1.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

namespace Lupanov

variable {n : ℕ}

/-! ## Bit bookkeeping -/

/-- Input bit `i`, read as `false` out of range. -/
def xget (x : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then x ⟨i, h⟩ else false

/-- The heap path of the bits `x_o, x_{o+1}, …`: `1` followed by the first `l` of them, read
as a binary number (most significant first). -/
def heapPath (x : Fin n → Bool) (o : ℕ) : ℕ → ℕ
  | 0 => 1
  | l + 1 => 2 * heapPath x o l + (xget x (o + l)).toNat

/-- The heap path of length `l` lies in `[2ˡ, 2ˡ⁺¹)`. -/
theorem heapPath_bounds (x : Fin n → Bool) (o : ℕ) :
    ∀ l, 2 ^ l ≤ heapPath x o l ∧ heapPath x o l < 2 ^ (l + 1)
  | 0 => by simp [heapPath]
  | l + 1 => by
    have ih := heapPath_bounds x o l
    have hb := Bool.toNat_le (xget x (o + l))
    simp only [heapPath, pow_succ] at ih ⊢
    omega

/-- The heap path of length `l` has binary logarithm `l`. -/
theorem log_heapPath (x : Fin n → Bool) (o l : ℕ) : Nat.log 2 (heapPath x o l) = l :=
  Nat.log_eq_of_pow_le_of_lt_pow (heapPath_bounds x o l).1 (heapPath_bounds x o l).2

/-- Bit `l - 1 - i` of the heap path of length `l` is the input bit `x_{o+i}`. -/
theorem testBit_heapPath (x : Fin n → Bool) (o : ℕ) :
    ∀ l i, i < l → (heapPath x o l).testBit (l - 1 - i) = xget x (o + i)
  | 0, i, h => absurd h (Nat.not_lt_zero _)
  | l + 1, i, h => by
    simp only [heapPath]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · obtain ⟨j, hj⟩ : ∃ j, l + 1 - 1 - i = j + 1 := ⟨l - 1 - i, by omega⟩
      rw [hj, Nat.testBit_succ, ← testBit_heapPath x o l i h]
      congr 1
      · cases xget x (o + l) <;> (simp; try omega)
      · omega
    · rw [show i + 1 - 1 - i = 0 by omega, Nat.testBit_zero]
      cases xget x (o + i) <;> simp

/-- `testBit (2ᴸ + t) r` for `t < 2ᴸ`: bit `L` is set and the others are those of `t`. -/
theorem testBit_two_pow_add_of_lt {L t : ℕ} (ht : t < 2 ^ L) (r : ℕ) :
    (2 ^ L + t).testBit r = (t.testBit r || decide (r = L)) := by
  rcases lt_trichotomy r L with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [h.ne]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ht]; simp
  · have h1 : 2 ^ r ≥ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) h
    rw [Nat.testBit_lt_two_pow (by rw [pow_succ] at h1; omega),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) h.le))]
    simp [h.ne']

/-- A bit list read as a binary number, least significant bit first. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: l => 2 * ofBits l + b.toNat

/-- Bit `i` of `ofBits l` is the `i`-th entry of `l`. -/
theorem testBit_ofBits : ∀ (l : List Bool) (i : ℕ), (ofBits l).testBit i = l.getD i false
  | [], i => by simp [ofBits]
  | b :: l, 0 => by cases b <;> simp [ofBits]
  | b :: l, i + 1 => by
    rw [Nat.testBit_succ, ofBits, List.getD_cons_succ, ← testBit_ofBits l i]
    congr 1
    cases b <;> (simp; try omega)

/-- `ofBits l < 2 ^ |l|`. -/
theorem ofBits_lt : ∀ l : List Bool, ofBits l < 2 ^ l.length
  | [] => by simp [ofBits]
  | b :: l => by
    have := ofBits_lt l
    have := Bool.toNat_le b
    simp only [ofBits, List.length_cons, pow_succ]
    omega

/-! ## The gate list -/

/-- The vertex of the literal `xᵢ` (if `b`) or `¬xᵢ` (if not `b`), the negation of `xᵢ`
being gate `i` (vertex `n + i`). -/
def litV (n i : ℕ) (b : Bool) : ℕ := if b then i else n + i

/-- Node `q ≥ 1` of a prefix-sharing minterm heap over the variables `x_o, x_{o+1}, …`,
stored at vertex `base + (q - 1)`: the root `q = 1` is the constant `1`, and node `q ≥ 2`
is the `∧` of its parent `q / 2` with the literal fixing variable `o + ⌊log₂ q⌋ - 1` to
the last bit of `q`. -/
def heapGate (n base o q : ℕ) : DAGGate :=
  if q ≤ 1 then ⟨.and, []⟩
  else ⟨.and, [base + (q / 2 - 1), litV n (o + (Nat.log 2 q - 1)) (q % 2 == 1)]⟩

/-- Gate `t` of the table of all functions of the `z`-variables, stored at vertex
`fBase + t` and computing the function whose truth table is the binary expansion of `t`:
`t = 0` is the constant `0`, and `t ≥ 1` is the `∨` of the function `t - 2ᴸ`
(`L = ⌊log₂ t⌋`) with the `L`-th `z`-minterm (heap leaf `2ᵏ + L`, at `zBase + 2ᵏ + L - 1`). -/
def funcGate (fBase zBase k t : ℕ) : DAGGate :=
  if t = 0 then ⟨.or, []⟩
  else ⟨.or, [fBase + (t - 2 ^ Nat.log 2 t), zBase + (2 ^ k + Nat.log 2 t - 1)]⟩

/-- The `p`-th combining gate: the `∧` of the `y`-minterm `p` (heap leaf `2ᵐ + p`) with the
`z`-function `code p`. -/
def combGate (yBase fBase m : ℕ) (code : ℕ → ℕ) (p : ℕ) : DAGGate :=
  ⟨.and, [yBase + (2 ^ m + p - 1), fBase + code p]⟩

/-- Gate index where the `z`-minterm heap starts (after `n` negations and the
`2ᵐ⁺¹ - 1` nodes of the `y`-heap, `m = n - k`). -/
def oZ (n k : ℕ) : ℕ := n + (2 ^ (n - k + 1) - 1)

/-- Gate index where the table of `z`-functions starts. -/
def oF (n k : ℕ) : ℕ := oZ n k + (2 ^ (k + 1) - 1)

/-- Gate index where the combining gates start. -/
def oC (n k : ℕ) : ℕ := oF n k + 2 ^ 2 ^ k

/-- Number of gates before the final `∨`-tree. -/
def total (n k : ℕ) : ℕ := oC n k + 2 ^ (n - k)

/-- The input whose `y`-part has heap path `2ᵐ + p` and whose `z`-part has heap path
`2ᵏ + r` (`m = n - k`). -/
def assemble (n k p r : ℕ) : Fin n → Bool := fun i =>
  if (i : ℕ) < n - k then (2 ^ (n - k) + p).testBit (n - k - 1 - i)
  else (2 ^ k + r).testBit (k - 1 - (i - (n - k)))

/-- The index in the function table of the `z`-function `r ↦ f (assemble p r)`. -/
def code (f : (Fin n → Bool) → Bool) (k p : ℕ) : ℕ :=
  ofBits ((List.range (2 ^ k)).map fun r => f (assemble n k p r))

/-- Gate `j` of the construction, dispatched on the region `j` falls in. -/
def gateAt (f : (Fin n → Bool) → Bool) (k j : ℕ) : DAGGate :=
  if j < n then ⟨.not, [j]⟩
  else if j < oZ n k then heapGate n (n + n) 0 (j - n + 1)
  else if j < oF n k then heapGate n (n + oZ n k) (n - k) (j - oZ n k + 1)
  else if j < oC n k then funcGate (n + oF n k) (n + oZ n k) k (j - oF n k)
  else combGate (n + n) (n + oF n k) (n - k) (code f k) (j - oC n k)

/-- All gates before the final `∨`-tree. -/
def gates (f : (Fin n → Bool) → Bool) (k : ℕ) : List DAGGate :=
  (List.range (total n k)).map (gateAt f k)

/-- The roots of the combining gates. -/
def combRoots (n k : ℕ) : List ℕ := (List.range (2 ^ (n - k))).map fun p => n + oC n k + p

/-- The full gate list and output: the gates followed by a balanced `∨`-tree over the
combining gates. -/
def lupGates (f : (Fin n → Bool) → Bool) (k : ℕ) : List DAGGate × ℕ :=
  emitTree n .or (combRoots n k) (gates f k)

/-- The construction has `total n k` gates before the `∨`-tree. -/
@[simp] theorem length_gates (f : (Fin n → Bool) → Bool) (k : ℕ) :
    (gates f k).length = total n k := by simp [gates]

/-- Gate `j` of the list is `gateAt f k j`. -/
theorem getElem_gates (f : (Fin n → Bool) → Bool) (k j : ℕ) (h : j < (gates f k).length) :
    (gates f k)[j] = gateAt f k j := by simp [gates]

/-! ## Acyclicity and fan-in -/

/-- `2^(a+1) = 2 · 2^a`. -/
private theorem two_pow_succ_eq (a : ℕ) : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring

/-- A literal vertex is at most `n + i`. -/
private theorem litV_le (i : ℕ) (b : Bool) : litV n i b ≤ n + i := by unfold litV; split_ifs <;> omega

/-- Below `2^(a+1)` the binary logarithm is at most `a`. -/
private theorem log_le_of_lt_two_pow_succ {q a : ℕ} (h : q < 2 ^ (a + 1)) : Nat.log 2 q ≤ a := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hq.ne' h)

/-- A fan-in-zero `∧`/`∨` gate is admissible in a fan-in-two circuit. -/
private theorem nil_faninTwo {k : GateKind} (hk : k ≠ .not) : (⟨k, []⟩ : DAGGate).FaninTwo :=
  ⟨⟨by simp, fun h => absurd h hk⟩, by simp⟩

/-- An `∧`/`∨` gate reading two distinct vertices is admissible in a fan-in-two circuit. -/
private theorem pair_faninTwo {k : GateKind} (hk : k ≠ .not) {a b : ℕ} (hab : a ≠ b) :
    (⟨k, [a, b]⟩ : DAGGate).FaninTwo :=
  ⟨⟨by simpa using hab, fun h => absurd h hk⟩, by simp⟩

/-- Every gate reads only earlier vertices.

**Proof sketch.** By region.  A negation reads its input.  A heap node `q ≥ 2` reads its
parent `q / 2 < q` in the same heap and a literal (an input or a negation, below `2n`, the
variable index being at most `n`).  A table gate `t ≥ 1` reads the earlier table entry
`t - 2^⌊log₂ t⌋` and a `z`-heap leaf, which lies before the table since
`⌊log₂ t⌋ < 2ᵏ`.  A combining gate reads a `y`-heap leaf and the table entry `code p`,
which is below `2^(2ᵏ)` (`ofBits_lt`). -/
theorem gateAt_args_lt (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (j : ℕ)
    (hj : j < total n k) : ∀ a ∈ (gateAt f k j).args, a < n + j := by
  have e1 := two_pow_succ_eq (n - k)
  have e2 := two_pow_succ_eq k
  have p1 : 1 ≤ 2 ^ (n - k) := Nat.one_le_two_pow
  have p2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  unfold gateAt
  simp only [total, oC, oF, oZ] at hj ⊢
  split_ifs with h1 h2 h3 h4
  · intro a ha; simp only [List.mem_singleton] at ha; omega
  · intro a ha
    unfold heapGate at ha
    split_ifs at ha with hq
    · simp at ha
    · have hl := log_le_of_lt_two_pow_succ (q := j - n + 1) (a := n - k) (by omega)
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl
      · omega
      · have := litV_le (n := n) (0 + (Nat.log 2 (j - n + 1) - 1)) ((j - n + 1) % 2 == 1)
        omega
  · intro a ha
    unfold heapGate at ha
    split_ifs at ha with hq
    · simp at ha
    · have hl := log_le_of_lt_two_pow_succ
        (q := j - (n + (2 ^ (n - k + 1) - 1)) + 1) (a := k) (by omega)
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl
      · omega
      · have := litV_le (n := n) (n - k + (Nat.log 2
          (j - (n + (2 ^ (n - k + 1) - 1)) + 1) - 1))
          ((j - (n + (2 ^ (n - k + 1) - 1)) + 1) % 2 == 1)
        omega
  · intro a ha
    unfold funcGate at ha
    split_ifs at ha with ht
    · simp at ha
    · set t := j - (n + (2 ^ (n - k + 1) - 1) + (2 ^ (k + 1) - 1)) with htdef
      have hl : Nat.log 2 t < 2 ^ k := Nat.log_lt_of_lt_pow ht (by omega)
      have hp : 1 ≤ 2 ^ Nat.log 2 t := Nat.one_le_two_pow
      have hp' : 2 ^ Nat.log 2 t ≤ t := Nat.pow_log_le_self 2 ht
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl <;> omega
  · intro a ha
    simp only [combGate, List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · omega
    · have := ofBits_lt ((List.range (2 ^ k)).map fun r => f (assemble n k
        (j - (n + (2 ^ (n - k + 1) - 1) + (2 ^ (k + 1) - 1) + 2 ^ 2 ^ k)) r))
      simp only [List.length_map, List.length_range] at this
      simp only [code]
      omega

/-- Every gate is admissible in a fan-in-two circuit.

**Proof sketch.** Every gate reads at most two vertices.  Negations read one; constants
none; the two inputs of every binary gate lie in different regions (a heap node and a
literal, a table entry and a `z`-heap leaf, a `y`-heap leaf and a table entry), hence are
distinct. -/
theorem gateAt_faninTwo (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (j : ℕ)
    (hj : j < total n k) : (gateAt f k j).FaninTwo := by
  have e1 := two_pow_succ_eq (n - k)
  have e2 := two_pow_succ_eq k
  have p1 : 1 ≤ 2 ^ (n - k) := Nat.one_le_two_pow
  have p2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  unfold gateAt
  simp only [total, oC, oF, oZ] at hj ⊢
  split_ifs with h1 h2 h3 h4
  · exact ⟨⟨by simp, fun _ => rfl⟩, by simp⟩
  · unfold heapGate
    split_ifs with hq
    · exact nil_faninTwo (by decide)
    · have hl := log_le_of_lt_two_pow_succ (q := j - n + 1) (a := n - k) (by omega)
      have hl2 : 1 ≤ Nat.log 2 (j - n + 1) := Nat.log_pos (by norm_num) (by omega)
      have := litV_le (n := n) (0 + (Nat.log 2 (j - n + 1) - 1)) ((j - n + 1) % 2 == 1)
      exact pair_faninTwo (by decide) (by omega)
  · unfold heapGate
    split_ifs with hq
    · exact nil_faninTwo (by decide)
    · have hl := log_le_of_lt_two_pow_succ
        (q := j - (n + (2 ^ (n - k + 1) - 1)) + 1) (a := k) (by omega)
      have := litV_le (n := n) (n - k + (Nat.log 2
          (j - (n + (2 ^ (n - k + 1) - 1)) + 1) - 1))
          ((j - (n + (2 ^ (n - k + 1) - 1)) + 1) % 2 == 1)
      exact pair_faninTwo (by decide) (by omega)
  · unfold funcGate
    split_ifs with ht
    · exact nil_faninTwo (by decide)
    · set t := j - (n + (2 ^ (n - k + 1) - 1) + (2 ^ (k + 1) - 1)) with htdef
      have hl : Nat.log 2 t < 2 ^ k := Nat.log_lt_of_lt_pow ht (by omega)
      exact pair_faninTwo (by decide) (by omega)
  · exact pair_faninTwo (by decide) (by omega)

/-- The gate list reads only earlier vertices. -/
theorem gates_acyclic (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) :
    GatesAcyclic n (gates f k) := by
  intro j hj a ha
  rw [getElem_gates] at ha
  exact gateAt_args_lt f k hk j (by simpa using hj) a ha

/-! ## Region lemmas -/

/-- The region offsets, in closed form, with the positivity facts `omega` needs. -/
theorem offsets (n k : ℕ) : oZ n k + 1 = n + 2 * 2 ^ (n - k) ∧
    oF n k + 1 = oZ n k + 2 * 2 ^ k ∧ oC n k = oF n k + 2 ^ 2 ^ k ∧
    total n k = oC n k + 2 ^ (n - k) ∧ 1 ≤ 2 ^ (n - k) ∧ 1 ≤ 2 ^ k ∧ 1 ≤ 2 ^ 2 ^ k := by
  have e1 := two_pow_succ_eq (n - k)
  have e2 := two_pow_succ_eq k
  have p1 : 1 ≤ 2 ^ (n - k) := Nat.one_le_two_pow
  have p2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have p3 : 1 ≤ 2 ^ 2 ^ k := Nat.one_le_two_pow
  unfold total oC oF oZ
  omega

/-- The gates at indices `n + (q - 1)` are the `y`-heap (variables `x_0, …, x_{n-k-1}`). -/
theorem gateAt_y (f : (Fin n → Bool) → Bool) (k q : ℕ) (hq1 : 1 ≤ q)
    (hq : q < 2 ^ (n - k + 1)) : gateAt f k (n + (q - 1)) = heapGate n (n + n) 0 q := by
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  rw [two_pow_succ_eq] at hq
  have c1 : ¬ n + (q - 1) < n := by omega
  have c2 : n + (q - 1) < oZ n k := by omega
  unfold gateAt
  rw [if_neg c1, if_pos c2]
  congr 1; omega

/-- The gates at indices `oZ + (q - 1)` are the `z`-heap (variables `x_{n-k}, …, x_{n-1}`). -/
theorem gateAt_z (f : (Fin n → Bool) → Bool) (k q : ℕ) (hq1 : 1 ≤ q)
    (hq : q < 2 ^ (k + 1)) :
    gateAt f k (oZ n k + (q - 1)) = heapGate n (n + oZ n k) (n - k) q := by
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  rw [two_pow_succ_eq] at hq
  have c1 : ¬ oZ n k + (q - 1) < n := by omega
  have c2 : ¬ oZ n k + (q - 1) < oZ n k := by omega
  have c3 : oZ n k + (q - 1) < oF n k := by omega
  unfold gateAt
  rw [if_neg c1, if_neg c2, if_pos c3]
  congr 1; omega

/-- The gates at indices `oF + t`, `t < 2^(2ᵏ)`, are the function table. -/
theorem gateAt_f (f : (Fin n → Bool) → Bool) (k t : ℕ) (ht : t < 2 ^ 2 ^ k) :
    gateAt f k (oF n k + t) = funcGate (n + oF n k) (n + oZ n k) k t := by
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  have c1 : ¬ oF n k + t < n := by omega
  have c2 : ¬ oF n k + t < oZ n k := by omega
  have c3 : ¬ oF n k + t < oF n k := by omega
  have c4 : oF n k + t < oC n k := by omega
  unfold gateAt
  rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4]
  congr 1; omega

/-- The gates at indices `oC + p` are the combining gates. -/
theorem gateAt_c (f : (Fin n → Bool) → Bool) (k p : ℕ) :
    gateAt f k (oC n k + p) = combGate (n + n) (n + oF n k) (n - k) (code f k) p := by
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  have c1 : ¬ oC n k + p < n := by omega
  have c2 : ¬ oC n k + p < oZ n k := by omega
  have c3 : ¬ oC n k + p < oF n k := by omega
  have c4 : ¬ oC n k + p < oC n k := by omega
  unfold gateAt
  rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4]
  congr 1; omega

/-! ## Values -/

/-- The value of gate vertex `n + j` is the gate evaluated on all vertex values, provided it
reads only earlier vertices. -/
private theorem vertexValue_gate (G : List DAGGate) (x : Fin n → Bool) {j : ℕ} (hj : j < G.length)
    (hargs : ∀ a ∈ G[j].args, a < n + j) :
    vertexValue G x (n + j) = G[j].eval (runWith DAGGate.eval G (List.ofFn x)) := by
  unfold vertexValue
  have h := runWith_getD_gate DAGGate.eval G (List.ofFn x) hj false
  rw [List.length_ofFn] at h
  rw [h]
  apply DAGGate.eval_congr
  intro a ha
  exact runWith_getD_take _ _ _ hj.le (by rw [List.length_ofFn]; exact hargs a ha) false

/-- The value of gate `j` of the construction. -/
theorem value_gateAt (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool)
    {j : ℕ} (hj : j < total n k) :
    vertexValue (gates f k) x (n + j) =
      (gateAt f k j).eval (runWith DAGGate.eval (gates f k) (List.ofFn x)) := by
  have hj' : j < (gates f k).length := by simpa using hj
  rw [vertexValue_gate _ x hj' (by rw [getElem_gates]; exact gateAt_args_lt f k hk j hj),
    getElem_gates]

/-- A binary `∧` gate is the `&&` of its two inputs. -/
private theorem eval_and_pair (a b : ℕ) (vals : List Bool) :
    (⟨.and, [a, b]⟩ : DAGGate).eval vals = (vals.getD a false && vals.getD b false) := by
  simp [DAGGate.eval]

/-- A binary `∨` gate is the `||` of its two inputs. -/
private theorem eval_or_pair (a b : ℕ) (vals : List Bool) :
    (⟨.or, [a, b]⟩ : DAGGate).eval vals = (vals.getD a false || vals.getD b false) := by
  simp [DAGGate.eval]

/-- Literal vertices carry their literal. -/
theorem value_litV (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool)
    {i : ℕ} (hi : i < n) (b : Bool) :
    vertexValue (gates f k) x (litV n i b) = (xget x i == b) := by
  have hin : vertexValue (gates f k) x i = x ⟨i, hi⟩ :=
    vertexValue_input (gates f k) x ⟨i, hi⟩
  unfold litV xget
  rw [dif_pos hi]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
    rw [value_gateAt f k hk x (by omega)]
    unfold gateAt
    rw [if_pos hi]
    simp only [DAGGate.eval, List.all_cons, List.all_nil, Bool.and_true]
    change (!vertexValue (gates f k) x i) = _
    rw [hin]; cases x ⟨i, hi⟩ <;> rfl
  · simp only [↓reduceIte]; rw [hin]; cases x ⟨i, hi⟩ <;> rfl

/-- **Minterm heaps.**  If the gates at indices `bj + (q - 1)` form a heap over the
variables `x_o, …, x_{o+L-1}`, node `q` is true exactly when the heap path of the first
`⌊log₂ q⌋` of these variables is `q`.

**Proof sketch.** Strong induction on `q`.  The root `q = 1` is the constant `1`, and the
empty heap path is `1`.  For `q ≥ 2`, `⌊log₂ q⌋ = ⌊log₂ (q/2)⌋ + 1`; node `q` is the `∧` of
node `q / 2` (true iff the shorter heap path is `q / 2`, by induction) with the literal
saying the next variable is the last bit `q mod 2` of `q`; the heap path recursion
`H' = 2H + bit` makes the conjunction equivalent to `H' = q`. -/
theorem value_heap (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool)
    (bj o L : ℕ) (hoL : o + L ≤ n)
    (hG : ∀ q, 1 ≤ q → q < 2 ^ (L + 1) → gateAt f k (bj + (q - 1)) = heapGate n (n + bj) o q)
    (hlen : bj + (2 ^ (L + 1) - 1) ≤ total n k) :
    ∀ q, 1 ≤ q → q < 2 ^ (L + 1) →
      vertexValue (gates f k) x (n + bj + (q - 1)) =
        decide (heapPath x o (Nat.log 2 q) = q) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq1 hq
  rw [add_assoc, value_gateAt f k hk x (by omega), hG q hq1 hq]
  unfold heapGate
  split_ifs with hq2
  · obtain rfl : q = 1 := by omega
    simp [DAGGate.eval, heapPath]
  · have hlog : Nat.log 2 q = Nat.log 2 (q / 2) + 1 :=
      Nat.log_of_one_lt_of_le (by norm_num) (by omega)
    have hlq : Nat.log 2 q ≤ L := log_le_of_lt_two_pow_succ hq
    rw [eval_and_pair]
    change (vertexValue (gates f k) x (n + bj + (q / 2 - 1)) &&
      vertexValue (gates f k) x (litV n _ _)) = _
    rw [ih (q / 2) (by omega) (by omega) (by omega), value_litV f k hk x (by omega), hlog,
      show Nat.log 2 (q / 2) + 1 - 1 = Nat.log 2 (q / 2) by omega]
    simp only [heapPath]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rcases Nat.mod_two_eq_zero_or_one q with hm | hm <;>
      cases xget x (o + Nat.log 2 (q / 2)) <;> simp [hm] <;> omega

/-- `⌊log₂ (2ᵃ + p)⌋ = a` for `p < 2ᵃ`. -/
private theorem log_two_pow_add {a p : ℕ} (hp : p < 2 ^ a) : Nat.log 2 (2 ^ a + p) = a :=
  Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [two_pow_succ_eq]; omega)

/-- The `y`-minterm of `p`: heap leaf `2ᵐ + p` of the `y`-heap is true iff the heap path of
`y` is `2ᵐ + p`. -/
theorem value_yleaf (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool)
    {p : ℕ} (hp : p < 2 ^ (n - k)) :
    vertexValue (gates f k) x (n + n + (2 ^ (n - k) + p - 1)) =
      decide (heapPath x 0 (n - k) = 2 ^ (n - k) + p) := by
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  have h := value_heap f k hk x n 0 (n - k) (by omega)
    (fun q hq1 hq => gateAt_y f k q hq1 hq) (by rw [two_pow_succ_eq]; omega)
    (2 ^ (n - k) + p) (by omega) (by rw [two_pow_succ_eq]; omega)
  rwa [log_two_pow_add hp] at h

/-- The `z`-minterm of `r`: heap leaf `2ᵏ + r` of the `z`-heap is true iff the heap path of
`z` is `2ᵏ + r`. -/
theorem value_zleaf (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool)
    {r : ℕ} (hr : r < 2 ^ k) :
    vertexValue (gates f k) x (n + oZ n k + (2 ^ k + r - 1)) =
      decide (heapPath x (n - k) k = 2 ^ k + r) := by
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  have h := value_heap f k hk x (oZ n k) (n - k) k (by omega)
    (fun q hq1 hq => gateAt_z f k q hq1 hq) (by rw [two_pow_succ_eq]; omega)
    (2 ^ k + r) (by omega) (by rw [two_pow_succ_eq]; omega)
  rwa [log_two_pow_add hr] at h

/-- **The function table.**  Gate `t` of the table computes bit `r` of `t`, where `r` is the
index of the `z`-part of the input.

**Proof sketch.** Strong induction on `t`.  Entry `0` is the constant `0`.  For `t ≥ 1`
write `t = 2ᴸ + t'` with `L = ⌊log₂ t⌋` and `t' < 2ᴸ`; the entry is the `∨` of entry
`t'` (bit `r` of `t'`, by induction) and the `z`-minterm `L` (true iff `r = L`), and
`testBit_two_pow_add_of_lt` says bit `r` of `2ᴸ + t'` is exactly this `∨`. -/
theorem value_func (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool) :
    ∀ t, t < 2 ^ 2 ^ k → vertexValue (gates f k) x (n + oF n k + t) =
      t.testBit (heapPath x (n - k) k - 2 ^ k) := by
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  have hz := heapPath_bounds x (n - k) k
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro ht
  rw [add_assoc, value_gateAt f k hk x (by omega), gateAt_f f k t ht]
  unfold funcGate
  split_ifs with ht0
  · subst ht0; simp [DAGGate.eval]
  · set L := Nat.log 2 t with hL
    have hL1 : 2 ^ L ≤ t := Nat.pow_log_le_self 2 ht0
    have hL2 : t < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
    have hLk : L < 2 ^ k := Nat.log_lt_of_lt_pow ht0 ht
    rw [two_pow_succ_eq] at hL2
    rw [eval_or_pair]
    change (vertexValue (gates f k) x (n + oF n k + (t - 2 ^ L)) ||
      vertexValue (gates f k) x (n + oZ n k + (2 ^ k + L - 1))) = _
    rw [ih _ (by omega) (by omega), value_zleaf f k hk x hLk]
    have ht' : t = 2 ^ L + (t - 2 ^ L) := by omega
    conv_rhs => rw [ht', testBit_two_pow_add_of_lt (by omega)]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    omega

/-- The `p`-th combining gate is the `y`-minterm of `p` and the `z`-function `code p`. -/
theorem value_comb (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool)
    {p : ℕ} (hp : p < 2 ^ (n - k)) :
    vertexValue (gates f k) x (n + oC n k + p) =
      (decide (heapPath x 0 (n - k) = 2 ^ (n - k) + p) &&
        (code f k p).testBit (heapPath x (n - k) k - 2 ^ k)) := by
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  rw [add_assoc, value_gateAt f k hk x (by omega), gateAt_c, combGate, eval_and_pair]
  change (vertexValue (gates f k) x (n + n + (2 ^ (n - k) + p - 1)) &&
    vertexValue (gates f k) x (n + oF n k + code f k p)) = _
  have hc : code f k p < 2 ^ 2 ^ k := by
    have := ofBits_lt ((List.range (2 ^ k)).map fun r => f (assemble n k p r))
    simpa only [List.length_map, List.length_range] using this
  rw [value_yleaf f k hk x hp, value_func f k hk x _ hc]

end Lupanov

end BoolCircuit
