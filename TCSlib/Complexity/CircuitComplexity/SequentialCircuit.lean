/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fin.Tuple.Basic
import TCSlib.Complexity.CircuitComplexity.DAGTransform

/-!
# Sequential circuits and unrolling

[AB09, p. 108, footnote 1]: "the circuits in silicon chips are not acyclic and use cycles
to implement memory.  However, any computation that runs on a silicon chip with `C` gates
and finishes in time `T` can be performed by a Boolean circuit of size `O(C · T)`."

We model a chip as a synchronous sequential circuit: combinational logic (a
`BoolCircuit.DAGCircuit`, [AB09, Def 6.1]) over the inputs and the current contents of `r`
registers, the registers latching designated vertices at every clock tick, so that every
cycle passes through a register.  Unrolling `T + 1` copies of the logic gives a circuit of
the book's model computing the chip's output after `T` ticks.

## Main definitions

* `BoolCircuit.SeqCircuit n r` — a chip with `n` inputs and `r` registers, with `size`
  (gates plus registers), `state` (register contents after `t` ticks) and `run` (the
  output after `T` ticks).
* `BoolCircuit.SeqCircuit.unroll` — the unrolled circuit.

## Main results

* `BoolCircuit.SeqCircuit.unroll_values`, `unroll_eval` — copy `k` of the unrolled
  circuit holds the chip's values at time `k`; the unrolled circuit computes `run T`.
* `BoolCircuit.SeqCircuit.unroll_size` — exactly `n + (T + 1) · size` vertices.
* `BoolCircuit.SeqCircuit.unroll_isWellFormed`, `unroll_isFaninTwo` — unrolling preserves
  well-formedness and fan-in two.
* `BoolCircuit.SeqCircuit.exists_dagCircuit_of_run` — the footnote, with constant `2`:
  size `≤ 2 (C T + n)` for `T ≥ 1`.

## Divergences from [AB09, p. 108, footnote 1]

* **A model had to be chosen.**  The footnote names no model of a chip; we take the
  standard synchronous one (combinational logic plus clocked registers, input held fixed,
  registers initialized to fixed values).  `C` counts gates and registers.
* **Inputs counted.**  The `O(C · T)` hides the `n` input vertices that [AB09, Def 6.1]'s
  size counts; we prove `2 (C T + n)`, exactly `n + (T + 1) C`.
* **Register copies.**  The register values at time `k ≥ 1` are identity gates (fan-in-one
  `∧`) reading the latched vertices of copy `k - 1`; at time `0` they are constants
  (fan-in-zero gates).  Both are gates of the model (see `DAGCircuit.lean`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, p. 108, footnote 1.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-- A synchronous sequential circuit ("silicon chip") with `n` inputs and `r` registers.
Its combinational logic is a DAG circuit `comb` over `n + r` sources — the inputs, then the
current register contents — so every cycle of the chip passes through a register.  At each
clock tick register `j` latches the value of vertex `next j`; the chip's output is
`comb`'s output vertex.  [AB09, p. 108, footnote 1] -/
structure SeqCircuit (n r : ℕ) where
  /-- The combinational logic, reading the inputs (sources `0, …, n - 1`) and the current
  register contents (sources `n, …, n + r - 1`). -/
  comb : DAGCircuit (n + r)
  /-- The vertex of `comb` latched into register `j` at each tick. -/
  next : Fin r → ℕ
  /-- Each latched vertex is a vertex of `comb`. -/
  next_lt : ∀ j, next j < n + r + comb.gates.length
  /-- The register contents at time `0`. -/
  init : Fin r → Bool

namespace SeqCircuit

variable {n r : ℕ} (M : SeqCircuit n r)

/-- The size of the chip: its gates and its registers. -/
def size : ℕ := r + M.comb.gates.length

/-- The register contents after `t` clock ticks on input `x` (held fixed). -/
def state (x : Fin n → Bool) : ℕ → Fin r → Bool
  | 0 => M.init
  | t + 1 => fun j => (M.comb.values (Fin.append x (state x t))).getD (M.next j) false

/-- The chip's output after `T` clock ticks on input `x`. -/
def run (T : ℕ) (x : Fin n → Bool) : Bool :=
  M.comb.eval (Fin.append x (M.state x T))

/-! ## Unrolling -/

/-- Where block `k` of the unrolled circuit puts vertex `a` of `comb`: an input stays put,
and the other vertices (registers, then gates) are shifted by `k` blocks of `size`
gates. -/
def place (k a : ℕ) : ℕ := if a < n then a else a + k * M.size

/-- Gate `p` of the unrolled circuit, in block `k = p / size` at offset `j = p % size`:
for `j < r` the value of register `j` at time `k` (a constant at `k = 0`, otherwise an
identity gate reading the latched vertex of block `k - 1`), and for `j ≥ r` a copy of gate
`j - r` of `comb` reading block `k`. -/
def unrollGate (p : ℕ) : DAGGate :=
  if h : p % M.size < r then
    if p / M.size = 0 then ⟨if M.init ⟨p % M.size, h⟩ then .and else .or, []⟩
    else ⟨.and, [M.place (p / M.size - 1) (M.next ⟨p % M.size, h⟩)]⟩
  else
    let g := M.comb.gates.getD (p % M.size - r) ⟨.and, []⟩
    ⟨g.kind, g.args.map (M.place (p / M.size))⟩

/-- Block `k`'s vertices lie below the end of block `k`. -/
theorem place_lt {k a : ℕ} (ha : a < n + r + M.comb.gates.length) :
    M.place k a < n + (k + 1) * M.size := by
  unfold place size at *
  rw [Nat.succ_mul]
  split_ifs <;> omega

/-- Gate `p` of the unrolled circuit reads only vertices below its own, `n + p`.

**Proof sketch.** Write `p = k · size + j` with `j < size`.  A register gate of block `0`
reads nothing; one of block `k ≥ 1` reads a vertex of block `k - 1`, which lies below
`n + k · size ≤ n + p` (`place_lt`).  A copy of `comb`'s gate `j - r` reads `place k c` for
`c < n + j`, which is `c < n` or `c + k · size < n + p`. -/
theorem args_unrollGate_lt {p : ℕ} : ∀ c ∈ (M.unrollGate p).args, c < n + p := by
  intro c hc
  have hdm : M.size * (p / M.size) + p % M.size = p := Nat.div_add_mod p M.size
  rw [Nat.mul_comm] at hdm
  unfold unrollGate at hc
  by_cases hj : p % M.size < r
  · rw [dif_pos hj] at hc
    by_cases hk : p / M.size = 0
    · rw [if_pos hk] at hc; simp at hc
    · rw [if_neg hk, List.mem_singleton] at hc
      subst hc
      obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk
      rw [hk'] at hdm ⊢
      have := M.place_lt (k := k) (M.next_lt ⟨p % M.size, hj⟩)
      simp only [Nat.succ_sub_one, Nat.succ_eq_add_one] at this hdm ⊢
      omega
  · rw [dif_neg hj] at hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    rcases Nat.lt_or_ge (p % M.size - r) M.comb.gates.length with hlt | hge
    · rw [List.getD_eq_getElem _ _ hlt] at hc0
      have := M.comb.args_lt _ hlt c0 hc0
      unfold place
      split_ifs <;> omega
    · rw [List.getD_eq_default _ _ hge] at hc0
      simp at hc0

/-- The circuit computing the output of `M` after `T` ticks: `T + 1` copies of the chip's
logic, copy `k` reading the inputs and the registers' values at time `k`. -/
def unroll (T : ℕ) : DAGCircuit n where
  gates := (List.range ((T + 1) * M.size)).map M.unrollGate
  output := M.place T M.comb.output
  args_lt := fun i hi c hc => by
    simp only [List.getElem_map, List.getElem_range] at hc
    exact M.args_unrollGate_lt c hc
  output_lt := by
    simpa using M.place_lt (k := T) M.comb.output_lt

/-- Position `S k + m`, for an offset `m < S`, is offset `m` of block `k`. -/
private theorem div_mod_block {S k m : ℕ} (hm : m < S) :
    (S * k + m) / S = k ∧ (S * k + m) % S = m := by
  have hS : 0 < S := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hS, Nat.div_eq_of_lt hm, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hm]

/-- Gate `p` of the unrolled circuit is `unrollGate p`. -/
theorem getElem_unroll_gates {T p : ℕ} (hp : p < (M.unroll T).gates.length) :
    (M.unroll T).gates[p] = M.unrollGate p := by
  simp [unroll]

/-- The unrolled circuit has `T + 1` blocks of `size` gates. -/
theorem length_unroll_gates (T : ℕ) : (M.unroll T).gates.length = (T + 1) * M.size := by
  simp [unroll]

/-- Within block `k`, once the registers hold their values at time `k`, every vertex of the
copy of `comb` holds its value at time `k`.

**Proof sketch.** Strong induction on the vertex `a` of `comb`.  An input is placed at
itself and holds `xₐ`, as does `comb`'s input `a` of `Fin.append x state`.  A register is
the hypothesis.  A gate `i` is placed at gate `size · k + r + i` of the unrolled circuit,
which is `comb`'s gate `i` with inputs placed in block `k`; its inputs are earlier vertices,
which hold their time-`k` values by induction, so it computes `comb`'s gate value
(`DAGGate.eval_remap`, `DAGCircuit.values_getD_gate`). -/
private theorem unroll_block (T : ℕ) (x : Fin n → Bool) {k : ℕ} (hk : k ≤ T)
    (hreg : ∀ j : Fin r, ((M.unroll T).values x).getD (M.place k (n + j)) false =
      M.state x k j) :
    ∀ a < n + r + M.comb.gates.length,
      ((M.unroll T).values x).getD (M.place k a) false =
        (M.comb.values (Fin.append x (M.state x k))).getD a false := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha
  rcases Nat.lt_or_ge a n with h1 | h1
  · -- an input
    have hp : M.place k a = a := by simp [place, h1]
    rw [hp, (M.unroll T).values_getD_input x ⟨a, h1⟩]
    have := M.comb.values_getD_input (Fin.append x (M.state x k)) ⟨a, by omega⟩
    simp only at this
    rw [this]
    exact (Fin.append_left x (M.state x k) ⟨a, h1⟩).symm
  rcases Nat.lt_or_ge a (n + r) with h2 | h2
  · -- a register
    obtain ⟨j, rfl⟩ : ∃ j : Fin r, a = n + j := ⟨⟨a - n, by omega⟩, by simp; omega⟩
    rw [hreg j]
    have := M.comb.values_getD_input (Fin.append x (M.state x k)) (Fin.natAdd n j)
    simp only [Fin.coe_natAdd] at this
    rw [this, Fin.append_right]
  · -- a gate of `comb`
    obtain ⟨i, rfl⟩ : ∃ i, a = n + r + i := ⟨a - (n + r), by omega⟩
    have hi : i < M.comb.gates.length := by omega
    have hS : r + i < M.size := by simp [size]; omega
    have hp : M.size * k + (r + i) < (M.unroll T).gates.length := by
      rw [length_unroll_gates]
      have : M.size * k ≤ M.size * T := Nat.mul_le_mul_left _ hk
      have h3 : (T + 1) * M.size = M.size * T + M.size := by ring
      omega
    have hplace : M.place k (n + r + i) = n + (M.size * k + (r + i)) := by
      simp only [place]; rw [if_neg (by omega)]; ring
    rw [hplace, (M.unroll T).values_getD_gate x hp, getElem_unroll_gates]
    obtain ⟨hdiv, hmod⟩ := div_mod_block (k := k) hS
    have hgate : M.unrollGate (M.size * k + (r + i)) =
        ⟨M.comb.gates[i].kind, M.comb.gates[i].args.map (M.place k)⟩ := by
      unfold unrollGate
      rw [dif_neg (by rw [hmod]; omega)]
      simp only [hdiv, hmod, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi]
    rw [hgate]
    refine (DAGGate.eval_remap M.comb.gates[i] (M.place k) fun c hc => ih c ?_ ?_).trans ?_
    · have := M.comb.args_lt i hi c hc; omega
    · have := M.comb.args_lt i hi c hc; omega
    · exact (M.comb.values_getD_gate _ hi).symm

/-- Register `j` of block `k ≤ T` is the unrolled circuit's gate `size · k + j`. -/
private theorem unroll_reg (T : ℕ) (x : Fin n → Bool) {k : ℕ} (hk : k ≤ T) (j : Fin r) :
    ((M.unroll T).values x).getD (M.place k (n + j)) false =
      (if k = 0 then (⟨if M.init j then .and else .or, []⟩ : DAGGate)
        else ⟨.and, [M.place (k - 1) (M.next j)]⟩).eval ((M.unroll T).values x) := by
  have hS : (j : ℕ) < M.size := by simp [size]; omega
  have hp : M.size * k + j < (M.unroll T).gates.length := by
    rw [length_unroll_gates]
    have : M.size * k ≤ M.size * T := Nat.mul_le_mul_left _ hk
    have h3 : (T + 1) * M.size = M.size * T + M.size := by ring
    omega
  have hplace : M.place k (n + j) = n + (M.size * k + j) := by
    simp only [place]; rw [if_neg (by omega)]; ring
  rw [hplace, (M.unroll T).values_getD_gate x hp, getElem_unroll_gates]
  obtain ⟨hdiv, hmod⟩ := div_mod_block (k := k) hS
  unfold unrollGate
  rw [dif_pos (by rw [hmod]; exact j.isLt)]
  simp only [hdiv, hmod]

/-- Every vertex of block `k ≤ T` of the unrolled circuit holds the value of the
corresponding vertex of the chip at time `k`. -/
theorem unroll_values (T : ℕ) (x : Fin n → Bool) :
    ∀ k ≤ T, ∀ a < n + r + M.comb.gates.length,
      ((M.unroll T).values x).getD (M.place k a) false =
        (M.comb.values (Fin.append x (M.state x k))).getD a false := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine M.unroll_block T x hk fun j => ?_
    rw [M.unroll_reg T x hk j, if_pos rfl]
    simp only [state]
    cases M.init j <;> rfl
  | succ k ih =>
    intro hk
    refine M.unroll_block T x hk fun j => ?_
    rw [M.unroll_reg T x hk j, if_neg (by omega), Nat.add_sub_cancel]
    simp only [DAGGate.eval, List.all_cons, List.all_nil, Bool.and_true]
    exact ih (by omega) _ (M.next_lt j)

/-- The unrolled circuit computes the chip's output after `T` ticks. -/
theorem unroll_eval (T : ℕ) (x : Fin n → Bool) : (M.unroll T).eval x = M.run T x :=
  M.unroll_values T x T le_rfl _ M.comb.output_lt

/-- The unrolled circuit has `n` inputs plus `T + 1` blocks of `size` gates. -/
theorem unroll_size (T : ℕ) : (M.unroll T).size = n + (T + 1) * M.size := by
  simp [DAGCircuit.size, length_unroll_gates]

/-- Each block places the chip's vertices injectively. -/
theorem place_injective (k : ℕ) : Function.Injective (M.place k) := by
  intro a b h
  unfold place at h
  split_ifs at h <;> omega

/-- An unrolled gate is a register gate (an `∧`/`∨` gate of fan-in at most one) or a copy
of a gate of `comb` with its inputs placed injectively. -/
private theorem unrollGate_cases (p : ℕ) :
    ((M.unrollGate p).args.length ≤ 1 ∧ (M.unrollGate p).kind ≠ .not) ∨
      ∃ g ∈ M.comb.gates, M.unrollGate p = ⟨g.kind, g.args.map (M.place (p / M.size))⟩ := by
  unfold unrollGate
  by_cases hj : p % M.size < r
  · rw [dif_pos hj]
    left
    split_ifs with h1 h2 <;> simp
  · rw [dif_neg hj]
    rcases Nat.lt_or_ge (p % M.size - r) M.comb.gates.length with hlt | hge
    · right
      refine ⟨_, List.getElem_mem hlt, ?_⟩
      simp only [List.getD_eq_getElem _ _ hlt]
    · left
      rw [List.getD_eq_default _ _ hge]
      simp

/-- Unrolling preserves well-formedness. -/
theorem unroll_isWellFormed (T : ℕ) (h : M.comb.IsWellFormed) : (M.unroll T).IsWellFormed := by
  intro g hg
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
  rcases M.unrollGate_cases p with ⟨hl, hk⟩ | ⟨g, hg, he⟩
  · exact ⟨List.nodup_iff_count_le_one.mpr fun a => (List.count_le_length).trans hl,
      fun h => absurd h hk⟩
  · rw [he]
    exact ⟨(h g hg).1.map (M.place_injective _), fun hk => by simpa using (h g hg).2 hk⟩

/-- Unrolling preserves fan-in two. -/
theorem unroll_isFaninTwo (T : ℕ) (h : M.comb.IsFaninTwo) : (M.unroll T).IsFaninTwo := by
  refine ⟨M.unroll_isWellFormed T h.1, fun g hg => ?_⟩
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
  rcases M.unrollGate_cases p with ⟨hl, -⟩ | ⟨g, hg, he⟩
  · omega
  · rw [he]; simpa using h.2 g hg

end SeqCircuit

/-- **Unrolling a chip.**  Any computation that runs on a synchronous sequential circuit
with `C` gates and registers and finishes in time `T ≥ 1` is performed by a circuit of the
book's model of size at most `2 (C T + n)`, which is fan-in two if the chip's logic is.
[AB09, p. 108, footnote 1] ("can be performed by a Boolean circuit of size `O(C · T)`")

The book's `O(C · T)` hides the `n` input vertices, which [AB09, Def 6.1]'s size counts;
the exact size is `n + (T + 1) C` (`SeqCircuit.unroll_size`).  Registers are counted
among the chip's `C` gates, as each is a physical gate (a latch) on the chip.

**Proof sketch.** Lay out `T + 1` copies of the chip's combinational logic.  Copy `k`
reads the inputs directly and reads, in place of the registers, `r` gates holding the
register contents at time `k`: constants for `k = 0`, and for `k ≥ 1` identity gates
(fan-in-one `∧`) reading the latched vertices of copy `k - 1`.  By induction on `k`, and
within a copy by strong induction on the vertex, every vertex of copy `k` holds the chip's
value at time `k` (`SeqCircuit.unroll_values`); the output is that of copy `T`.  Vertices
are placed injectively, so no gate reads a vertex twice. -/
theorem SeqCircuit.exists_dagCircuit_of_run {n r : ℕ} (M : SeqCircuit n r) {T : ℕ}
    (hT : 1 ≤ T) :
    ∃ D : DAGCircuit n, (∀ x, D.eval x = M.run T x) ∧ D.size ≤ 2 * (M.size * T + n) ∧
      (M.comb.IsWellFormed → D.IsWellFormed) ∧ (M.comb.IsFaninTwo → D.IsFaninTwo) := by
  refine ⟨M.unroll T, M.unroll_eval T, ?_, M.unroll_isWellFormed T, M.unroll_isFaninTwo T⟩
  rw [M.unroll_size T]
  have : M.size ≤ M.size * T := Nat.le_mul_of_pos_right _ hT
  have h3 : (T + 1) * M.size = M.size * T + M.size := by ring
  omega

end BoolCircuit
