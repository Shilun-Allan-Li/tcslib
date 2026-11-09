/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-wiring inputs into a circuit

The construction used in the proof of [AB09, Thm 6.18] (p. 113): "taking a circuit `C` with
two inputs `x ∈ {0,1}^n`, `y ∈ {0,1}^m` and fixing the inputs corresponding to `y` gives
the circuit `C_y` that for every `x` returns `C(x, y)`.  It is easy to do so while ensuring
that the size of `C_y` is not greater than the size of `C`."

Over the book model `BoolCircuit.DAGCircuit`, each fixed input vertex is replaced by a
constant gate (a fan-in-zero `∧` for `1`, a fan-in-zero `∨` for `0`).  Inputs are combined
with `Fin.append`, so `C (x, y)` is `C.eval (Fin.append x y)`, whose underlying bit list is
`x ++ y`.

## Main definitions

* `BoolCircuit.DAGCircuit.hardwire` — fix the *last* `m` inputs (the book's "second
  input"): `C : DAGCircuit (n + m)` becomes a `DAGCircuit n`.
* `BoolCircuit.DAGCircuit.hardwireLeft` — fix the *first* `m` inputs:
  `C : DAGCircuit (m + n)` becomes a `DAGCircuit n`.
* `BoolCircuit.DAGCircuitFamily.hardwire` — hard-wire one advice string per input length.

## Main results

* `hardwire_eval`, `hardwire_size`, `hardwire_isWellFormed`, `hardwire_isFaninTwo`,
  `hardwire_depth_le`, and the same five for `hardwireLeft`.
* `Language.InSIZE.of_hardwire`, `Language.InPPoly.of_hardwire` — the family-level step of
  [AB09, Thm 6.18]: if circuits `D_n` on `n + a(n)` inputs have fan-in two and size at most
  `p(n)`, then `{x | D_{|x|}(x, α_{|x|}) = 1} ∈ SIZE(p)`, hence in `P/poly` for polynomial
  `p`.

## Divergences from [AB09, Thm 6.18]

* **Size is preserved exactly** (`hardwire_size`), which is stronger than the book's
  "not greater": the model counts input vertices in the size, and each of the `m` fixed
  input vertices becomes one constant gate.
* **The construction relies on the model's constant gates.**  Each fixed input becomes a
  fan-in-zero `∧` (`true`) or `∨` (`false`) gate, the model's constants (see the constants
  divergence in `DAGCircuit.lean`).  The book's literal model (fan-in exactly two, no
  constants) has none; with `n = 0` free inputs it could not build a constant at all.
* **Depth may grow by one** (`hardwire_depth_le`).  The book says nothing about depth.  In
  the model an input has depth `0` while every gate, including a constant, has depth at
  least `1`, so a gate reading a fixed input can get one deeper.
* **The family corollary takes the size bound `p(n)` directly.**  In the book, `D_n` has
  size polynomial in `n + a(n)` with `a` polynomial; the composition into one polynomial in
  `n` is left to the caller.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.3, proof of Theorem 6.18, p. 113.)
-/

namespace BoolCircuit

/-! ## Running constant gates -/

/-- Running constant gates for the bits `l` appends `l` to the vertex values. -/
theorem runWith_eval_constGates (l : List Bool) (init : List Bool) :
    runWith DAGGate.eval (l.map constGate) init = init ++ l := by
  induction l generalizing init with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, runWith_cons, ih]; simp

/-- Running constant gates appends depth `1` for each of them. -/
theorem runWith_depth_constGates (l : List Bool) (init : List ℕ) :
    runWith DAGGate.depth (l.map constGate) init = init ++ List.replicate l.length 1 := by
  induction l generalizing init with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, runWith_cons, ih]
    simp [List.replicate_succ]

/-! ## Depth of a remapped gate -/

private theorem foldr_max_le_succ {l : List ℕ} {p q : ℕ → ℕ} (h : ∀ a ∈ l, p a ≤ q a + 1) :
    (l.map p).foldr max 0 ≤ (l.map q).foldr max 0 + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le ((h a (by simp)).trans (Nat.add_le_add_right (le_max_left _ _) 1))
      ((ih fun b hb => h b (by simp [hb])).trans (Nat.add_le_add_right (le_max_right _ _) 1))

/-- A renamed gate is at most one deeper than the original gate when every renamed input
is at most one deeper than the original input. -/
theorem DAGGate.depth_remap_le (σ : ℕ → ℕ) (g : DAGGate) (ds ds' : List ℕ)
    (h : ∀ a ∈ g.args, ds.getD (σ a) 0 ≤ ds'.getD a 0 + 1) :
    (g.remap σ).depth ds ≤ g.depth ds' + 1 := by
  simp only [DAGGate.remap, DAGGate.depth, List.map_map, Function.comp_def]
  have := foldr_max_le_succ (l := g.args) (p := fun a => ds.getD (σ a) 0)
    (q := fun a => ds'.getD a 0) h
  omega

private theorem getD_le_one {l : List ℕ} (hl : ∀ b ∈ l, b ≤ 1) (k : ℕ) : l.getD k 0 ≤ 1 := by
  rw [List.getD_eq_getD_getElem?]
  cases h : l[k]? with
  | none => simp
  | some b => exact hl b (List.mem_of_getElem? h)

/-! ## Fixing the last inputs -/

namespace DAGCircuit

variable {n m : ℕ}

/-- The circuit `C_y` of [AB09, Thm 6.18]: the circuit `C` on inputs `(x, y)`, with the
last `m` inputs fixed to `y`.  The input vertices `n, …, n + m - 1` of `C` become constant
gates, so every vertex keeps its number and no gate needs rewiring.  [AB09, Thm 6.18] -/
def hardwire (C : DAGCircuit (n + m)) (y : Fin m → Bool) : DAGCircuit n where
  gates := (List.ofFn y).map constGate ++ C.gates
  output := C.output
  args_lt := by
    intro i hi a ha
    have hy : ((List.ofFn y).map constGate).length = m := by simp
    by_cases him : i < m
    · rw [List.getElem_append_left (by rw [hy]; exact him)] at ha
      simp at ha
    · rw [List.getElem_append_right (by rw [hy]; omega)] at ha
      have := C.args_lt (i - ((List.ofFn y).map constGate).length) (by simp at hi ⊢; omega) a ha
      rw [hy] at this
      omega
  output_lt := by have := C.output_lt; simp; omega

section Right

variable (C : DAGCircuit (n + m)) (y : Fin m → Bool)

/-- The hard-wired circuit's vertex values on `x` are `C`'s vertex values on `(x, y)`. -/
theorem hardwire_values (x : Fin n → Bool) :
    (C.hardwire y).values x = C.values (Fin.append x y) := by
  simp only [values, hardwire, runWith_append, runWith_eval_constGates, List.ofFn_fin_append]

/-- `C_y(x) = C(x, y)`: the hard-wired circuit computes `C` with its second input fixed to
`y`.  [AB09, Thm 6.18] -/
theorem hardwire_eval (x : Fin n → Bool) :
    (C.hardwire y).eval x = C.eval (Fin.append x y) := by
  simp only [eval, hardwire_values]; rfl

/-- `|C_y| = |C|`: hard-wiring preserves the size exactly, each fixed input vertex becoming
one constant gate.  [AB09, Thm 6.18] (the book claims `|C_y| ≤ |C|`). -/
theorem hardwire_size : (C.hardwire y).size = C.size := by
  simp [size, hardwire]; omega

/-- `|C_y| ≤ |C|`, as stated in [AB09, Thm 6.18]. -/
theorem hardwire_size_le : (C.hardwire y).size ≤ C.size :=
  (hardwire_size C y).le

/-- Hard-wiring keeps a circuit well formed: the new gates are constants. -/
theorem hardwire_isWellFormed (hC : C.IsWellFormed) : (C.hardwire y).IsWellFormed := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
    exact ⟨by simp, fun h => absurd h (constGate_kind_ne_not b)⟩
  · exact hC g hg

/-- Hard-wiring keeps fan-in at most two: the new gates have fan-in zero. -/
theorem hardwire_isFaninTwo (hC : C.IsFaninTwo) : (C.hardwire y).IsFaninTwo := by
  refine ⟨hardwire_isWellFormed C y hC.1, fun g hg => ?_⟩
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
    simp
  · exact hC.2 g hg

/-- Hard-wiring increases the depth by at most one: a fixed input of depth `0` becomes a
constant gate of depth `1`.  (Not in [AB09].) -/
theorem hardwire_depth_le : (C.hardwire y).depth ≤ C.depth + 1 := by
  have key := runWith_remap_rel DAGGate.depth (fun a b => a ≤ b + 1) 0 id
    (fun g ds ds' h => by simpa using DAGGate.depth_remap_le id g ds ds' h)
    (L := n + m) (L' := n + m) (List.replicate (n + m) 0)
    (List.replicate n 0 ++ List.replicate m 1) (by simp) (by simp) (fun v hv => hv)
    (fun i => rfl)
    (fun v _ => (getD_le_one (l := List.replicate n 0 ++ List.replicate m 1)
      (by intro b hb; simp at hb; omega) _).trans (Nat.le_add_left _ _)) C.gates C.args_lt
    C.output C.output_lt
  have hmap : C.gates.map (DAGGate.remap id) = C.gates := by
    conv_rhs => rw [← List.map_id C.gates]
    exact List.map_congr_left fun g _ => DAGGate.remap_id g
  rw [hmap] at key
  unfold depth depthAt depths hardwire
  dsimp only
  rw [runWith_append, runWith_depth_constGates, List.length_ofFn]
  exact key

end Right

/-! ## Fixing the first inputs -/

/-- The renumbering used to fix the first `m` of `m + n` inputs: old input `v < m` (fixed)
moves to vertex `n + v`, old input `m + j` (free) moves to vertex `j`, and gate vertices
`m + n + i` stay put. -/
def leftPerm (m n v : ℕ) : ℕ :=
  if v < m then n + v else if v < m + n then v - m else v

/-- `leftPerm` sends vertices below `m + n + k` to vertices below `n + m + k`. -/
theorem leftPerm_lt {v k : ℕ} (hv : v < m + n + k) : leftPerm m n v < n + m + k := by
  unfold leftPerm; split_ifs <;> omega

/-- `leftPerm` fixes every gate vertex `m + n + i`. -/
theorem leftPerm_gate (i : ℕ) : leftPerm m n (m + n + i) = n + m + i := by
  unfold leftPerm; split_ifs <;> omega

/-- `leftPerm` is injective (it is a permutation of `ℕ`). -/
theorem leftPerm_injective : Function.Injective (leftPerm m n) := by
  intro a b h; unfold leftPerm at h; split_ifs at h <;> omega

/-- The circuit `C` on inputs `(y, x)` with the *first* `m` inputs fixed to `y`: the
mirror image of `hardwire`.  The fixed input vertices become constant gates placed right
after the free inputs, so the vertices of `C` are renumbered by `leftPerm`.
[AB09, Thm 6.18] (the book fixes the second input; this is the symmetric variant). -/
def hardwireLeft (C : DAGCircuit (m + n)) (y : Fin m → Bool) : DAGCircuit n where
  gates := (List.ofFn y).map constGate ++ C.gates.map (DAGGate.remap (leftPerm m n))
  output := leftPerm m n C.output
  args_lt := by
    intro i hi a ha
    have hy : ((List.ofFn y).map constGate).length = m := by simp
    by_cases him : i < m
    · rw [List.getElem_append_left (by rw [hy]; exact him)] at ha
      simp at ha
    · rw [List.getElem_append_right (by rw [hy]; omega)] at ha
      simp only [List.getElem_map, DAGGate.remap, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have := C.args_lt _ (by simp at hi ⊢; omega) b hb
      rw [hy] at this
      have := leftPerm_lt (m := m) (n := n) (k := i - m) (by omega : b < m + n + (i - m))
      omega
  output_lt := by
    have := leftPerm_lt (m := m) (n := n) C.output_lt
    simp; omega

section Left

variable (C : DAGCircuit (m + n)) (y : Fin m → Bool)

/-- `C_y(x) = C(y, x)`: the circuit with its first input fixed to `y`.  [AB09, Thm 6.18]

**Proof sketch.** After the constant gates the vertex values are `x ++ y`, while `C` on
`(y, x)` starts from `y ++ x`; `leftPerm` matches each old input vertex with the new
vertex holding the same bit, and fixes the gate vertices.  Renaming commutes with running
the gates (`runWith_remap_rel` with equality), so the renamed output vertex carries `C`'s
output. -/
theorem hardwireLeft_eval (x : Fin n → Bool) :
    (C.hardwireLeft y).eval x = C.eval (Fin.append y x) := by
  have key := runWith_remap_rel DAGGate.eval Eq false (leftPerm m n)
    (fun g _ _ h => DAGGate.eval_remap g _ h) (L := m + n) (L' := n + m)
    (List.ofFn (Fin.append y x)) (List.ofFn x ++ List.ofFn y) (by simp) (by simp)
    (fun v hv => by simpa using leftPerm_lt (m := m) (n := n) (k := 0) (by simpa using hv))
    (fun i => leftPerm_gate i)
    (fun v hv => by
      rw [List.ofFn_fin_append]
      unfold leftPerm
      by_cases hvm : v < m
      · rw [if_pos hvm, List.getD_append_right _ _ _ _ (by simp),
          List.getD_append _ _ _ _ (by simpa using hvm)]
        simp
      · rw [if_neg hvm, if_pos hv, List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp)
    C.gates C.args_lt C.output C.output_lt
  unfold eval values hardwireLeft
  dsimp only
  rw [runWith_append, runWith_eval_constGates]
  exact key

/-- Fixing the first inputs preserves the size exactly.  [AB09, Thm 6.18] -/
theorem hardwireLeft_size : (C.hardwireLeft y).size = C.size := by
  simp [size, hardwireLeft]; omega

/-- `|C_y| ≤ |C|` when fixing the first inputs.  [AB09, Thm 6.18] -/
theorem hardwireLeft_size_le : (C.hardwireLeft y).size ≤ C.size :=
  (hardwireLeft_size C y).le

/-- Fixing the first inputs keeps a circuit well formed: renumbering is injective, and the
new gates are constants. -/
theorem hardwireLeft_isWellFormed (hC : C.IsWellFormed) : (C.hardwireLeft y).IsWellFormed := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
    exact ⟨by simp, fun h => absurd h (constGate_kind_ne_not b)⟩
  · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hnd, hnot⟩ := hC g₀ hg₀
    exact ⟨hnd.map leftPerm_injective, fun h => by simpa [DAGGate.remap] using hnot h⟩

/-- Fixing the first inputs keeps fan-in at most two. -/
theorem hardwireLeft_isFaninTwo (hC : C.IsFaninTwo) : (C.hardwireLeft y).IsFaninTwo := by
  refine ⟨hardwireLeft_isWellFormed C y hC.1, fun g hg => ?_⟩
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
    simp
  · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    simpa [DAGGate.remap] using hC.2 g₀ hg₀

/-- Fixing the first inputs increases the depth by at most one.  (Not in [AB09].) -/
theorem hardwireLeft_depth_le : (C.hardwireLeft y).depth ≤ C.depth + 1 := by
  have key := runWith_remap_rel DAGGate.depth (fun a b => a ≤ b + 1) 0 (leftPerm m n)
    (fun g ds ds' h => DAGGate.depth_remap_le _ g ds ds' h)
    (L := m + n) (L' := n + m) (List.replicate (m + n) 0)
    (List.replicate n 0 ++ List.replicate m 1) (by simp) (by simp)
    (fun v hv => by simpa using leftPerm_lt (m := m) (n := n) (k := 0) (by simpa using hv))
    (fun i => leftPerm_gate i)
    (fun v _ => (getD_le_one (l := List.replicate n 0 ++ List.replicate m 1)
      (by intro b hb; simp at hb; omega) _).trans (Nat.le_add_left _ _))
    C.gates C.args_lt C.output C.output_lt
  unfold depth depthAt depths hardwireLeft
  dsimp only
  rw [runWith_append, runWith_depth_constGates, List.length_ofFn]
  exact key

end Left

end DAGCircuit

/-! ## Hard-wiring advice into a family -/

namespace DAGCircuitFamily

/-- The family `C_n = (D_n)_{α_n}` of [AB09, Thm 6.18]: circuit `D_n` on `n + a(n)`
inputs with its second input hard-wired to the advice string `α_n`.  [AB09, Thm 6.18] -/
def hardwire {a : ℕ → ℕ} (D : (n : ℕ) → DAGCircuit (n + a n))
    (α : (n : ℕ) → Fin (a n) → Bool) : DAGCircuitFamily :=
  ⟨fun n => (D n).hardwire (α n)⟩

variable {a : ℕ → ℕ} (D : (n : ℕ) → DAGCircuit (n + a n)) (α : (n : ℕ) → Fin (a n) → Bool)

/-- The hard-wired family decides `{x | D_{|x|}(x, α_{|x|}) = 1}`.  [AB09, Thm 6.18] -/
theorem hardwire_language :
    (hardwire D α).language = {w | (D w.length).eval (Fin.append w.get (α w.length)) = true} := by
  ext w
  simp only [mem_language_iff, hardwire, DAGCircuit.hardwire_eval]
  exact Iff.rfl

end DAGCircuitFamily

end BoolCircuit

open BoolCircuit in
/-- **Hard-wiring advice into a `SIZE` bound** ([AB09, Thm 6.18], the `DTIME(n^c)/n^d ⊆ P/poly`
direction).  If the fan-in-two circuits `D_n` on `n + a(n)` inputs have size at most
`p(n)` and `α_n ∈ {0,1}^{a(n)}`, then `{x | D_{|x|}(x, α_{|x|}) = 1} ∈ SIZE(p)`.

The bound `p(n)` is on the size of `D_n` itself (which counts its `n + a(n)` inputs); the
book bounds `|D_n|` by a polynomial in `n + a(n)` and composes. -/
theorem Language.InSIZE.of_hardwire {a : ℕ → ℕ} (D : (n : ℕ) → DAGCircuit (n + a n))
    (α : (n : ℕ) → Fin (a n) → Bool) {p : ℕ → ℕ} (hD : ∀ n, (D n).IsFaninTwo)
    (hp : ∀ n, (D n).size ≤ p n) :
    Language.InSIZE p {w | (D w.length).eval (Fin.append w.get (α w.length)) = true} :=
  ⟨DAGCircuitFamily.hardwire D α, fun n => (D n).hardwire_isFaninTwo (α n) (hD n),
    fun n => ((D n).hardwire_size_le (α n)).trans (hp n),
    DAGCircuitFamily.hardwire_language D α⟩

open BoolCircuit in
/-- **Hard-wiring advice into `P/poly`** ([AB09, Thm 6.18]).  If the fan-in-two circuits
`D_n` on `n + a(n)` inputs have size at most `c (n + 1)^k` and `α_n ∈ {0,1}^{a(n)}`, then
`{x | D_{|x|}(x, α_{|x|}) = 1} ∈ P/poly`.  The polynomial is written `c (n + 1)^k` rather
than `n^c`, following `Language.InPPoly`. -/
theorem Language.InPPoly.of_hardwire {a : ℕ → ℕ} (D : (n : ℕ) → DAGCircuit (n + a n))
    (α : (n : ℕ) → Fin (a n) → Bool) {c k : ℕ} (hD : ∀ n, (D n).IsFaninTwo)
    (hp : ∀ n, (D n).size ≤ c * (n + 1) ^ k) :
    Language.InPPoly {w | (D w.length).eval (Fin.append w.get (α w.length)) = true} :=
  ⟨c, k, Language.InSIZE.of_hardwire D α hD hp⟩
