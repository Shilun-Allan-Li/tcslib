/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.HardFunctions
import TCSlib.Complexity.CircuitComplexity.Universal

/-!
# A nonuniform size hierarchy for tree circuits

`Language.InTreeSize T` is the class of languages decided, at each input length `n`, by a
`BoolCircuit.Circuit n` of size at most `T n`.  **It is not `Language.InSIZE`**, and the
theorem below is therefore not [AB09, Thm 6.22]; see `## Divergences`.

## Main definitions

* `ACP.widenCircuit` / `ACP.restrictCircuit` — reindex a circuit into more variables, and
  restrict a circuit to its first `m` variables by fixing the rest to constants.
* `ACP.onFirst` — `f` applied to the first `m` of `n` input bits; [AB09, p.116]'s `g`.
* `Language.InTreeSize`, `ACP.TreeSize` — the size class, as a predicate and as a set.
* `ACP.padFamily` / `ACP.padLanguage` — the padded language and its circuits: at length `n`,
  `F n` applied to the first `ℓ n` bits.

## Main results

* `ACP.widenCircuit_size`, `ACP.restrictCircuit_size` — both reindexings preserve `size`
  exactly; `ACP.restrictCircuit_eval_of_onFirst` is the step [AB09, p.116] needs, pulling a
  circuit for `g` back to one for `f`.
* `Language.InTreeSize.mono`, `Language.zero_inTreeSize` — monotonicity in `T`, and that
  every class with `1 ≤ T` is inhabited.
* `ACP.padLanguage_inTreeSize` / `ACP.padLanguage_not_inTreeSize` — the two halves of the
  separation, from [AB09, Claim 2.13] and [AB09, Thm 6.21] respectively.
* `ACP.treeSize_ssubset` — `TreeSize T ⊂ TreeSize T'` given a padding length `ℓ`; the
  tree-model analogue of [AB09, Thm 6.22] and **not** that theorem, whose class is
  `Language.InSIZE`.
* `ACP.treeSize_ssubset_of_lt` — the same with `ℓ` supplied; `ACP.treeSize_one_ssubset` an
  instance of it, and `ACP.zero_mem_treeSize_one` that its smaller class is nonempty.

## Divergences from [AB09, Thm 6.22]

**This is not AB's `SIZE`, and AB's theorem is not formalized.** [AB09, Def 6.2]'s `SIZE(T)`
is `Language.InSIZE` (`PPoly.lean`), over `ACP.CircuitFamily` — a layered `FeedForward`
*DAG* on `AC_GateOps`.  Everything here is over `BoolCircuit.Circuit`, an unbounded-fan-in
*tree*.  Neither transfer is available.  Tree → `FeedForward` exists only as
`BoolCircuit.Circuit.toFeedForward`, which is over `FeedForward Bool`, not `Fin 2`, and puts
the whole circuit into one gate `⟨Fin n, C.eval⟩` that is not in `AC_GateOps`; every layer
above the input is `Unit`, so its size is `C.depth + 1` whatever `C.size` is, and a map whose
image size never mentions its source's cannot transport a size class either way.
`FeedForward` → tree is `ACP.FeedForward.toCircuit`, correct only under
`FeedForward.IsAndOrGate` — every gate an AND or an OR — whereas `AC_GateOps` also holds
`id` and `NOT`, for neither of which `BoolCircuit.Circuit` has a gate (it negates only at
literals); and its bound `(k + 1) ^ depth` is exponential in depth in any case.  Carrying
U10's hardness over to `SIZE`'s model needs that second direction, so the hierarchy is
stated here over the model U9 and U10 live in, and `SIZE(T) ⊊ SIZE(T')` remains open.

**The size measures also differ, in both directions.** `Circuit.size` counts every node of a
tree, so every literal *occurrence* costs a node and no gate can be reused, raising the count
against [AB09, Def 6.1]; but it charges `1` for a `k`-ary gate where Def 6.1 charges `k - 1`
vertices, lowering it.  The two families are therefore not comparable.  The full accounting
is in `Universal.lean` and `HardFunctions.lean`; it is not restated here.

**The constants are ours.** At [AB09, p.116] the padded function costs `10 ℓ 2 ^ ℓ` and the
hardness bound is `2 ^ ℓ / (10 ℓ)`; we use `Universal.lean`'s `2 ^ ℓ * (ℓ + 1) + 1` and
`HardFunctions.lean`'s side condition `(ℓ + 4) * S < 2 ^ ℓ`.  Both of ours are the sharper
number for every `ℓ ≥ 1`, which buys nothing across models — they measure the incomparable
object above.  AB's hypothesis `2ⁿ/n > T'(n) > 10 T(n) > n`, with `ℓ = 1.1 log n` chosen
inside the proof, is not reproduced: `ℓ` is a parameter here, constrained by `ℓ n ≤ n` and
the one inequality each half consumes.  Recovering AB's shape needs `Nat.log` arithmetic and
a large-`n` argument, and is not attempted.

**`ℓ n₀ ≥ 3` is what keeps the statement non-degenerate.** Below it `hlow` forces
`T n₀ = 0`, and `Circuit.size` is never `0`, so `TreeSize T` would be empty and the strict
inclusion would separate nothing.  `ACP.treeSize_one_ssubset` takes `ℓ n = min n 3`.

**One length suffices.** AB relates `T` and `T'` at every length; `hlow` is imposed here at a
single `n₀`, which is all strictness needs.  Demanding it at every `n` would force `T n = 0`
for `n ≤ 2` and empty the class, for the reason just given.

## Implementation notes

`BoolCircuit.TreeCircuitFamily` in `NCAC.lean` bundles the same `(n : ℕ) → Circuit n` data,
but that file is a parallel track; `Language.InTreeSize` quantifies over the bare function so
that this file depends only on U9 and U10.  Merging the two is a cross-track item.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open BoolCircuit

namespace ACP

variable {m n : ℕ}

/-! ## Reindexing a circuit -/

/-- An empty gate is a constant: the empty `AND` is `true`, the empty `OR` is `false`. -/
theorem eval_node_nil (b : Bool) (x : Fin n → Bool) :
    (Circuit.node b ([] : List (Circuit n))).eval x = b := by
  cases b <;> simp [Circuit.eval]

/-- A circuit on `m` variables read as a circuit on `n ≥ m` variables, ignoring the rest. -/
def widenCircuit (h : m ≤ n) : Circuit m → Circuit n
  | .lit l => .lit ⟨Fin.castLE h l.idx, l.sign⟩
  | .node b cs => .node b (cs.map (widenCircuit h))

/-- Widening reads the first `m` coordinates of its input. -/
theorem widenCircuit_eval (h : m ≤ n) (c : Circuit m) (x : Fin n → Bool) :
    (widenCircuit h c).eval x = c.eval fun i => x (Fin.castLE h i) := by
  induction c using Circuit.ind with
  | hlit l => simp [widenCircuit, Circuit.eval, Lit.eval]
  | hnode b cs ih =>
      cases b <;>
        simp only [widenCircuit, Circuit.eval, List.foldr_map] <;>
        exact List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc]

/-- Widening changes no node. -/
theorem widenCircuit_size (h : m ≤ n) (c : Circuit m) :
    (widenCircuit h c).size = c.size := by
  induction c using Circuit.ind with
  | hlit l => simp [widenCircuit, Circuit.size]
  | hnode b cs ih =>
      simp only [widenCircuit, Circuit.size, List.foldr_map]
      exact congrArg (1 + ·) (List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc])

/-- The input on `n` variables agreeing with `y` on the first `m` and with `pad` beyond. -/
def extendBy (m : ℕ) (pad : Fin n → Bool) (y : Fin m → Bool) : Fin n → Bool :=
  fun i => if hi : i.val < m then y ⟨i.val, hi⟩ else pad i

/-- A circuit on `n` variables restricted to its first `m`, the rest fixed to `pad`.  A
literal on a fixed variable becomes an empty gate, which costs the same one node. -/
def restrictCircuit (m : ℕ) (pad : Fin n → Bool) : Circuit n → Circuit m
  | .lit l =>
      if hi : l.idx.val < m then .lit ⟨⟨l.idx.val, hi⟩, l.sign⟩ else .node (l.eval pad) []
  | .node b cs => .node b (cs.map (restrictCircuit m pad))

/-- Restricting computes the original circuit on the extended input. -/
theorem restrictCircuit_eval (m : ℕ) (pad : Fin n → Bool) (c : Circuit n) (y : Fin m → Bool) :
    (restrictCircuit m pad c).eval y = c.eval (extendBy m pad y) := by
  induction c using Circuit.ind with
  | hlit l =>
      by_cases hi : l.idx.val < m
      · simp [restrictCircuit, hi, Circuit.eval, Lit.eval, extendBy]
      · simp [restrictCircuit, hi, eval_node_nil, Circuit.eval, Lit.eval, extendBy]
  | hnode b cs ih =>
      cases b <;>
        simp only [restrictCircuit, Circuit.eval, List.foldr_map] <;>
        exact List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc]

/-- Restricting changes no node: a fixed literal becomes a one-node empty gate. -/
theorem restrictCircuit_size (m : ℕ) (pad : Fin n → Bool) (c : Circuit n) :
    (restrictCircuit m pad c).size = c.size := by
  induction c using Circuit.ind with
  | hlit l => by_cases hi : l.idx.val < m <;> simp [restrictCircuit, hi, Circuit.size]
  | hnode b cs ih =>
      simp only [restrictCircuit, Circuit.size, List.foldr_map]
      exact congrArg (1 + ·) (List.foldr_ext _ _ _ fun c hc _ => by rw [ih c hc])

/-- `f` applied to the first `m` of `n` input bits.  [AB09, p.116]'s `g`. -/
def onFirst (h : m ≤ n) (f : (Fin m → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => f fun i => x (Fin.castLE h i)

/-- A circuit for `onFirst h f` restricts to a circuit for `f`. -/
theorem restrictCircuit_eval_of_onFirst {h : m ≤ n} {pad : Fin n → Bool} {c : Circuit n}
    {f : (Fin m → Bool) → Bool} (hc : ∀ x, c.eval x = onFirst h f x) (y : Fin m → Bool) :
    (restrictCircuit m pad c).eval y = f y := by
  rw [restrictCircuit_eval, hc, onFirst]
  exact congrArg f (funext fun i => by simp [extendBy, Fin.castLE])

end ACP

/-! ## The size class -/

/-- `L ∈ TreeSize(T)`: some family of `BoolCircuit.Circuit`s, the length-`n` one of size at
most `T n`, decides `L`.  **Not** [AB09, Def 6.2] — see this file's `## Divergences`. -/
def Language.InTreeSize (T : ℕ → ℕ) (L : Language Bool) : Prop :=
  ∃ C : (n : ℕ) → BoolCircuit.Circuit n,
    (∀ n, (C n).size ≤ T n) ∧ ∀ w : List Bool, w ∈ L ↔ (C w.length).eval w.get = true

/-- `TreeSize(T) ⊆ TreeSize(T')` whenever `T ≤ T'` pointwise. -/
theorem Language.InTreeSize.mono {T T' : ℕ → ℕ} {L : Language Bool} (hL : L.InTreeSize T)
    (h : ∀ n, T n ≤ T' n) : L.InTreeSize T' := by
  obtain ⟨C, hS, hC⟩ := hL
  exact ⟨C, fun n => (hS n).trans (h n), hC⟩

/-- The empty language needs only the empty `OR`, so every class with `1 ≤ T` is inhabited. -/
theorem Language.zero_inTreeSize {T : ℕ → ℕ} (hT : ∀ n, 1 ≤ T n) :
    (0 : Language Bool).InTreeSize T :=
  ⟨fun _ => .node false [], fun n => by simpa [BoolCircuit.Circuit.size] using hT n, fun w => by
    simp only [ACP.eval_node_nil, Bool.false_eq_true, iff_false]
    exact Language.notMem_zero w⟩

namespace ACP

variable {m n : ℕ}

/-- The size class packaged as a set of languages. -/
def TreeSize (T : ℕ → ℕ) : Set (Language Bool) := {L | L.InTreeSize T}

/-- Set membership in `TreeSize` agrees with the predicate `Language.InTreeSize`. -/
@[simp]
theorem mem_treeSize_iff (T : ℕ → ℕ) (L : Language Bool) :
    L ∈ TreeSize T ↔ L.InTreeSize T :=
  Iff.rfl

/-- Two families deciding the same language agree on every assignment.  Every assignment is a
`w.get` for `w = List.ofFn x`; `key` generalizes the length so that reaching it is a `subst`
rather than a dependent rewrite. -/
private theorem eval_eq_of_iff {C D : (n : ℕ) → Circuit n}
    (h : ∀ w : List Bool, (C w.length).eval w.get = true ↔ (D w.length).eval w.get = true)
    (n : ℕ) (x : Fin n → Bool) : (C n).eval x = (D n).eval x := by
  have hall : ∀ w : List Bool, (C w.length).eval w.get = (D w.length).eval w.get := fun w => by
    rw [Bool.eq_iff_iff]; exact h w
  have key : ∀ (k : ℕ) (w : List Bool) (hw : w.length = k) (z : Fin k → Bool),
      (∀ i, z i = w.get (Fin.cast hw.symm i)) → (C k).eval z = (D k).eval z := by
    intro k w hw z hz
    subst hw
    have hzw : z = w.get := funext fun i => by simpa using hz i
    subst hzw
    exact hall w
  exact key n (List.ofFn x) List.length_ofFn x fun i => by simp

/-! ## Padding a hard function -/

/-- The circuit family of [AB09, p.116]: at length `n`, the universal circuit for `F n`
widened to read only the first `ℓ n` bits. -/
noncomputable def padFamily {ℓ : ℕ → ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool) (n : ℕ) : Circuit n :=
  widenCircuit (hle n) (universalCircuit (F n))

/-- `padFamily` computes `F n` on the first `ℓ n` bits. -/
theorem padFamily_eval {ℓ : ℕ → ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool) (n : ℕ) (x : Fin n → Bool) :
    (padFamily hle F n).eval x = onFirst (hle n) (F n) x := by
  rw [padFamily, widenCircuit_eval, onFirst, universalCircuit_eval]

/-- The language `padFamily` decides. -/
def padLanguage {ℓ : ℕ → ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool) : Language Bool :=
  {w | (padFamily hle F w.length).eval w.get = true}

/-- The upper half: padding costs nothing, so [AB09, Claim 2.13]'s bound at length `ℓ n`
bounds the circuit at length `n`. -/
theorem padLanguage_inTreeSize {ℓ T' : ℕ → ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool)
    (hup : ∀ n, 2 ^ ℓ n * (ℓ n + 1) + 1 ≤ T' n) :
    (padLanguage hle F).InTreeSize T' :=
  ⟨padFamily hle F, fun n => by
    rw [padFamily, widenCircuit_size]
    exact (universalCircuit_size_le (F n)).trans (hup n), fun _ => Iff.rfl⟩

/-- The lower half: if `F n₀` is hard for size `T n₀`, the padded language is not in
`TreeSize(T)`.

**Proof sketch.** A family deciding `padLanguage` agrees with `padFamily` on every word,
hence — by `eval_eq_of_iff` — on every assignment, so at length `n₀` its circuit computes
`F n₀` on the first `ℓ n₀` bits.  Restricting that circuit to its first `ℓ n₀` variables,
with the rest fixed to `false`, gives a circuit for `F n₀` itself of the same size, which
hardness forbids. -/
theorem padLanguage_not_inTreeSize {ℓ T : ℕ → ℕ} {n₀ : ℕ} (hle : ∀ n, ℓ n ≤ n)
    (F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool)
    (hF : ∀ C : Circuit (ℓ n₀), C.size ≤ T n₀ → ∃ x, C.eval x ≠ F n₀ x) :
    ¬ (padLanguage hle F).InTreeSize T := by
  rintro ⟨D, hDsize, hDL⟩
  have hev : ∀ x : Fin n₀ → Bool, (D n₀).eval x = onFirst (hle n₀) (F n₀) x := fun x => by
    rw [← eval_eq_of_iff (fun w => hDL w) n₀ x, padFamily_eval]
  obtain ⟨y, hy⟩ := hF (restrictCircuit (ℓ n₀) (fun _ => false) (D n₀))
    (by rw [restrictCircuit_size]; exact hDsize n₀)
  exact hy (restrictCircuit_eval_of_onFirst hev y)

/-! ## The hierarchy -/

/-- **Nonuniform hierarchy, tree model.**  With a padding length `ℓ` long enough that
[AB09, Thm 6.21] bites at some length `n₀` and short enough that [AB09, Claim 2.13] still
fits inside `T'`, `TreeSize(T)` is a proper subclass of `TreeSize(T')`.  The tree-model analogue
of [AB09, Thm 6.22]; not that theorem — see this file's `## Divergences`.

**Proof sketch.** Inclusion is `Language.InTreeSize.mono`.  For strictness, pick at each
length `n` a function `F n` on `ℓ n` bits that no circuit of size `T n` computes, where the
counting bound permits one, and anything otherwise; `n₀` is a length where it permits one.
The language obtained by applying `F n` to the first `ℓ n` bits is in `TreeSize(T')` by
`padLanguage_inTreeSize` and outside `TreeSize(T)` by `padLanguage_not_inTreeSize`, so the
reverse inclusion fails. -/
theorem treeSize_ssubset {T T' ℓ : ℕ → ℕ} (n₀ : ℕ) (hle : ∀ n, ℓ n ≤ n)
    (hTT' : ∀ n, T n ≤ T' n) (hup : ∀ n, 2 ^ ℓ n * (ℓ n + 1) + 1 ≤ T' n)
    (hlow : (ℓ n₀ + 4) * T n₀ < 2 ^ ℓ n₀) :
    TreeSize T ⊂ TreeSize T' := by
  classical
  rw [Set.ssubset_def]
  refine ⟨fun _ hL => hL.mono hTT', fun hsub => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F : (n : ℕ) → (Fin (ℓ n) → Bool) → Bool,
      ∀ C : Circuit (ℓ n₀), C.size ≤ T n₀ → ∃ x, C.eval x ≠ F n₀ x := by
    refine ⟨fun n => if h : (ℓ n + 4) * T n < 2 ^ ℓ n then
      Classical.choose (exists_not_eval_of_lt h) else fun _ => false, ?_⟩
    simpa only [dif_pos hlow] using Classical.choose_spec (exists_not_eval_of_lt hlow)
  exact padLanguage_not_inTreeSize hle F hF (hsub (padLanguage_inTreeSize hle F hup))

/-- Any `T` that the counting bound beats at a single length `n₀` is beaten by a larger
bound: take `ℓ n = min n n₀`. -/
theorem treeSize_ssubset_of_lt {T : ℕ → ℕ} {n₀ : ℕ} (h : (n₀ + 4) * T n₀ < 2 ^ n₀) :
    TreeSize T ⊂ TreeSize fun n => max (T n) (2 ^ min n n₀ * (min n n₀ + 1) + 1) :=
  treeSize_ssubset (ℓ := fun n => min n n₀) n₀ (fun n => Nat.min_le_left n n₀)
    (fun n => Nat.le_max_left _ _) (fun n => Nat.le_max_right _ _)
    (by simpa using h)

/-- A concrete instance, with `ℓ = 3`, the least length at which [AB09, Thm 6.21] has
content. -/
theorem treeSize_one_ssubset :
    TreeSize (fun _ => 1) ⊂ TreeSize fun n => max 1 (2 ^ min n 3 * (min n 3 + 1) + 1) :=
  treeSize_ssubset_of_lt (T := fun _ => 1) (n₀ := 3) (by norm_num)

/-- The smaller class of `treeSize_one_ssubset` is inhabited, so that inclusion is a strict
one between two nonempty classes. -/
theorem zero_mem_treeSize_one : (0 : Language Bool) ∈ TreeSize fun _ => 1 :=
  Language.zero_inTreeSize fun _ => le_refl 1

end ACP
