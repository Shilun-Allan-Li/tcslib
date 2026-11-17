/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation in law, coins in advance, and functions overridden by a table

Generic facts on simulations of oracle computations, stated for arbitrary oracle specifications.
They are the `Games` forms of the tools first proved for the encrypt-then-tag proof of
[PS10, Theorem 170.4] (`Composability.ETTGame`, `EncryptThenTag/Tools.lean`), with the tape
extension of `AdaptiveCPA.extTape` restated here.

* **Simulation through a state abstraction, in law** (`Games.expect_simulate_abs`): if every
  call of `impl₁` from the abstract image `f s` has the law of the call of `impl₂` from `s` with
  its new state abstracted, so do whole simulations, along runs within a query budget.
* **Coins in advance** (`Games.expect_simulate_tapeImpl`): an implementation that draws one fresh
  coin `t` per query (`Games.freshImpl`) has the law of the implementation that reads the `j`-th
  query's coin from a tape `T j` drawn in advance (`Games.tapeImpl`, `Games.extTape`), for
  computations with at most `κ` queries.
* **Functions overridden by a table** (`Games.ovr`): `ovr M R` is `R` with the values of the
  table `M` written over it; resampling `R` at a point outside the table moves into the table
  (`Games.expect_sample_ovr`).

## Main definitions

* `Games.freshImpl`, `Games.tapeImpl`: per-query coins drawn fresh, and read from tapes.
* `Games.extTape`: a finite family of coins extended to every index.
* `Games.ovr`: a function overridden by a finite table.

## Main results

* `Games.expect_simulate_abs`, `Games.expect_simulate_abs_inv`: simulation in law through a state
  abstraction.
* `Games.simulate_tapeImpl_congr`, `Games.expect_simulate_tapeImpl`: coins in advance.
* `Games.extTape_of_lt`, `Games.extTape_of_not_lt`, `Games.extTape_update`: the tape extension.
* `Games.ovr_nil`, `Games.ovr_cons`, `Games.ovr_of_not_mem`, `Games.ovr_of_mem`,
  `Games.ovr_update`, `Games.ovr_append`, `Games.expect_sample_ovr`: tables over functions.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  Theorem 170.4 (book p. 170): the first consumer.
-/

namespace TCSlib.Cryptography.Games

open ProbComp

/-! ### Simulation through a state abstraction, in law -/

section Abs

variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}

/-- **Simulation through a state abstraction, in law, along runs with a query budget.** Let every
call of `impl₂` from a state `s` with `cnt s < κ` raise `cnt` by at most one, and give every
function `g` of the answer and the abstracted new state the expectation that the call of `impl₁`
from `f s` gives it. Then for a computation `c` with at most `m` queries and `cnt s + m ≤ κ`,
`𝔼[G] (simulate impl₁ c (f s)) = 𝔼[fun p => G (p.1, f p.2)] (simulate impl₂ c s)`.
Framework glue, no textbook counterpart.

**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
`cnt s < κ`: rewrite the call of `impl₁` by the hypothesis, and on each possible outcome of the
call of `impl₂` (where `cnt` grew by at most one) apply the induction hypothesis
(`expect_congr_of_allOutputs`). -/
protected theorem expect_simulate_abs (impl₁ : QueryImpl spec σ₁ unifSpec)
    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
    (hcnt : ∀ i x s, cnt s < κ → (impl₂ i x s).AllOutputs fun p => cnt p.2 ≤ cnt s + 1)
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s (by omega)]
    refine expect_congr_of_allOutputs (hcnt i x s (by omega)) fun p _ => ?_
    exact ih p.1 (m - 1) (hk p.1) p.2 (by omega)

/-- **Simulation through a state abstraction, in law, along runs with a query budget and an
invariant:** as `Games.expect_simulate_abs`, with the hypotheses only on the states satisfying
an invariant `P` that every call of `impl₂` keeps: for `c` with at most `m` queries, `P s` and
`cnt s + m ≤ κ`, `𝔼[G | simulate impl₁ c (f s)] = 𝔼[fun p => G (p.1, f p.2) | simulate impl₂ c s]`.
Framework glue, no textbook counterpart.

**Proof sketch.** As `Games.expect_simulate_abs`, carrying `P` through the possible outcomes. -/
protected theorem expect_simulate_abs_inv (impl₁ : QueryImpl spec σ₁ unifSpec)
    (impl₂ : QueryImpl spec σ₂ unifSpec) (f : σ₂ → σ₁) (P : σ₂ → Prop) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, P s → cnt s < κ → ∀ g : spec.rng i × σ₁ → ℝ,
      expect (impl₁ i x (f s)) g = expect (impl₂ i x s) fun p => g (p.1, f p.2))
    (hcnt : ∀ i x s, P s → cnt s < κ →
      (impl₂ i x s).AllOutputs fun p => P p.2 ∧ cnt p.2 ≤ cnt s + 1)
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂) (hP : P s)
    (hs : cnt s + m ≤ κ) (G : α × σ₁ → ℝ) :
    expect (simulate impl₁ c (f s)) G = expect (simulate impl₂ c s) fun p => G (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h i x s hP (by omega)]
    refine expect_congr_of_allOutputs (hcnt i x s hP (by omega)) fun p hp => ?_
    exact ih p.1 (m - 1) (hk p.1) p.2 hp.1 (by omega)

end Abs

/-! ### Coins drawn fresh and coins in advance -/

section Tapes

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **One fresh coin per query:** the query `x` to oracle `i` in state `s` draws a uniform
`t ∈ τ`, then runs `K i x s t`: `freshImpl K i x s = (sample τ).bind (K i x s)`.
Framework glue, no textbook counterpart. -/
protected noncomputable def freshImpl [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) : QueryImpl spec σ unifSpec :=
  fun i x s => (sample τ).bind (K i x s)

/-- The reader of `Games.freshImpl`: `freshImpl K i x s = (sample τ).bind (K i x s)`.
Framework glue, no textbook counterpart. -/
protected theorem freshImpl_apply [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (i : ι) (x : spec.dom i) (s : σ) :
    Games.freshImpl K i x s = (sample τ).bind (K i x s) :=
  rfl

/-- **A family of `κ` coins, extended to every index** by an arbitrary value:
`extTape T m = T ⟨m, hm⟩` for `hm : m < κ`, and `Classical.arbitrary C` otherwise.
Framework glue, no textbook counterpart. -/
protected noncomputable def extTape {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) (m : ℕ) : C :=
  if hm : m < κ then T ⟨m, hm⟩ else Classical.arbitrary C

/-- Below `κ` the extended family is the family: `m < κ → extTape T m = T ⟨m, hm⟩`.
Framework glue, no textbook counterpart. -/
protected theorem extTape_of_lt {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) {m : ℕ}
    (hm : m < κ) : Games.extTape T m = T ⟨m, hm⟩ := by
  rw [Games.extTape, dif_pos hm]

/-- From `κ` on the extended family is the arbitrary value:
`¬ m < κ → extTape T m = Classical.arbitrary C`. Framework glue, no textbook counterpart. -/
protected theorem extTape_of_not_lt {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) {m : ℕ}
    (hm : ¬ m < κ) : Games.extTape T m = Classical.arbitrary C := by
  rw [Games.extTape, dif_neg hm]

/-- Changing one coordinate `j` of `T` changes its extension only at `j`:
`m ≠ j → extTape (update T j r) m = extTape T m`. Framework glue, no textbook counterpart. -/
protected theorem extTape_update {C : Type} [Nonempty C] {κ : ℕ} (T : Fin κ → C) (j : Fin κ)
    (r : C) {m : ℕ} (hm : m ≠ j) : Games.extTape (Function.update T j r) m = Games.extTape T m := by
  by_cases h : m < κ
  · rw [Games.extTape_of_lt _ h, Games.extTape_of_lt _ h, Function.update_of_ne]
    exact fun h' => hm (congrArg Fin.val h')
  · rw [Games.extTape_of_not_lt _ h, Games.extTape_of_not_lt _ h]

/-- **One coin per query, from tapes in advance:** the query `x` to oracle `i` in state `(s, j)`
runs `K i x s (T j)` and advances the query counter `j`,
`tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`.
Framework glue, no textbook counterpart. -/
protected def tapeImpl (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ) :
    QueryImpl spec (σ × ℕ) unifSpec :=
  fun i x s => (K i x s.1 (T s.2)).bind fun p => .pure (p.1, (p.2, s.2 + 1))

/-- The reader of `Games.tapeImpl`:
`tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => pure (p.1, (p.2, j + 1))`.
Framework glue, no textbook counterpart. -/
protected theorem tapeImpl_apply (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (T : ℕ → τ) (i : ι) (x : spec.dom i) (s : σ) (j : ℕ) :
    Games.tapeImpl K T i x (s, j) = (K i x s (T j)).bind fun p => .pure (p.1, (p.2, j + 1)) :=
  rfl

/-- **The run from the counter `j` ignores the tapes below `j`:** if `T m = T' m` for every
`m ≥ j`, then `simulate (tapeImpl K T) c (s, j) = simulate (tapeImpl K T') c (s, j)`.
Framework glue, no textbook counterpart.

**Proof sketch.** Induction on the computation: a query at counter `j' ≥ j` reads `T j'` and
moves to `j' + 1`. -/
protected theorem simulate_tapeImpl_congr
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (T T' : ℕ → τ) (c : OracleComp spec α) (s : σ) (j : ℕ) (hT : ∀ m, j ≤ m → T m = T' m) :
    simulate (Games.tapeImpl K T) c (s, j) = simulate (Games.tapeImpl K T') c (s, j) := by
  induction c generalizing s j with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, Games.tapeImpl_apply, Games.tapeImpl_apply,
      hT j le_rfl, OracleComp.bind_assoc, OracleComp.bind_assoc]
    congr 1
    funext p
    rw [OracleComp.pure_bind, OracleComp.pure_bind]
    exact ih p.1 p.2 (j + 1) fun m hm => hT m (by omega)

/-- **Coins in advance have the law of fresh coins:** for a computation with at most `m`
queries, a counter `j` with `j + m ≤ κ`, and every function `G` of the output,
`𝔼_{T ← τ^κ} 𝔼[G (simulate (tapeImpl K (extTape T)) c (s, j))] = 𝔼[G (simulate (freshImpl K) c s)]`.
Framework glue, no textbook counterpart.

**Proof sketch.** Induction on `c`, generalizing the counter, the state and the budget. A query
costs one unit, so it reads the tape `T j` with `j < κ`; the continuation runs from `j + 1`, so
it ignores `T j` (`Games.simulate_tapeImpl_congr`, `Games.extTape_update`), and
`ProbComp.expect_sample_coord` replaces `T j` by the fresh coin of `freshImpl`
(`expect_expect_sample` exchanges the tape with the call). -/
protected theorem expect_simulate_tapeImpl [Fintype τ] [Nonempty τ]
    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ))
    (κ : ℕ) (G : α → ℝ) (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m)
    (s : σ) (j : ℕ) (hj : j + m ≤ κ) :
    expect (sample (Fin κ → τ))
        (fun T => expect (simulate (Games.tapeImpl K (Games.extTape T)) c (s, j)) fun p => G p.1) =
      expect (simulate (Games.freshImpl K) c s) fun p => G p.1 := by
  induction c generalizing m s j with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    have hjk : j < κ := by omega
    let jj : Fin κ := ⟨j, hjk⟩
    have hT : ∀ T : Fin κ → τ, Games.extTape T j = T jj :=
      fun T => Games.extTape_of_lt T hjk
    simp only [simulate_query, Games.tapeImpl_apply, Games.freshImpl_apply, OracleComp.bind_assoc,
      OracleComp.pure_bind, expect_bind, hT]
    refine (expect_sample_coord jj (fun t T => expect (K i x s t) fun p =>
      expect (simulate (Games.tapeImpl K (Games.extTape T)) (k p.1) (p.2, j + 1))
        fun q => G q.1) ?_).trans ?_
    · intro t t' T
      refine congrArg _ (funext fun p => ?_)
      refine congrArg (fun c => expect c fun q => G q.1)
        (Games.simulate_tapeImpl_congr K _ _ _ _ _ fun m' hm' => ?_)
      exact Games.extTape_update T jj t' (by
        intro h
        have : m' = j := h
        omega)
    · refine congrArg _ (funext fun t => ?_)
      rw [← expect_expect_sample]
      refine congrArg _ (funext fun p => ?_)
      exact ih p.1 (m - 1) (hk p.1) p.2 (j + 1) (by omega)

end Tapes

/-! ### Functions overridden by a table -/

section Override

variable {κ β : Type} [DecidableEq κ]

/-- **A function overridden by a table:** `ovr M R` is `R` with the entries `(p, y)` of `M`
written over it, the first entry of a key winning: `ovr [] R = R`,
`ovr ((p, y) :: M) R = update (ovr M R) p y`. Framework glue, no textbook counterpart. -/
protected def ovr : List (κ × β) → (κ → β) → κ → β
  | [], R => R
  | e :: M, R => Function.update (Games.ovr M R) e.1 e.2

/-- The reader of `Games.ovr` on the empty table: `ovr [] R = R`.
Framework glue, no textbook counterpart. -/
protected theorem ovr_nil (R : κ → β) : Games.ovr ([] : List (κ × β)) R = R :=
  rfl

/-- The reader of `Games.ovr` on a nonempty table: `ovr ((p, y) :: M) R = update (ovr M R) p y`.
Framework glue, no textbook counterpart. -/
protected theorem ovr_cons (p : κ) (y : β) (M : List (κ × β)) (R : κ → β) :
    Games.ovr ((p, y) :: M) R = Function.update (Games.ovr M R) p y :=
  rfl

/-- Outside the keys of the table, the overridden function is `R`:
`p ∉ M.map Prod.fst → ovr M R p = R p`. Framework glue, no textbook counterpart. -/
protected theorem ovr_of_not_mem {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst)
    (R : κ → β) : Games.ovr M R p = R p := by
  induction M with
  | nil => rw [Games.ovr_nil]
  | cons e M ih =>
    obtain ⟨q, y⟩ := e
    rw [List.map_cons, List.mem_cons, not_or] at hp
    rw [Games.ovr_cons, Function.update_of_ne hp.1]
    exact ih hp.2

/-- On the keys of the table, the overridden function does not read `R`:
`p ∈ M.map Prod.fst → ovr M R p = ovr M R' p`. Framework glue, no textbook counterpart. -/
protected theorem ovr_of_mem {M : List (κ × β)} {p : κ} (hp : p ∈ M.map Prod.fst)
    (R R' : κ → β) : Games.ovr M R p = Games.ovr M R' p := by
  induction M with
  | nil => rw [List.map_nil] at hp; exact absurd hp List.not_mem_nil
  | cons e M ih =>
    obtain ⟨q, y⟩ := e
    rw [Games.ovr_cons, Games.ovr_cons]
    by_cases hpq : p = q
    · subst hpq
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hpq, Function.update_of_ne hpq]
      rw [List.map_cons, List.mem_cons] at hp
      exact ih (hp.resolve_left hpq)

/-- Changing `R` at a point outside the table changes the overridden function there only:
`p ∉ M.map Prod.fst → ovr M (update R p y) = update (ovr M R) p y`.
Framework glue, no textbook counterpart. -/
protected theorem ovr_update {M : List (κ × β)} {p : κ} (hp : p ∉ M.map Prod.fst) (R : κ → β)
    (y : β) : Games.ovr M (Function.update R p y) = Function.update (Games.ovr M R) p y := by
  induction M with
  | nil => rw [Games.ovr_nil, Games.ovr_nil]
  | cons e M ih =>
    obtain ⟨q, z⟩ := e
    rw [List.map_cons, List.mem_cons, not_or] at hp
    rw [Games.ovr_cons, Games.ovr_cons, ih hp.2]
    exact Function.update_comm hp.1 _ _ _

/-- Writing a concatenation is writing its parts: `ovr (A ++ B) R = ovr A (ovr B R)`.
Framework glue, no textbook counterpart. -/
protected theorem ovr_append (A B : List (κ × β)) (R : κ → β) :
    Games.ovr (A ++ B) R = Games.ovr A (Games.ovr B R) := by
  induction A with
  | nil => rw [List.nil_append, Games.ovr_nil]
  | cons e A ih =>
    obtain ⟨p, y⟩ := e
    rw [List.cons_append, Games.ovr_cons, Games.ovr_cons, ih]

/-- **Resampling a point outside the table moves it into the table:** for `p` not a key of `M`,
`𝔼_R F (R p) (ovr M R) = 𝔼_y 𝔼_R F y (ovr ((p, y) :: M) R)`.
Framework glue, no textbook counterpart.

**Proof sketch.** `ProbComp.expect_sample_coord` at the coordinate `p` with
`F' y R = F y (ovr ((p, y) :: M) R)`, which does not read `R p` (`Games.ovr_update`,
`Function.update_idem`); at `y = R p` the new entry repeats `ovr M R p = R p`
(`Games.ovr_of_not_mem`, `Function.update_eq_self`). -/
protected theorem expect_sample_ovr [Fintype κ] [Fintype β] [Nonempty β] (M : List (κ × β))
    {p : κ} (hp : p ∉ M.map Prod.fst) (F : β → (κ → β) → ℝ) :
    expect (sample (κ → β)) (fun R => F (R p) (Games.ovr M R)) =
      expect (sample β) fun y =>
        expect (sample (κ → β)) fun R => F y (Games.ovr ((p, y) :: M) R) := by
  have h := expect_sample_coord p (fun y R => F y (Games.ovr ((p, y) :: M) R)) fun y y' R => by
    show F y (Games.ovr ((p, y) :: M) (Function.update R p y')) =
      F y (Games.ovr ((p, y) :: M) R)
    rw [Games.ovr_cons, Games.ovr_cons, Games.ovr_update hp, Function.update_idem]
  refine Eq.trans ?_ h
  refine congrArg _ (funext fun R => ?_)
  show F (R p) (Games.ovr M R) = F (R p) (Games.ovr ((p, R p) :: M) R)
  rw [Games.ovr_cons, ← Games.ovr_of_not_mem hp R, Function.update_eq_self]

end Override

end TCSlib.Cryptography.Games
