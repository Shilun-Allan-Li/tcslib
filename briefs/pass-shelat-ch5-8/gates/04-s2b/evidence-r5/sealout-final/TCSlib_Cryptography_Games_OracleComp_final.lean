/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Notation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
-- (no candidates)

/-!
# Oracle computations

The syntax of security games and protocols. An *oracle specification* names a family of oracles,
each with a type of queries and a type of answers. An *oracle computation* over it asks one
oracle a query, looks at the answer, chooses what to do next, and eventually returns a value. It
is the free monad over the specification: a well-founded tree (every run makes finitely many
queries) whose inner nodes are queries, with one subtree per possible answer. With finite answer
types, as for probabilistic computations, the tree is finite.

Everything else in the framework is built on this file:
- uniform sampling is one more oracle (`TCSlib.Cryptography.Games.Probability`);
- running a computation against implementations of its oracles is `simulate`
  (`TCSlib.Cryptography.Games.Simulate`);
- a two-party protocol is a pair of computations whose oracle is the message exchange
  (`TCSlib.Cryptography.Games.Protocols`).

With one oracle, an oracle computation is a `TCSlib.Cryptography.QueryTree` of the concrete
layer ([Gar26]); the bridge between the two is in the S2b layer.

## Main definitions

* `Games.OracleSpec ι`: a family of oracles named by `ι`.
* `Games.OracleComp spec α`: computations with access to the oracles of `spec`, returning an `α`;
  a `Monad` and a `LawfulMonad`.
* `Games.OracleComp.call i x`: ask oracle `i` the query `x` and return the answer.
* `Games.singleSpec I O`: one oracle (index `Unit`); its computations are the concrete layer's
  query trees.
* `Games.OracleSpec.add`: the disjoint union of two oracle families;
  `OracleComp.liftLeft`/`liftRight` run a computation over one part in the union.
* `Games.OracleComp.AllOutputs P c`: every possible output of `c` satisfies `P`.
* `Games.OracleComp.CostBoundedBy cost c q`: every run of `c` spends at most `q`, oracle `i`
  costing `cost i` per query (for example, 1 for the oracle under attack and 0 for coin draws).

## Main results

* `Games.OracleComp.instLawfulMonad`: the monad laws.
* `Games.OracleComp.CostBoundedBy.bind`: costs add under sequencing.
* `Games.OracleComp.costBoundedBy_liftLeft`, `costBoundedBy_liftRight`: lifting into a union of
  specifications keeps the cost.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (oracle adversaries).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games

/-- A **family of oracles** named by `ι`: oracle `i` accepts queries in `dom i` and answers in
`rng i`. [VCVio, OracleComp/OracleSpec] -/
structure OracleSpec (ι : Type) where
  /-- The queries oracle `i` accepts. -/
  dom : ι → Type
  /-- The answers oracle `i` gives. -/
  rng : ι → Type

/-- **Oracle computations** over `spec` returning an `α`: either return a value, or ask oracle
`i` the query `x` and continue with `k` applied to the answer. This is the free monad over
`spec`; an oracle adversary of [Gar26, Definition 3.9] or [PS10, §3.8.1] with fixed coins is the
one-oracle case. [VCVio, OracleComp/OracleComp] -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type where
  /-- Return `a` without further queries. -/
  | pure : α → OracleComp spec α
  /-- Ask oracle `i` the query `x`, and continue with `k` on the answer. -/
  | query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α) : OracleComp spec α

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {α β γ : Type}

/-- Sequencing: run `c`, then `f` on its result. Queries of `c` come first. -/
def bind : OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | .pure a, f => f a
  | .query i x k, f => .query i x (fun y => bind (k y) f)

instance : Monad (OracleComp spec) where
  pure := .pure
  bind := bind

/-- `>>=` is `OracleComp.bind`. -/
theorem bind_eq_bind (c : OracleComp spec α) (f : α → OracleComp spec β) :
    (c >>= f) = c.bind f := rfl

/-- `pure` is the constructor `OracleComp.pure`. -/
theorem pure_eq_pure (a : α) : (Pure.pure a : OracleComp spec α) = .pure a := rfl

/-- `<$>` is sequencing with a return. -/
theorem map_eq_bind (h : α → β) (c : OracleComp spec α) :
    (h <$> c) = c.bind (fun a => .pure (h a)) := rfl

/-- Returning first, then continuing, is continuing. -/
@[simp] theorem pure_bind (a : α) (f : α → OracleComp spec β) : (OracleComp.pure a).bind f = f a :=
  rfl

/-- A query followed by `f` is the query whose continuation is followed by `f`. -/
@[simp] theorem query_bind (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (f : α → OracleComp spec β) :
    (OracleComp.query i x k).bind f = .query i x (fun y => (k y).bind f) := rfl

/-- Continuing with a return changes nothing. -/
@[simp] theorem bind_pure (c : OracleComp spec α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- Sequencing is associative. -/
theorem bind_assoc (c : OracleComp spec α) (f : α → OracleComp spec β)
    (g : β → OracleComp spec γ) : (c.bind f).bind g = c.bind (fun a => (f a).bind g) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- The monad laws. -/
instance instLawfulMonad : LawfulMonad (OracleComp spec) :=
  LawfulMonad.mk' _
    (id_map := fun c => bind_pure c)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun c f g => bind_assoc c f g)

/-- Ask oracle `i` the query `x` and return the answer. -/
def call (i : ι) (x : spec.dom i) : OracleComp spec (spec.rng i) :=
  .query i x .pure

/-- Asking and then continuing with `f` is the query with continuation `f`. -/
@[simp] theorem call_bind (i : ι) (x : spec.dom i) (f : spec.rng i → OracleComp spec α) :
    (call i x).bind f = .query i x f := rfl

/-! ### Unions of oracle families -/

end OracleComp

/-- A single oracle with queries in `I` and answers in `O` (index type `Unit`). The concrete
layer's query trees are the computations over it (`TCSlib.Cryptography.QueryTree`). -/
abbrev singleSpec (I O : Type) : OracleSpec Unit := ⟨fun _ => I, fun _ => O⟩

/-- The single oracle of `singleSpec I O` takes queries in `I`. -/
theorem singleSpec_dom (I O : Type) (u : Unit) : (singleSpec I O).dom u = I := rfl

/-- The single oracle of `singleSpec I O` answers in `O`. -/
theorem singleSpec_rng (I O : Type) (u : Unit) : (singleSpec I O).rng u = O := rfl

/-- The **disjoint union** of two oracle families: oracle `.inl i` is oracle `i` of `s₁`, and
oracle `.inr j` is oracle `j` of `s₂`. [VCVio, OracleComp/OracleSpec] -/
abbrev OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :
    OracleSpec (ι₁ ⊕ ι₂) :=
  ⟨Sum.elim s₁.dom s₂.dom, Sum.elim s₁.rng s₂.rng⟩

/-- The left oracles of the union have the queries of `s₁`: `(s₁.add s₂).dom (.inl i) = s₁.dom i`. -/
theorem OracleSpec.add_dom_inl {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (i : ι₁) :
    (s₁.add s₂).dom (.inl i) = s₁.dom i := rfl

/-- The right oracles of the union have the queries of `s₂`: `(s₁.add s₂).dom (.inr j) = s₂.dom j`. -/
theorem OracleSpec.add_dom_inr {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (j : ι₂) :
    (s₁.add s₂).dom (.inr j) = s₂.dom j := rfl

/-- The left oracles of the union have the answers of `s₁`: `(s₁.add s₂).rng (.inl i) = s₁.rng i`. -/
theorem OracleSpec.add_rng_inl {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (i : ι₁) :
    (s₁.add s₂).rng (.inl i) = s₁.rng i := rfl

/-- The right oracles of the union have the answers of `s₂`: `(s₁.add s₂).rng (.inr j) = s₂.rng j`. -/
theorem OracleSpec.add_rng_inr {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (j : ι₂) :
    (s₁.add s₂).rng (.inr j) = s₂.rng j := rfl

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {α β : Type}

/-- Run a computation over `s₁` inside the union `s₁.add s₂`, asking only oracles of `s₁`. -/
def liftLeft {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₁ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query i x k => .query (.inl i) x (fun y => liftLeft (k y))

/-- Run a computation over `s₂` inside the union `s₁.add s₂`, asking only oracles of `s₂`. -/
def liftRight {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₂ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query j x k => .query (.inr j) x (fun y => liftRight (k y))

/-- Lifting commutes with sequencing. -/
theorem liftLeft_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₁ α)
    (f : α → OracleComp s₁ β) :
    (liftLeft (s₂ := s₂) (c.bind f)) = (liftLeft c).bind (fun a => liftLeft (f a)) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, liftLeft, ih]

/-- Lifting commutes with sequencing. -/
theorem liftRight_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₂ α)
    (f : α → OracleComp s₂ β) :
    (liftRight (s₁ := s₁) (c.bind f)) = (liftRight c).bind (fun a => liftRight (f a)) := by
  induction c with
  | pure a => rfl
  | query j x k ih => simp only [query_bind, liftRight, ih]

/-! ### Query costs -/

variable {spec : OracleSpec ι₁}

/-- `c` is **cost-bounded by `q`**: along every run, the total cost of its queries, oracle `i`
costing `cost i` per query, is at most `q`. With `cost` equal to 1 on the oracle under attack and
0 elsewhere, this is "at most `q` queries to that oracle", the query bound of
[Gar26, Definition 3.9]. -/
def CostBoundedBy (cost : ι₁ → ℕ) : OracleComp spec α → ℕ → Prop
  | .pure _, _ => True
  | .query i _ k, q => cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i)

/-- A return costs nothing. -/
@[simp] theorem costBoundedBy_pure (cost : ι₁ → ℕ) (a : α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.pure (spec := spec) a) q :=
  trivial

/-- A query is within budget `q` exactly when its cost fits and every continuation fits in what
is left. -/
@[simp] theorem costBoundedBy_query (cost : ι₁ → ℕ) (i : ι₁) (x : spec.dom i)
    (k : spec.rng i → OracleComp spec α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.query i x k) q ↔
      cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i) :=
  Iff.rfl

/-- A larger budget is still a bound. -/
theorem CostBoundedBy.mono {cost : ι₁ → ℕ} {c : OracleComp spec α} {q q' : ℕ}
    (h : CostBoundedBy cost c q) (hq : q ≤ q') : CostBoundedBy cost c q' := by
  induction c generalizing q q' with
  | pure a => trivial
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := h
    exact ⟨Nat.le_trans hi hq, fun y => ih y (hk y) (Nat.sub_le_sub_right hq _)⟩

/-- **Costs add under sequencing:** if `c` fits in `q₁` and every continuation `f a` fits in
`q₂`, then `c` followed by `f` fits in `q₁ + q₂`.

**Proof sketch.** Induction on `c`. At a query of cost `cost i ≤ q₁`, the continuation fits in
`q₁ - cost i` by hypothesis, so by induction it fits in `(q₁ - cost i) + q₂`, which is
`(q₁ + q₂) - cost i`. -/
theorem CostBoundedBy.bind {cost : ι₁ → ℕ} {c : OracleComp spec α} {f : α → OracleComp spec β}
    {q₁ q₂ : ℕ} (hc : CostBoundedBy cost c q₁) (hf : ∀ a, CostBoundedBy cost (f a) q₂) :
    CostBoundedBy cost (c.bind f) (q₁ + q₂) := by
  induction c generalizing q₁ with
  | pure a => exact (hf a).mono (Nat.le_add_left _ _)
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := hc
    refine ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
    rw [Nat.sub_add_comm hi]
    exact ih y (hk y)

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
left part. -/
theorem costBoundedBy_liftLeft {s₂ : OracleSpec ι₂} {cost : ι₁ ⊕ ι₂ → ℕ} {c : OracleComp spec α}
    {q : ℕ} (h : CostBoundedBy (fun i => cost (.inl i)) c q) :
    CostBoundedBy cost (liftLeft (s₂ := s₂) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query i x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
right part. -/
theorem costBoundedBy_liftRight {s₁ : OracleSpec ι₂} {cost : ι₂ ⊕ ι₁ → ℕ}
    {c : OracleComp spec α} {q : ℕ} (h : CostBoundedBy (fun j => cost (.inr j)) c q) :
    CostBoundedBy cost (liftRight (s₁ := s₁) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query j x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

/-! ### Possible outputs -/

/-- **Every possible output** of `c` satisfies `P`: a return satisfies it, and every
continuation of a query does, whatever the answer. -/
def AllOutputs {spec : OracleSpec ι} (P : α → Prop) : OracleComp spec α → Prop
  | .pure a => P a
  | .query _ _ k => ∀ y, AllOutputs P (k y)

/-- The only possible output of a return is its value: `(pure a).AllOutputs P ↔ P a`. -/
theorem allOutputs_pure {spec : OracleSpec ι} {P : α → Prop} {a : α} :
    (OracleComp.pure (spec := spec) a).AllOutputs P ↔ P a :=
  Iff.rfl

/-- The possible outputs of a query are those of its continuations, whatever the answer:
`(query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P`. -/
theorem allOutputs_query {spec : OracleSpec ι} {P : α → Prop} {i : ι} {x : spec.dom i}
    {k : spec.rng i → OracleComp spec α} :
    (OracleComp.query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P :=
  Iff.rfl

/-- Every computation satisfies the trivial predicate at every possible output. -/
theorem allOutputs_true {spec : OracleSpec ι} (c : OracleComp spec α) :
    c.AllOutputs fun _ => True := by
  induction c with
  | pure a => trivial
  | query i x k ih => exact fun y => ih y

/-- `AllOutputs` is monotone in the predicate. -/
theorem AllOutputs.mono {spec : OracleSpec ι} {P Q : α → Prop} (hPQ : ∀ a, P a → Q a)
    {c : OracleComp spec α} (h : c.AllOutputs P) : c.AllOutputs Q := by
  induction c with
  | pure a => exact hPQ a h
  | query i x k ih => exact fun y => ih y (h y)

/-- Every possible output of `c` followed by `f` satisfies `Q` when every possible output `a`
of `c` satisfies `P` and every possible output of `f a` with `P a` satisfies `Q`. -/
theorem AllOutputs.bind {spec : OracleSpec ι} {P : α → Prop} {Q : β → Prop}
    {c : OracleComp spec α} {f : α → OracleComp spec β} (hc : c.AllOutputs P)
    (hf : ∀ a, P a → (f a).AllOutputs Q) : (c.bind f).AllOutputs Q := by
  induction c with
  | pure a => exact hf a hc
  | query i x k ih => exact fun y => ih y (hc y)

end OracleComp

end TCSlib.Cryptography.Games
