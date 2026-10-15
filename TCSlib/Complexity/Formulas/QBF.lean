/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Function.Basic
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quantified Boolean formulas (prenex, CNF matrix)

[AB09, §4.2, Definition 4.10]: a quantified Boolean formula is
`Q₁x₁ Q₂x₂ … Qₙxₙ φ(x₁, …, xₙ)` with each `Qᵢ` one of `∀`/`∃`, the variables
ranging over `{0, 1}`, and `φ` a plain Boolean formula. Phase P4.3 of
`AroraBarakChapters3-4Plan.md`; the campaign carrier per decision CH34-Q5:
**prenex form with a CNF matrix**, reusing the chapter-2 carrier
(`Std.Sat.CNF ℕ`, `TCSlib.Complexity.Formulas.CNF`).

## Divergences from [AB09] (each deliberate, recorded for the audit)

* **CNF matrix.** Definition 4.10 allows an arbitrary unquantified matrix and
  notes (p. 83) that restricting to 3CNF is harmless via auxiliary variables.
  The campaign takes the CNF restriction *as the carrier* (decision CH34-Q5):
  `TQBF`'s hardness pays the Tseitin step inside its reduction, and a
  general-formula carrier remains future work (`backlog.md`, general Boolean
  formulas).
* **Prenex by construction**: the quantifier prefix is a `List`, the matrix
  follows; non-prenex formulas are out of scope (the book converts to prenex
  in polynomial time, p. 83 — not formalized here).
* **Free variables read `false`.** Quantifier `i` binds variable `i` (the
  prefix binds an initial segment of `ℕ`); matrix variables at or beyond the
  prefix length are unbound and evaluate at the all-`false` base assignment.
  [AB09] considers only closed formulas; this totalization (in the spirit of
  the chapter-2 `codeFallback` conventions) makes `QBF.truth` total without a
  well-formedness side condition, and well-formed consumers never rely on it.

## Main definitions

* `Complexity.QBF.Quant`, `Complexity.QBF` — the prefix alphabet and the
  formula. [AB09, Definition 4.10]
* `Complexity.QBF.truth` — the truth value, by recursion on the prefix.
  [AB09, Definition 4.10 and Example 4.11]
* `Complexity.QBF.PrefixTruth` — the same recursion over an arbitrary predicate
  of the final assignment in place of the matrix.

## Main results

* `Complexity.QBF.prefixTruth_congr_agree` — prefix truth from `(σ, i)` sees the leaf only on
  assignments that agree with `σ` below `i`.
* `Complexity.QBF.truth_exPrefix_iff_satisfiable` — an all-`∃` prefix covering
  the matrix's variables renders exactly satisfiability: the `SAT` embedding
  of [AB09, Example 4.12].
* `Complexity.QBF.truth_exSuffix_of_pointwise` — auxiliary variables
  quantified existentially **after** an arbitrary prefix: a CNF that is correct
  for every prefix assignment gives an equivalent closed formula ([AB09, §4.2,
  p. 83]; the "Tseitin after the prefix" item of design §14 row H6).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Definitions 4.9-4.10, Examples
  4.11-4.12; the remark on auxiliary variables, p. 83.)
-/

namespace Complexity

open Std.Sat (CNF)

namespace QBF

/-- A quantifier of the prenex prefix. [AB09, Definition 4.10] -/
inductive Quant where
  /-- the existential quantifier `∃` -/
  | ex
  /-- the universal quantifier `∀` -/
  | all
deriving DecidableEq

end QBF

/-- A prenex quantified Boolean formula with CNF matrix: the quantifier
prefix (quantifier `i` binds variable `i`) and the matrix. Matrix variables
beyond the prefix length are free and read `false` under `QBF.truth` (see the
divergences list). [AB09, Definition 4.10, with decision CH34-Q5's CNF
restriction] -/
structure QBF where
  /-- the prenex quantifier prefix; entry `i` binds variable `i` -/
  quants : List QBF.Quant
  /-- the CNF matrix over the chapter-2 carrier -/
  matrix : CNF ℕ

namespace QBF

/-- Truth of the matrix `m` under the remaining prefix, the partial
assignment built so far, and the next variable index: the recursion of
[AB09, Definition 4.10]'s semantics ("∀ and ∃ have their standard meaning"),
peeling one quantifier per step. -/
def truthAux (m : CNF ℕ) : List Quant → (ℕ → Bool) → ℕ → Prop
  | [], σ, _ => m.eval σ = true
  | .ex :: qs, σ, i => ∃ b : Bool, truthAux m qs (Function.update σ i b) (i + 1)
  | .all :: qs, σ, i => ∀ b : Bool, truthAux m qs (Function.update σ i b) (i + 1)

/-- **The truth value of a QBF** [AB09, Definition 4.10]: peel the prefix
from variable `0`, starting at the all-`false` base assignment (free
variables read `false`; see the divergences list). Since every prefix
variable is bound, a closed formula's truth is assignment-independent. -/
def truth (Q : QBF) : Prop :=
  truthAux Q.matrix Q.quants (fun _ => false) 0

/-- Q1: existential-prefix truth supplies a satisfying final assignment,
without any hypothesis that the prefix covers the matrix. -/
private theorem satisfiable_of_exPrefix (m : CNF ℕ) (j : ℕ)
    (σ : ℕ → Bool) (i : ℕ) :
    truthAux m (List.replicate j .ex) σ i → m.Satisfiable := by
  induction j generalizing σ i with
  | zero => exact fun h => ⟨σ, h⟩
  | succ j ih =>
      rintro ⟨b, hb⟩
      exact ih (Function.update σ i b) (i + 1) hb

/-- Q2: updating the next position with the target bit extends prefix
agreement by one position. -/
private theorem update_prefix_agreement (σ τ : ℕ → Bool) (i : ℕ)
    (h : ∀ v < i, σ v = τ v) :
    ∀ v < i + 1, Function.update σ i (τ i) v = τ v := by
  intro v hv
  by_cases he : v = i
  · subst v
    exact Function.update_self i (τ i) σ
  · rw [Function.update_of_ne he]
    exact h v (by omega)

/-- Q3: a satisfying assignment extends any matching consumed prefix through
an existential suffix covering all remaining matrix variables.

**Proof sketch.** Induct on the suffix length. Choose the satisfying bit
at the next position, extending agreement by Q2. At length zero, coverage
and prefix agreement imply equality of matrix evaluations by
`eval_congr_of_lt_numVars`. -/
private theorem exPrefix_of_satisfying (m : CNF ℕ) (τ : ℕ → Bool)
    (hτ : m.eval τ = true) (j : ℕ) (σ : ℕ → Bool) (i : ℕ)
    (hag : ∀ v < i, σ v = τ v) (hcover : m.numVars ≤ i + j) :
    truthAux m (List.replicate j .ex) σ i := by
  induction j generalizing σ i with
  | zero =>
      change m.eval σ = true
      rw [eval_congr_of_lt_numVars (fun v hv => hag v (by omega))]
      exact hτ
  | succ j ih =>
      refine ⟨τ i, ih (Function.update σ i (τ i)) (i + 1) ?_ ?_⟩
      · exact update_prefix_agreement σ τ i hag
      · omega

/-- **The `SAT` embedding** ([AB09, Example 4.12]): under an all-`∃` prefix covering every matrix variable, truth
is exactly satisfiability of the matrix.

**Proof sketch.** Forward: the recursion's witnesses assemble an assignment
on `[0, n)` under which the matrix evaluates `true`; variables `≥ n` carry
the base `false`, and `Complexity.eval_congr_of_lt_numVars` (chapter 2)
transports evaluation to the assembled assignment. Backward: given a
satisfying `σ`, choose the witness `σ i` at step `i`; after `n` updates the
built assignment agrees with `σ` below `numVars m ≤ n`, and
`eval_congr_of_lt_numVars` closes. Fill obligations: the update-prefix
agreement lemma (`Function.update` accumulation agrees with `σ` on the
consumed segment) and the two inductions.

**C1d proof-sketch appendix.** The forward induction simply returns the
final total assignment; it needs no coverage hypothesis or evaluation
transport. Only the backward induction uses the matrix-variable bound. -/
theorem truth_exPrefix_iff_satisfiable (m : CNF ℕ) (n : ℕ) (hn : m.numVars ≤ n) :
    QBF.truth ⟨List.replicate n .ex, m⟩ ↔ m.Satisfiable := by
  constructor
  · exact satisfiable_of_exPrefix m n (fun _ => false) 0
  · rintro ⟨τ, hτ⟩
    exact exPrefix_of_satisfying m τ hτ n (fun _ => false) 0
      (by intro v hv; omega) (by simpa using hn)

/-! ### Prefix truth over an arbitrary leaf, and auxiliary variables after the prefix

Added by RD-2 (design §16b item 2; design §14 row H6, "Tseitin on `Std.Sat.CNF ℕ` correct
for every prefix assignment"). The `TQBF` hardness reduction writes its prenex matrix as a CNF
over the prefix variables and further auxiliary variables, quantified existentially after
the whole prefix, so that an auxiliary value may depend on every universal variable before
it (P4.3 round-1 answer 5). -/

/-- **Prefix truth over an arbitrary leaf predicate**: the recursion of
`Complexity.QBF.truthAux` ([AB09, Definition 4.10]) with the matrix test replaced by a
predicate `P` of the final assignment. Quantifier number `j` of the remaining prefix binds
variable `i + j`, as in `Complexity.QBF.truthAux`. -/
def PrefixTruth (P : (ℕ → Bool) → Prop) : List Quant → (ℕ → Bool) → ℕ → Prop
  | [], σ, _ => P σ
  | .ex :: qs, σ, i => ∃ b : Bool, PrefixTruth P qs (Function.update σ i b) (i + 1)
  | .all :: qs, σ, i => ∀ b : Bool, PrefixTruth P qs (Function.update σ i b) (i + 1)

/-- The CNF-matrix semantics is prefix truth with the matrix test as the leaf. (Proved, by
induction on the prefix.) -/
theorem truthAux_iff_prefixTruth (m : CNF ℕ) (qs : List Quant) (σ : ℕ → Bool) (i : ℕ) :
    truthAux m qs σ i ↔ PrefixTruth (fun τ => m.eval τ = true) qs σ i := by
  induction qs generalizing σ i with
  | nil => exact Iff.rfl
  | cons q qs ih =>
    cases q with
    | ex => exact exists_congr fun b => ih _ _
    | all => exact forall_congr' fun b => ih _ _

/-- **Prefix truth sees only the assignment below its start**: two leaves that agree on
every assignment agreeing with `σ` below `i` have the same prefix truth from `(σ, i)`.

**Proof sketch.** Induction on the prefix; an update at position `i` keeps agreement
below `i + 1` equivalent to agreement below `i` together with the updated value. -/
theorem prefixTruth_congr_agree {P P' : (ℕ → Bool) → Prop} (qs : List Quant) (σ : ℕ → Bool)
    (i : ℕ) (h : ∀ τ : ℕ → Bool, (∀ v < i, τ v = σ v) → (P τ ↔ P' τ)) :
    PrefixTruth P qs σ i ↔ PrefixTruth P' qs σ i := by
  induction qs generalizing σ i with
  | nil => exact h σ (fun _ _ => rfl)
  | cons q qs ih =>
    have h' : ∀ b : Bool, ∀ τ : ℕ → Bool, (∀ v < i + 1, τ v = Function.update σ i b v) →
        (P τ ↔ P' τ) := by
      intro b τ hτ
      apply h τ
      intro v hv
      rw [hτ v (by omega), Function.update_of_ne (by omega)]
    cases q with
    | ex => exact exists_congr fun b => ih _ _ (h' b)
    | all => exact forall_congr' fun b => ih _ _ (h' b)

/-- Prefix truth depends on its leaf predicate only through its truth values. (Proved: the case
of `prefixTruth_congr_agree` with leaves that agree everywhere.) -/
theorem prefixTruth_congr {P P' : (ℕ → Bool) → Prop} (h : ∀ τ, P τ ↔ P' τ)
    (qs : List Quant) (σ : ℕ → Bool) (i : ℕ) :
    PrefixTruth P qs σ i ↔ PrefixTruth P' qs σ i :=
  prefixTruth_congr_agree qs σ i fun τ _ => h τ

/-- **Splitting a prefix**: the prefix truth of `qs ++ rs` is the prefix truth of `qs` whose
leaf is the prefix truth of `rs`, started at the variable after `qs`. (Proved, by induction
on `qs`.) -/
theorem prefixTruth_append (P : (ℕ → Bool) → Prop) (qs rs : List Quant)
    (σ : ℕ → Bool) (i : ℕ) :
    PrefixTruth P (qs ++ rs) σ i ↔
      PrefixTruth (fun τ => PrefixTruth P rs τ (i + qs.length)) qs σ i := by
  induction qs generalizing σ i with
  | nil => exact Iff.rfl
  | cons q qs ih =>
    have he : i + 1 + qs.length = i + (q :: qs).length := by
      simp only [List.length_cons]
      omega
    cases q with
    | ex =>
      simp only [List.cons_append, PrefixTruth]
      exact exists_congr fun b => by rw [ih, he]
    | all =>
      simp only [List.cons_append, PrefixTruth]
      exact forall_congr' fun b => by rw [ih, he]

/-- **An existential suffix is satisfiability above the bound part**: if the matrix
mentions only variables below `i + j`, then `j` existential quantifiers started at variable
`i` hold iff some assignment agreeing with `σ` below `i` satisfies the matrix. The case
`i = 0` is `Complexity.QBF.truth_exPrefix_iff_satisfiable` ([AB09, Example 4.12]).

**Proof sketch.** Forward, the witnesses build a final assignment that agrees with `σ` below
`i` (each update is at a position `≥ i`) and satisfies the matrix; no coverage hypothesis is
needed. Backward is Q3 (`exPrefix_of_satisfying`), the coverage hypothesis transporting the
evaluation through `Complexity.eval_congr_of_lt_numVars`. (Proved.) -/
theorem truthAux_exSuffix_iff (m : CNF ℕ) (j : ℕ) (σ : ℕ → Bool) (i : ℕ)
    (hm : m.numVars ≤ i + j) :
    truthAux m (List.replicate j .ex) σ i ↔
      ∃ τ : ℕ → Bool, (∀ v < i, τ v = σ v) ∧ m.eval τ = true := by
  constructor
  · intro h
    clear hm
    induction j generalizing σ i with
    | zero => exact ⟨σ, fun _ _ => rfl, h⟩
    | succ j ih =>
      obtain ⟨b, hb⟩ := h
      obtain ⟨τ, hτ, he⟩ := ih (Function.update σ i b) (i + 1) hb
      refine ⟨τ, fun v hv => ?_, he⟩
      rw [hτ v (by omega), Function.update_of_ne (by omega)]
  · rintro ⟨τ, hag, hτ⟩
    exact exPrefix_of_satisfying m τ hτ j σ i (fun v hv => (hag v hv).symm) hm

/-- **Auxiliary variables after the prefix, for any encoding** (the "Tseitin after the
prefix" fill obligation of `Complexity.TQBF_PSPACEHard`): let `qs` be a quantifier prefix,
`T` a CNF on the prefix variables and `G` further variables, and `P` a predicate of the
assignment. If, **for every assignment `σ`**, some assignment agreeing with `σ` on the prefix
variables `0, …, |qs| - 1` satisfies `T` exactly when `P σ` holds, then the closed formula
with prefix `qs` followed by `G` existential quantifiers and matrix `T` is true iff the prefix
`qs` holds of `P`. The auxiliary values are quantified after every universal variable of
`qs`, so they may depend on all of them (P4.3 round-1 answer 5). [AB09, §4.2, p. 83:
auxiliary variables, as in the Cook-Levin proof, give an equivalent formula whose matrix is in
CNF]

**Proof sketch.** `truthAux_iff_prefixTruth` and `prefixTruth_append` split the prefix after
`qs`; at each leaf `τ`, `truthAux_exSuffix_iff` (with the `numVars` bound) turns the
existential suffix into "some extension of `τ` satisfies `T`", which is `P τ` by the
pointwise hypothesis; `prefixTruth_congr` transports the leaf. (Proved.) -/
theorem truth_exSuffix_of_pointwise (qs : List Quant) (T : CNF ℕ) (G : ℕ)
    (P : (ℕ → Bool) → Prop) (hT : T.numVars ≤ qs.length + G)
    (hpt : ∀ σ : ℕ → Bool,
      (∃ τ : ℕ → Bool, (∀ v < qs.length, τ v = σ v) ∧ T.eval τ = true) ↔ P σ) :
    QBF.truth ⟨qs ++ List.replicate G .ex, T⟩ ↔ PrefixTruth P qs (fun _ => false) 0 := by
  change truthAux T (qs ++ List.replicate G .ex) (fun _ => false) 0 ↔ _
  rw [truthAux_iff_prefixTruth, prefixTruth_append]
  apply prefixTruth_congr
  intro τ
  rw [← truthAux_iff_prefixTruth, Nat.zero_add, truthAux_exSuffix_iff T G τ qs.length hT]
  exact hpt τ

end QBF

end Complexity
