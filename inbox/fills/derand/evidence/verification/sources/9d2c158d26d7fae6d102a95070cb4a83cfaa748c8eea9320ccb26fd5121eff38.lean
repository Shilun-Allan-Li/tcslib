/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.CoNP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The polynomial hierarchy: definitions

[AB09, §5.2, Definition 5.3]: for `i ≥ 1`, a language `L` is in `Σᵢᵖ` when there are a
polynomial `q` and a polynomial-time machine `M` with

`x ∈ L ⟺ ∃ u₁ ∈ {0,1}^{q(|x|)} ∀ u₂ ∈ {0,1}^{q(|x|)} ⋯ Qᵢ uᵢ ∈ {0,1}^{q(|x|)},
  M(x, u₁, …, uᵢ) = 1`,

`Πᵢᵖ = coΣᵢᵖ = {L | Lᶜ ∈ Σᵢᵖ}`, and `PH = ⋃ᵢ Σᵢᵖ`.

## Design and deviations from [AB09]

* **Certificate lengths follow `Complexity.NP`**: every block has length *exactly*
  `C · (|x| + 1)^c` (an explicit polynomial formula in `|x|`, never an abstract length
  function — the phase-1 audit's repair of Definition 2.1, inherited here).
* **The verifier is a language `V ∈ P`**, as in `Complexity.NP`.
* **Tuple encoding: left-nested self-delimiting pairs.** The verifier reads
  `⟨⋯⟨⟨x, u₁⟩, u₂⟩, …, uᵢ⟩`, built with the audited `Turing.pairEncode` (the pairing of
  the bounded-length form `Complexity.mem_NP_iff_exists_length_le`). Each block is
  recoverable by the proved linear-time pair projections, which is what makes the
  quantifier-manipulation lemmas of Theorem 5.4 provable in the machine framework.
  `Complexity.SigmaP_one` proves that at `i = 1` this is exactly `Complexity.NP`
  (whose single certificate is concatenated, `x ++ u`).
* **`i = 0` is allowed.** The same formula with no quantifier defines `Σ₀ᵖ = Π₀ᵖ = P`
  (`Complexity.SigmaP_zero`, `Complexity.PiP_zero`); [AB09] starts at `i = 1`.
  `Complexity.PH` is the union over `i ≥ 1` exactly as in [AB09].
* The quantifier prefix is the recursive predicate `Complexity.altQuant`: polarity
  `true` starts with `∃`, `false` with `∀`, and the polarity flips at each block.

## Main definitions

* `Complexity.qStep` — one bounded quantifier block (`∃` or `∀` over words of length `m`).
* `Complexity.altQuant` — the alternating quantifier prefix over the nested-pair tuple.
* `Complexity.altClass` — the class defined by `altQuant` with polarity `b` and `i` blocks.
* `Complexity.SigmaP` — `Σᵢᵖ`. [AB09, Definition 5.3]
* `Complexity.PiP` — `Πᵢᵖ = coΣᵢᵖ`. [AB09, §5.2]
* `Complexity.PH` — the polynomial hierarchy `⋃_{i ≥ 1} Σᵢᵖ`. [AB09, Definition 5.3]

## Main results

* `Complexity.not_altQuant` — negation duality of the quantifier prefix.
* `Complexity.mem_PiP_iff` — the `∀ u₁ ∃ u₂ ⋯` characterization of `Πᵢᵖ` [AB09, §5.2].
* `Complexity.SigmaP_zero`, `Complexity.PiP_zero` — `Σ₀ᵖ = Π₀ᵖ = P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§5.2, Definition 5.3, p. 97; Theorem 5.4, pp. 97–98.)
-/

namespace Complexity

open Turing

/-- **One bounded quantifier block**: `qStep true m Q` says that *some* word `u` of length
exactly `m` satisfies `Q`, and `qStep false m Q` says that *every* word of length exactly
`m` satisfies `Q`. -/
def qStep : Bool → ℕ → (List Bool → Prop) → Prop
  | true, m, Q => ∃ u : List Bool, u.length = m ∧ Q u
  | false, m, Q => ∀ u : List Bool, u.length = m → Q u

/-- **The alternating quantifier prefix** [AB09, Definition 5.3]: `altQuant V m b k w`
evaluates `Q₁ u₁ Q₂ u₂ ⋯ Q_k u_k, ⟨⋯⟨w, u₁⟩, …, u_k⟩ ∈ V`, where every block `u_j` ranges
over words of length exactly `m`, the quantifiers alternate, and `Q₁` is `∃` when
`b = true` and `∀` when `b = false`. The tuple is the left-nested `Turing.pairEncode`
pairing. With `k = 0` it is simply `w ∈ V`. -/
def altQuant (V : Language Bool) (m : ℕ) : Bool → ℕ → List Bool → Prop
  | _, 0, w => w ∈ V
  | b, k + 1, w => qStep b m fun u => altQuant V m (!b) k (pairEncode w u)

/-- A prefix with no blocks is plain verifier membership: `w ∈ V`. -/
@[simp]
theorem altQuant_zero (V : Language Bool) (m : ℕ) (b : Bool) (w : List Bool) :
    altQuant V m b 0 w ↔ w ∈ V := Iff.rfl

/-- Unfolding the prefix: a prefix with `k + 1` blocks is one block of polarity `b`
followed by a prefix with `k` blocks of the flipped polarity. -/
theorem altQuant_succ (V : Language Bool) (m : ℕ) (b : Bool) (k : ℕ) (w : List Bool) :
    altQuant V m b (k + 1) w ↔
      qStep b m fun u => altQuant V m (!b) k (pairEncode w u) := Iff.rfl

/-- An existential prefix with `k + 1` blocks: `∃ u, |u| = m ∧` a universal prefix
with `k` blocks on `⟨w, u⟩`. -/
theorem altQuant_true_succ (V : Language Bool) (m k : ℕ) (w : List Bool) :
    altQuant V m true (k + 1) w ↔
      ∃ u : List Bool, u.length = m ∧ altQuant V m false k (pairEncode w u) := Iff.rfl

/-- A universal prefix with `k + 1` blocks: `∀ u, |u| = m →` an existential prefix
with `k` blocks on `⟨w, u⟩`. -/
theorem altQuant_false_succ (V : Language Bool) (m k : ℕ) (w : List Bool) :
    altQuant V m false (k + 1) w ↔
      ∀ u : List Bool, u.length = m → altQuant V m true k (pairEncode w u) := Iff.rfl

/-- **Negation duality**: the negation of a prefix of polarity `b` over the verifier `V`
is the prefix of the opposite polarity over the complementary verifier `Vᶜ`
(De Morgan, block by block). -/
theorem not_altQuant (V : Language Bool) (m : ℕ) :
    ∀ (k : ℕ) (b : Bool) (w : List Bool),
      ¬ altQuant V m b k w ↔ altQuant Vᶜ m (!b) k w := by
  intro k
  induction k with
  | zero => intro b w; exact Iff.rfl
  | succ k ih =>
    intro b w
    cases b with
    | true =>
      simp only [altQuant_true_succ, Bool.not_true, altQuant_false_succ, not_exists, not_and]
      exact forall_congr' fun u => imp_congr_right fun _ => by simpa using ih false _
    | false =>
      simp only [altQuant_false_succ, Bool.not_false, altQuant_true_succ, not_forall,
        exists_prop]
      exact exists_congr fun u => and_congr_right fun _ => by simpa using ih true _

/-- **The class of an alternating prefix**: `L ∈ altClass b i` iff there are a block
length `C · (|x| + 1)^c` (an explicit polynomial formula, as in `Complexity.NP`) and a
verifier `V ∈ P` with `x ∈ L ↔ altQuant V (C (|x|+1)^c) b i x`. Polarity `true` gives
`Σᵢᵖ`, polarity `false` the `∀`-first form of `Πᵢᵖ` (`Complexity.mem_PiP_iff`). -/
def altClass (b : Bool) (i : ℕ) : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔ altQuant V (C * (x.length + 1) ^ c) b i x}

/-- **The class `Σᵢᵖ`** [AB09, Definition 5.3]: `L ∈ SigmaP i` iff there are an explicit
polynomial block length `q(n) = C · (n + 1)^c` and a verifier `V ∈ P` with
`x ∈ L ⟺ ∃ u₁ ∀ u₂ ⋯ Qᵢ uᵢ (each |u_j| = q(|x|)), ⟨⋯⟨⟨x, u₁⟩, u₂⟩, …, uᵢ⟩ ∈ V`.
Deviations (see the module docstring): the tuple is the nested `Turing.pairEncode`
pairing, the verifier is a language in `P`, and `i = 0` is allowed (`Σ₀ᵖ = P`). -/
def SigmaP (i : ℕ) : Set (Language Bool) := altClass true i

/-- **The class `Πᵢᵖ`** [AB09, §5.2]: `Πᵢᵖ = coΣᵢᵖ`, the complements of `Σᵢᵖ` languages
(the same complement form as `Complexity.coNP`). Its `∀ u₁ ∃ u₂ ⋯` characterization is
`Complexity.mem_PiP_iff`. -/
def PiP (i : ℕ) : Set (Language Bool) := {L | Lᶜ ∈ SigmaP i}

/-- **The polynomial hierarchy** [AB09, Definition 5.3]: `PH = ⋃_{i ≥ 1} Σᵢᵖ`, indexed
here as `⋃ i, Σ_{i+1}ᵖ`. (Including `Σ₀ᵖ = P` would not change the class:
`Complexity.mem_PH_iff`.) -/
def PH : Set (Language Bool) := ⋃ i : ℕ, SigmaP (i + 1)

/-- `L ∈ Σᵢᵖ` iff there are constants `C`, `c` and a verifier `V ∈ P` such that for every
`x`, `x ∈ L` exactly when the alternating prefix `∃ u₁ ∀ u₂ ⋯` with `i` blocks of length
`C (|x|+1)^c` makes `⟨⋯⟨x, u₁⟩, …, uᵢ⟩ ∈ V` hold. -/
theorem mem_SigmaP_iff {i : ℕ} {L : Language Bool} :
    L ∈ SigmaP i ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔ altQuant V (C * (x.length + 1) ^ c) true i x := Iff.rfl

/-- **Complements swap the polarity of the class**: `Lᶜ ∈ altClass b i` iff
`L ∈ altClass (!b) i`.

**Proof sketch.** Complement the verifier (`P` is closed under complement,
`Complexity.compl_mem_P`) and apply the negation duality `Complexity.not_altQuant`,
keeping the same block length. -/
theorem compl_mem_altClass_iff {b : Bool} {i : ℕ} {L : Language Bool} :
    Lᶜ ∈ altClass b i ↔ L ∈ altClass (!b) i := by
  constructor
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C, c, Vᶜ, compl_mem_P hV, fun x => ?_⟩
    have h : x ∈ L ↔ ¬ altQuant V (C * (x.length + 1) ^ c) b i x := by
      rw [← hL x, Set.mem_compl_iff, not_not]
    exact h.trans (not_altQuant V _ i b x)
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C, c, Vᶜ, compl_mem_P hV, fun x => ?_⟩
    have h := (not_altQuant V (C * (x.length + 1) ^ c) i (!b) x)
    simp only [Bool.not_not] at h
    rw [Set.mem_compl_iff, hL x]
    exact h

/-- **The `∀`-first characterization of `Πᵢᵖ`** [AB09, §5.2]: `L ∈ PiP i` iff there are
an explicit polynomial block length and a verifier `V ∈ P` with
`x ∈ L ⟺ ∀ u₁ ∃ u₂ ⋯ Qᵢ uᵢ, ⟨⋯⟨x, u₁⟩, …, uᵢ⟩ ∈ V`. -/
theorem mem_PiP_iff {i : ℕ} {L : Language Bool} :
    L ∈ PiP i ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔ altQuant V (C * (x.length + 1) ^ c) false i x :=
  compl_mem_altClass_iff (b := true)

/-- `Πᵢᵖ` is the polarity-`false` alternating class. -/
theorem PiP_eq_altClass (i : ℕ) : PiP i = altClass false i := by
  ext L; exact mem_PiP_iff

/-- `L ∈ Σᵢᵖ` iff `Lᶜ ∈ Πᵢᵖ`. -/
theorem compl_mem_PiP_iff {i : ℕ} {L : Language Bool} : Lᶜ ∈ PiP i ↔ L ∈ SigmaP i := by
  change Lᶜᶜ ∈ SigmaP i ↔ _
  rw [compl_compl]

/-- `L ∈ Πᵢᵖ` iff `Lᶜ ∈ Σᵢᵖ` (the definition, as a rewriting lemma). -/
theorem compl_mem_SigmaP_iff {i : ℕ} {L : Language Bool} : Lᶜ ∈ SigmaP i ↔ L ∈ PiP i :=
  Iff.rfl

/-- **Zero blocks give `P`**: `altClass b 0 = P` for either polarity.

**Proof sketch.** With no quantifier the condition is `x ∈ L ↔ x ∈ V`, i.e. `L = V`;
conversely take `V = L` with any block length. -/
theorem altClass_zero (b : Bool) : altClass b 0 = P := by
  ext L
  constructor
  · rintro ⟨C, c, V, hV, hL⟩
    have : L = V := Set.ext fun x => hL x
    exact this ▸ hV
  · intro hL
    exact ⟨0, 0, L, hL, fun x => Iff.rfl⟩

/-- **`Σ₀ᵖ = P`**: with no quantifier block the definition of `Σᵢᵖ` is `P`. -/
theorem SigmaP_zero : SigmaP 0 = P := altClass_zero true

/-- **`Π₀ᵖ = P`**. -/
theorem PiP_zero : PiP 0 = P := (PiP_eq_altClass 0).trans (altClass_zero false)

end Complexity
