/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Classes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Sipser–Gács theorem: BPP ⊆ Σ₂ ∩ Π₂

Arora–Barak's Theorem 7.18: `BPP` sits in the second level of the polynomial
hierarchy.  The proof shows `BPP ⊆ Σ₂`: after error reduction the set `S_x`
of accepting random strings is either almost all of `{0,1}^m` or a tiny
fraction, and two quantifier alternations — "there exist shifts `u₁,…,u_k`
whose translates of `S_x` cover `{0,1}^m`" — distinguish the two cases.

## Main definitions

* `Randomized.InSigma2`, `Randomized.InPi2` — verifier-style `Σ₂ᵖ` and `Π₂ᵖ`
  (two quantified witness strings over an efficient predicate), the classes
  in which [AB09, Thm 7.18] places `BPP`.
* `Randomized.shiftOrVerifier` — the predicate
  `(u, v) ↦ ⋁_{i ≤ k} M(x, v ⊕ uᵢ)` built from a `BPP` verifier, where `u`
  encodes the `k` shifts `u₁,…,u_k` as one concatenated string.

## Main results (sorry-stubbed)

* `Randomized.sipser_gacs` — [AB09, Thm 7.18].

## Deviations from the source

`Σ₂ᵖ` is defined here in the same certificate style as the chapter's other
classes (an efficient two-witness predicate with polynomially-bounded
witness lengths), rather than via oracle machines or the book's Chapter 5
definitions; `Π₂ᵖ` is its complement-dual, and `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` becomes
"`L` and `Lᶜ` are both `Σ₂`".  As throughout `Randomized.Classes`,
"polynomial time" is the abstract notion `E`, and the single computability
fact the proof uses — that the shifted-OR predicate built from an efficient
verifier is an efficient two-witness predicate — is the explicit hypothesis
`hShift`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

variable (E : VerifierModel)

/-- `L ∈ Σ₂ᵖ`, certificate-style: there is an efficient two-witness
predicate `N` and polynomial witness-length bounds such that
`x ∈ L ↔ ∃ u ∀ v, N(x, u, v)`.  [AB09, Thm 7.18]'s target class, defined in
the style of [AB09, Def 7.4] (see the module docstring's **Deviations**). -/
def InSigma2 (L : Language Bool) : Prop :=
  ∃ (N : List Bool → List Bool → List Bool → Bool) (a₁ k₁ a₂ k₂ : ℕ),
    E.EffTwoWitness N ∧
    ∀ x : List Bool,
      x ∈ L ↔ ∃ u : List Bool, u.length = polyLen a₁ k₁ x.length ∧
        ∀ v : List Bool, v.length = polyLen a₂ k₂ x.length → N x u v = true

/-- `L ∈ Π₂ᵖ` iff its complement is in `Σ₂ᵖ` (equivalently,
`x ∈ L ↔ ∀ u ∃ v, …`). -/
def InPi2 (L : Language Bool) : Prop :=
  InSigma2 E Lᶜ

/-- The two-witness predicate `(u, v) ↦ ⋁_{i < k} M(x, v ⊕ uᵢ)`, where the
first witness `u` is the concatenation of `k` shift strings `u₁,…,u_k` of
length `p(|x|)` each and `⊕` is bitwise XOR: the predicate with which
[AB09, Thm 7.18]'s proof expresses "the translates of the accepting set by
`u₁,…,u_k` cover all random strings `v`". -/
def shiftOrVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → List Bool → Bool := fun x u v =>
  (List.range (k x.length)).any fun i =>
    M x (List.zipWith xor v ((u.drop (i * p x.length)).take (p x.length)))

/-- `E` recognizes the shifted-OR construction: from an efficient Boolean
verifier, the predicate `shiftOrVerifier M p k` is an efficient two-witness
predicate for polynomial block lengths `p` and shift counts `k` (closure of
polynomial time under XOR-shifts and a polynomial OR). -/
def ClosedUnderShiftOr : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.EffTwoWitness (shiftOrVerifier M (polyLen a k) (polyLen a' k'))

/-- **Sipser–Gács** ([AB09, Thm 7.18]): `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` — relative to the
efficiency notion `E`, under the closure hypotheses the proof uses.

**Proof sketch.** It suffices to prove `BPP ⊆ Σ₂ᵖ` and apply it to `Lᶜ`,
since `BPP` is closed under complementation (`InBPP.compl`, which is where
the hypothesis `hNot` is used).  Given `L ∈ BPP` with a verifier using
`m₀ = polyLen a₀ k₀ |x|` random bits — padded so that `a₀ ≥ 7`, hence
`m₀ ≥ 7` at every input length — amplify by majority (`hMaj`,
`majority_error_le`) with `13·m₀` repetitions to error at most `2^{−m₀}`;
the amplified verifier `M` uses `m = 13·m₀²` random bits.  Let
`S_x ⊆ {0,1}^m` be its accepting set, so `|S_x| ≥ (1−2^{−m₀})2^m` if
`x ∈ L` and `|S_x| ≤ 2^{−m₀}2^m` otherwise.  Take `k = 13·m₀ + 1` shifts.
(Claim 1) if `|S_x| ≤ 2^{m−m₀}` then no `k` shifts of `S_x` cover
`{0,1}^m`: `|⋃ᵢ (S_x ⊕ uᵢ)| ≤ k·2^{m−m₀} < 2^m` since `13m₀ + 1 < 2^{m₀}`
(which holds for every length because `m₀ ≥ 7` — the book's choice
`k = ⌈m/n⌉ + 1` needs `k < 2^n` and fails at small `n`, so we balance
against `m₀` instead of `n`).  (Claim 2) if `|S_x| ≥ (1−2^{−m₀})2^m` then
random shifts cover: for fixed `v`,
`Pr_{u₁,…,u_k}[∀ i, v ⊕ uᵢ ∉ S_x] ≤ 2^{−m₀k} < 2^{−m}` since
`m₀·k = 13m₀² + m₀ > m`, so a union bound over the `2^m` strings `v` leaves
a positive-probability choice of shifts covering everything (the
probabilistic method).  Hence
`x ∈ L ↔ ∃ u₁,…,u_k ∀ v, ⋁ᵢ M(x, v ⊕ uᵢ)`, which is the `Σ₂`-shape
`shiftOrVerifier` expresses; all the lengths involved are `polyLen`
schedules. -/
theorem sipser_gacs (hMaj : ClosedUnderMajority E)
    (hNot : ClosedUnderNot E) (hShift : ClosedUnderShiftOr E)
    {L : Language Bool} (hL : InBPP E L) :
    InSigma2 E L ∧ InPi2 E L := by
  sorry

end Randomized
