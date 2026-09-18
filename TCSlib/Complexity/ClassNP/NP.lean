/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class NP

[AB09, §2.1, Definition 2.1]: a language `L` is in `NP` when membership has
polynomial-length certificates verifiable in polynomial time — `x ∈ L` iff some
certificate `u` of length exactly `p |x|` makes the verifier accept `x ++ u`.

## Design and deviations from [AB09]

* **The verifier is a language, not a machine.** We render "polynomial-time TM
  `M` with `M(x, u) = 1`" as membership of the concatenation `x ++ u` in a
  verifier language `V ∈ P` — reusing the audited Chapter-1 class and keeping the
  machine, its time bound, and its acceptance convention out of the definition.
  A concrete verifier machine is recovered from `V ∈ P` wherever a construction
  needs one (`Complexity.mem_P_iff`).
* **Pairing is concatenation** ([AB09], footnote 4): the input to the verifier is
  the plain concatenation `x ++ u`, with no marker and no self-delimiting
  pairing. The definition itself never splits `x ++ u` back into its parts —
  the membership equivalence quantifies over `x` and `u` separately — so no
  injectivity-of-splitting convention is needed here. Concrete verifier
  languages that do recover the split (e.g. in `EXP ⊆ NEXP`) prove their split
  computable case by case.
* **Certificates have length exactly `p |x|`** (Definition 2.1 verbatim). The
  common bounded-length variant is [AB09, Exercise 2.1], stated below as an
  equivalence.

## Main definitions

* `Complexity.NP` — the class NP. [AB09, Definition 2.1]

## Main results

* `Complexity.P_subset_NP` — `P ⊆ NP` (empty certificates). [AB09, §2.1]
* `Complexity.mem_NP_iff_exists_length_le` — bounded-length certificates define
  the same class. [AB09, Exercise 2.1]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1, Definition 2.1, pp. 39-41;
  Exercise 2.1.)
-/

namespace Complexity

/-- **The class NP** [AB09, Definition 2.1]: `L ∈ NP` iff there are a polynomially
bounded certificate length `p` and a polynomial-time-decidable verifier language
`V ∈ P` such that `x ∈ L` exactly when some certificate `u` of length `p |x|`
makes the concatenation `x ++ u` a member of `V`. -/
def NP : Set (Language Bool) :=
  {L | ∃ (p : ℕ → ℕ) (V : Language Bool), PolyBound p ∧ V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ u : List Bool, u.length = p x.length ∧ x ++ u ∈ V}

/-- **`P ⊆ NP`** [AB09, §2.1, after Definition 2.1]: a language decidable in
polynomial time is verifiable with empty certificates.

**Proof sketch.** Take `p = 0` and `V = L`: the only certificate of length `0` is
`[]`, and `x ++ [] = x`, so the membership equivalence is the identity. -/
theorem P_subset_NP : P ⊆ NP := by
  sorry

/-- **Bounded-length certificates define the same class** [AB09, Exercise 2.1]:
`L ∈ NP` iff there are a polynomially bounded `p` and a verifier `V ∈ P` with
`x ∈ L ↔ ∃ u, |u| ≤ p |x| ∧ x ++ u ∈ V`.

**Proof sketch.** (⇒) An exact-length certificate is in particular a
bounded-length one for the same `p`, and conversely any bounded-length witness
under the *exact*-length verifier's `V` can be re-verified after checking the
exact length — so the forward direction reuses `p` and `V` directly. (⇐) Enlarge
`p` to its monotone majorant `n ↦ C (n+1)^c` (permitted in the bounded form,
since `∃ u, |u| ≤ p n` only gains witnesses), and set the exact length
`p' n = C (n+1)^c + 1`, padding each certificate to `u ++ [true] ++ false-run`.
The new verifier, on a string `y`, first recovers the split: `n ↦ n + p' n` is
strictly increasing, so at most one `n` satisfies `n + p' n = |y|`, and it is
found by scanning `n ≤ |y|` in polynomial time — the one place the
concatenation convention needs an inverse, supplied here by the majorant's
strict monotonicity. It then checks that the certificate region has the shape
`u ++ [true] ++ false-run` with `|u| ≤ C (n+1)^c` (rejecting a marker-free
region, so the strip can never eat into `x`), and consults `V` on `x ++ u`. -/
theorem mem_NP_iff_exists_length_le {L : Language Bool} :
    L ∈ NP ↔ ∃ (p : ℕ → ℕ) (V : Language Bool), PolyBound p ∧ V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ u : List Bool, u.length ≤ p x.length ∧ x ++ u ∈ V := by
  sorry

end Complexity
