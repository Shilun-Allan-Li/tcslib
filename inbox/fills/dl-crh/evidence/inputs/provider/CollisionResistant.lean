/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Authentication.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Collision-resistant hash families and their collision game

The collision game reads the finder's output by padding or truncating to two domain
widths and splitting it into two inputs. It tests domain membership, distinctness,
and equality of the hash outputs.

## Main definitions

* `CRH` specifies an index generator, an efficient evaluator, and index-dependent
  domain and range membership tests.
* `CRH.Compresses`, `CRH.collisionGame` and `CRH.CollisionResistant` state compression,
  the collision experiment, and negligible collision probability.

## Main results

`CRH.hash_eq` and `CRH.collisionGame_eq` expose the computations. The predicate
characterizations give the conditions for compression and collision resistance.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 140.1.
-/

namespace TCSlib.Cryptography.Authentication

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Collision-resistant hashing -/

/-- A **family of collision-resistant hash functions**, in its syntax [PS10, Definition 140.1]:
an index generator `Gen(1^n)`; for each index `i`, a domain `D_i` of `d(n)`-bit strings and a
range `R_i` of `r(n)`-bit strings, given by membership tests; and a deterministic polynomial-time
evaluation `h_i(x)` on `⟨1^n, ⟨i, x⟩⟩`. The source's remaining clauses are properties a
construction is proved to have: compression `|R_i| < |D_i|` (`CRH.Compresses`) and collision
resistance (`CRH.CollisionResistant`).

**Deviation:** domains and ranges are sets of fixed-length strings, given by membership tests,
for the source's index-dependent `h_i : D_i → R_i`. The tests are needed: in Construction 142.2
the exponents range over `Z_{p−1}`, and an `n`-bit exponent domain would contain the trivial
collisions `x`, `x + (p − 1)`. -/
structure CRH where
  /-- The domain length `d(n)`. -/
  domLen : PolyExpr
  /-- The range length `r(n)`. -/
  rangeLen : PolyExpr
  /-- The index generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- The evaluation `⟨1^n, ⟨i, x⟩⟩ ↦ h_i(x)`. -/
  eval : List Bool → List Bool
  /-- Membership in the domain `D_i`. -/
  inDom : ∀ n, List Bool → (Fin (domLen.eval n) → Bool) → Bool
  /-- Membership in the range `R_i`. -/
  inRange : ∀ n, List Bool → (Fin (rangeLen.eval n) → Bool) → Bool
  /-- `Gen` is a PPT ("ease of sampling"). -/
  gen_uniform : gen.Uniform
  /-- Evaluation is polynomial-time ("ease of evaluation"). -/
  eval_poly : PolyTimeComputable eval

namespace CRH

variable (H : CRH)

/-- `h_i(x)` as an `r(n)`-bit string. -/
def hash (n : ℕ) (i : List Bool) (x : Fin (H.domLen.eval n) → Bool) :
    Fin (H.rangeLen.eval n) → Bool :=
  padFin (H.rangeLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn x))))

/-- The hash is the evaluator's output on `⟨1^n, ⟨i, x⟩⟩`, padded to `rangeLen(n)` bits. -/
theorem hash_eq (n : ℕ) (i : List Bool) (x : Fin (H.domLen.eval n) → Bool) :
    H.hash n i x =
      padFin (H.rangeLen.eval n) (H.eval (atParam n (pairEncode i (List.ofFn x)))) := rfl

/-- **Compression** [PS10, Definition 140.1, "compression"]: from some parameter on, at every
generated index `i`, `h_i` maps `D_i` into `R_i` and `|R_i| < |D_i|`.

**Deviation:** from a threshold on, since the ch. 2–4 instance generators are degenerate below
one (their deviation D10). -/
def Compresses : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ rg : H.gen.Coins n,
    (∀ x, H.inDom n (H.gen.runAt n [] rg) x = true →
      H.inRange n (H.gen.runAt n [] rg) (H.hash n (H.gen.runAt n [] rg) x) = true) ∧
    Fintype.card {y // H.inRange n (H.gen.runAt n [] rg) y = true} <
      Fintype.card {x // H.inDom n (H.gen.runAt n [] rg) x = true}

/-- Compression holds exactly when, eventually at every generated index, hashes lie in the
range and the range is smaller than the domain [PS10, Definition 140.1, "compression"]. -/
theorem compresses_iff :
    H.Compresses ↔ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ rg : H.gen.Coins n,
      (∀ x, H.inDom n (H.gen.runAt n [] rg) x = true →
        H.inRange n (H.gen.runAt n [] rg) (H.hash n (H.gen.runAt n [] rg) x) = true) ∧
      Fintype.card {y // H.inRange n (H.gen.runAt n [] rg) y = true} <
        Fintype.card {x // H.inDom n (H.gen.runAt n [] rg) x = true} := Iff.rfl

/-- **The collision game** [PS10, Definition 140.1] at parameter `n`, for the machine `A`: sample
`i ← Gen(1^n)` and `A`'s coins, run `A(1^n, i)`, read its output as `(x, x')`, and win when
`x, x' ∈ D_i`, `x ≠ x'` and `h_i(x) = h_i(x')`. -/
noncomputable def collisionGame (A : NUPPT) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (H.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
    let i := H.gen.runAt n [] rg
    let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n) (A.runAt n i r))
    .pure (decide (H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
      H.hash n i xx.1 = H.hash n i xx.2))

/-- The collision game samples an index and machine coins, splits the machine's output into
two inputs, and tests distinct domain elements with equal hashes [PS10, Definition 140.1]. -/
theorem collisionGame_eq (A : NUPPT) (n : ℕ) :
    H.collisionGame A n =
      (ProbComp.sample (H.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
        let i := H.gen.runAt n [] rg
        let xx := splitBits (padFin (H.domLen.eval n + H.domLen.eval n) (A.runAt n i r))
        .pure (decide (H.inDom n i xx.1 = true ∧ H.inDom n i xx.2 = true ∧ xx.1 ≠ xx.2 ∧
          H.hash n i xx.1 = H.hash n i xx.2))) := rfl

/-- **Collision resistance** [PS10, Definition 140.1]: for every non-uniform PPT `A`, the collision
probability is negligible. -/
def CollisionResistant : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, accept (H.collisionGame A n) ≤ ε n

/-- Collision resistance holds exactly when every machine has a negligible upper bound on
collision-game acceptance [PS10, Definition 140.1]. -/
theorem collisionResistant_iff :
    H.CollisionResistant ↔ ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, accept (H.collisionGame A n) ≤ ε n := Iff.rfl

end CRH

end TCSlib.Cryptography.Authentication
