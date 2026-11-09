/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Secret sharing: access structures and security definitions

This file sets up the scheme-independent vocabulary of secret sharing: monotone access
structures, the data of a sharing scheme, and the two security requirements (correctness for
authorized sets, perfect privacy for unauthorized sets). Nothing here mentions polynomials;
`TCSlib.Cryptography.SecretSharing.Shamir` instantiates all of it.

Perfect privacy is stated in *randomness-bijection* form: for any unauthorized set `B` and any
two secrets there is a bijection of the randomness space carrying the one secret's `B`-view to
the other's. For uniformly distributed randomness this is equivalent to the usual statement
that the joint distribution of the shares held by `B` is independent of the secret, but it is
finiteness-free and measure-theory-free, and it is what a scheme's proof naturally produces.
`PerfectPrivacy.card_view_eq` extracts the counting consequence.

## Main definitions

* `SecretSharing.AccessStructure`: a monotone family of authorized sets of parties.
* `SecretSharing.AccessStructure.threshold`: the `k`-out-of-`n` access structure.
* `SecretSharing.Scheme`: the data of a scheme (a randomized sharing map and a reconstruction
  map).
* `SecretSharing.Scheme.Correct`, `SecretSharing.Scheme.PerfectPrivacy`: the two security
  requirements.
* `SecretSharing.Scheme.LocalReconstruct`: reconstruction from `A` only reads the shares of `A`.

## Main results

* `SecretSharing.Scheme.PerfectPrivacy.card_view_eq`: an unauthorized set's view has the same
  number of randomness preimages under every secret.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
* [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011, §1–2.
-/

namespace TCSlib.SecretSharing

open Finset

variable {P : Type*}

/-- A monotone access structure on a party type `P`: a predicate `Auth` on finite sets of
parties, closed under taking supersets. `Auth A` means the parties in `A` are together allowed
to recover the secret. [Bei11, §1] -/
structure AccessStructure (P : Type*) where
  /-- The authorized sets. -/
  Auth : Finset P → Prop
  /-- Authorization is monotone: a superset of an authorized set is authorized. -/
  mono : ∀ {A B : Finset P}, A ⊆ B → Auth A → Auth B

/-- The `k`-out-of-`n` threshold access structure: a set of parties is authorized exactly when
it has at least `k` members. [Sha79, §1] -/
def AccessStructure.threshold (k : ℕ) : AccessStructure P where
  Auth A := k ≤ #A
  mono hAB hA := hA.trans (card_le_card hAB)

@[simp]
theorem AccessStructure.threshold_auth {k : ℕ} {A : Finset P} :
    (AccessStructure.threshold k).Auth A ↔ k ≤ #A := Iff.rfl

/-- The data of a secret sharing scheme: `share sec r i` is the share handed to party `i` when
the secret is `sec` and the dealer's coins are `r`, and `reconstruct A f` is the secret that the
set `A` computes from the share assignment `f`. Security is not part of the data; see
`Scheme.Correct` and `Scheme.PerfectPrivacy`. [Bei11, §1] -/
structure Scheme (P Secret Share Rand : Type*) where
  /-- The dealer's sharing map. -/
  share : Secret → Rand → P → Share
  /-- The reconstruction map used by a set of parties. -/
  reconstruct : Finset P → (P → Share) → Secret

namespace Scheme

variable {Secret Share Rand : Type*} (S : Scheme P Secret Share Rand)

/-- Every authorized set recovers the secret, whatever the dealer's coins were. [Bei11, §1] -/
def Correct (Γ : AccessStructure P) : Prop :=
  ∀ A : Finset P, Γ.Auth A → ∀ (sec : Secret) (r : Rand), S.reconstruct A (S.share sec r) = sec

/-- Reconstruction by `A` only inspects the shares held by `A`. This is a well-formedness
condition on the syntax of the scheme, not a security property, but without it `Correct` could
be satisfied by a reconstruction map that peeks at shares outside `A`. -/
def LocalReconstruct : Prop :=
  ∀ (A : Finset P) (f g : P → Share), (∀ i ∈ A, f i = g i) → S.reconstruct A f = S.reconstruct A g

/-- Perfect privacy: for every unauthorized set `B` and every pair of secrets there is a
bijection `e` of the randomness space such that sharing `sec'` with coins `e r` gives the
parties of `B` exactly the shares they would have received had the secret been `sec` with coins
`r`. With uniform coins this says the `B`-view is distributed independently of the secret.
[Bei11, §1], [Sha79, §2] -/
def PerfectPrivacy (Γ : AccessStructure P) : Prop :=
  ∀ B : Finset P, ¬ Γ.Auth B → ∀ sec sec' : Secret,
    ∃ e : Rand ≃ Rand, ∀ (r : Rand), ∀ i ∈ B, S.share sec' (e r) i = S.share sec r i

variable {S}

/-- The counting form of perfect privacy: for an unauthorized set `B` and any candidate view
`w`, the number of coin tosses producing that view is the same for every secret. In particular
an unbounded adversary holding the shares of `B` learns nothing about the secret.

**Proof sketch.** The privacy bijection `e` sending `sec`-coins to `sec'`-coins restricts to a
bijection between the two fibres, since it preserves the `B`-view by construction. -/
theorem PerfectPrivacy.card_view_eq {Γ : AccessStructure P} (h : S.PerfectPrivacy Γ)
    {B : Finset P} (hB : ¬ Γ.Auth B) (sec sec' : Secret) (w : P → Share) :
    Nat.card {r : Rand // ∀ i ∈ B, S.share sec r i = w i} =
      Nat.card {r : Rand // ∀ i ∈ B, S.share sec' r i = w i} := by
  obtain ⟨e, he⟩ := h B hB sec sec'
  refine Nat.card_congr ⟨fun r => ⟨e r.1, fun i hi => (he r.1 i hi).trans (r.2 i hi)⟩,
    fun r => ⟨e.symm r.1, fun i hi => ?_⟩, fun r => by simp, fun r => by simp⟩
  have := he (e.symm r.1) i hi
  rw [e.apply_symm_apply] at this
  exact this ▸ r.2 i hi

end Scheme

end TCSlib.SecretSharing
